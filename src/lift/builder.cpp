#include "decode.h"

#include <algorithm>
#include <format>
#include <set>
#include <stdexcept>
#include <utility>

namespace ir {
namespace {
using namespace decode;

void visitSuccessors(const Terminator& end, const auto& visit) {
    if (const auto* jump = std::get_if<Jump>(&end)) {
        if (const auto* target = std::get_if<Immediate>(&jump->target))
            visit(Address(target->value));
        for (const auto destination : jump->destinations)
            visit(destination);
    } else if (const auto* branch = std::get_if<Branch>(&end)) {
        visit(branch->taken);
        visit(branch->other);
    } else if (const auto* call = std::get_if<Call>(&end)) {
        if (const auto* target = std::get_if<Immediate>(&call->target))
            visit(Address(target->value));
        visit(call->resume);
    }
}

void recordJumpTable(Jump& jump, std::span<const std::uint8_t> image, std::span<const GuestRegion> regions,
    References& references, std::size_t start, unsigned width, std::size_t limit, bool exact,
    Address codeBase = 0, unsigned scale = 1, bool sign = false, bool inlineData = false) {
    const auto region = std::ranges::find_if(regions, [&](const GuestRegion& value) {
        return value.readable && !value.writable && !value.protectable && (!value.executable || inlineData) &&
            start >= value.start && start < value.end;
    });
    if (region == regions.end())
        return;
    std::set<Address> destinations;
    auto end = start;
    for (; region->end - end >= width && (end - start) / width < limit; end += width) {
        Reader entry{image, Address(end), true};
        const auto item = std::uint32_t(entry.read(width));
        const auto offset = sign ? signExtend(item, width * 8) : Address(item);
        const auto destination = codeBase + offset * scale;
        if (destination < 0 || std::size_t(destination) >= executableEnd(destination, image.size(), regions) ||
            (inlineData && !exact && (destination < Address(start) - 65536 || destination >= Address(start))) ||
            (inlineData && exact && destination >= Address(start) && destination < Address(start + width * limit)))
            break;
        destinations.insert(destination);
    }
    if (destinations.size() < 2 || (exact && (end - start) / width != limit))
        return;
    jump.destinations.assign(destinations.begin(), destinations.end());
    references.tables.push_back({start, end - start});
}

void recoverRelativeX64Table(Address pc, Jump& jump, const std::map<Address, Instruction>& instructions,
    std::span<const std::uint8_t> image, std::span<const GuestRegion> regions, References& references) {
    const auto* target = std::get_if<Register>(&jump.target);
    if (!target)
        return;
    auto cursor = pc;
    const auto previous = [&]() -> const Instruction* {
        auto at = instructions.lower_bound(cursor);
        if (at == instructions.begin() || (--at)->second.next != cursor)
            return nullptr;
        cursor = at->first;
        return &at->second;
    };
    const auto* inst = previous();
    const auto* add = inst ? std::get_if<Binary>(&inst->effect) : nullptr;
    const auto* base = add ? std::get_if<Register>(&add->rhs) : nullptr;
    if (!add || !base || add->op != BinaryOp::Add || add->size != 8 || add->count ||
        add->dst != target->index || add->lhs != target->index || base->index == target->index)
        return;
    inst = previous();
    const auto* extend = inst ? std::get_if<Extend>(&inst->effect) : nullptr;
    const auto* load = extend ? std::get_if<Memory>(&extend->src) : nullptr;
    if (!extend || !load || !extend->sign || extend->size != 8 || extend->bits != 32 ||
        extend->dst != target->index || load->address.base != base->index ||
        load->address.index == Zero || load->address.scale != 4)
        return;
    auto index = load->address.index;
    inst = previous();
    const auto* move = inst ? std::get_if<Move>(&inst->effect) : nullptr;
    for (unsigned skipped = 0; move && skipped < 4 && move->dst != index && move->dst != base->index &&
        std::holds_alternative<Register>(move->src); ++skipped) {
        inst = previous();
        move = inst ? std::get_if<Move>(&inst->effect) : nullptr;
    }
    std::optional<EffectiveAddress> indexMemory;
    unsigned narrowed = 0;
    const auto traceIndex = [&](const Move& move) {
        if (const auto* source = std::get_if<Register>(&move.src)) {
            index = source->index;
            return true;
        }
        if (const auto* memory = std::get_if<Memory>(&move.src); memory && !indexMemory && !narrowed) {
            indexMemory = memory->address;
            narrowed = move.size * 8;
            return true;
        }
        return false;
    };
    if (move && move->dst == index && (move->size == 4 || move->size == 8)) {
        if (index == base->index || !traceIndex(*move))
            return;
        inst = previous();
        move = inst ? std::get_if<Move>(&inst->effect) : nullptr;
    }
    const auto* table = move ? std::get_if<EffectiveAddress>(&move->src) : nullptr;
    if (!table || move->dst != base->index || move->size != 8 || table->base != Zero || table->index != Zero)
        return;
    auto entry = cursor;
    inst = previous();
    for (unsigned skipped = 0; inst && !inst->end && skipped < 8; ++skipped) {
        if (inst->after)
            return;
        if (const auto* zero = std::get_if<Extend>(&inst->effect); zero && zero->dst == index && !indexMemory) {
            if (zero->sign || zero->field || narrowed)
                return;
            if (const auto* source = std::get_if<Register>(&zero->src))
                index = source->index;
            else if (const auto* memory = std::get_if<Memory>(&zero->src))
                indexMemory = memory->address;
            else
                return;
            narrowed = zero->bits;
        } else if (const auto* other = std::get_if<Move>(&inst->effect)) {
            if (other->dst == index && !indexMemory) {
                if ((other->size != 4 && other->size != 8) || !traceIndex(*other))
                    return;
            } else if (std::holds_alternative<StackTop>(other->src) || (indexMemory &&
                (other->dst == indexMemory->base || other->dst == indexMemory->index))) {
                return;
            }
        } else if (const auto* adjust = std::get_if<Binary>(&inst->effect); adjust && adjust->dst == 4 &&
            index != 4 && (!indexMemory || (indexMemory->base != 4 && indexMemory->index != 4)) &&
            adjust->lhs == 4 && adjust->op == BinaryOp::Sub &&
            std::holds_alternative<Immediate>(adjust->rhs)) {
        } else {
            return;
        }
        entry = cursor;
        inst = previous();
    }
    const auto* guard = inst && inst->end ? std::get_if<Branch>(&*inst->end) : nullptr;
    const auto* cond = guard ? std::get_if<FlagsCondition>(&guard->condition) : nullptr;
    if (!cond || cond->code != 7 || guard->other != entry)
        return;
    inst = previous();
    for (unsigned skipped = 0; inst && !inst->end && !inst->after && skipped < 4; ++skipped) {
        if (const auto* move = std::get_if<Move>(&inst->effect); move &&
            !std::holds_alternative<StackTop>(move->src) && move->dst != index &&
            (!indexMemory || (move->dst != indexMemory->base && move->dst != indexMemory->index))) {
            inst = previous();
        } else if (std::holds_alternative<Store>(inst->effect)) {
            inst = previous();
        } else {
            break;
        }
    }
    const Immediate* limit = nullptr;
    if (const auto* check = inst ? std::get_if<Binary>(&inst->effect) : nullptr; check &&
        check->op == BinaryOp::Sub && check->dst == Zero && check->lhs == index && check->flags &&
        !indexMemory && (!narrowed || check->size * 8 == narrowed))
        limit = std::get_if<Immediate>(&check->rhs);
    if (const auto* check = inst ? std::get_if<ByteBinary>(&inst->effect) : nullptr; check &&
        check->op == BinaryOp::Sub && !check->writeBack && !check->lhsField && narrowed == 8) {
        const auto* source = std::get_if<Register>(&check->lhs);
        const auto* memory = std::get_if<Memory>(&check->lhs);
        if ((!indexMemory && source && source->index == index) || (indexMemory && memory && memory->address == *indexMemory))
            limit = std::get_if<Immediate>(&check->rhs);
    }
    if (const auto* check = inst ? std::get_if<MemoryBinary>(&inst->effect) : nullptr; check &&
        indexMemory && check->size * 8 == narrowed && check->op == BinaryOp::Sub && !check->writeBack) {
        if (const auto* memory = std::get_if<Memory>(&check->dst); memory && memory->address == *indexMemory)
            limit = std::get_if<Immediate>(&check->rhs);
    }
    if (!limit || limit->value >= 4096 || table->displacement + load->address.displacement < 0)
        return;
    recordJumpTable(jump, image, regions, references, table->displacement + load->address.displacement,
        4, limit->value + 1, true, table->displacement, 1, true);
}

std::optional<std::size_t> rvaTableBound(const std::map<Address, Instruction>& instructions,
    std::map<Address, Instruction>::const_iterator entry, unsigned base, unsigned index) {
    for (unsigned skipped = 0; entry != instructions.begin() && skipped < 2; ++skipped) {
        const auto before = std::prev(entry);
        if (before->second.next != entry->first || before->second.end)
            break;
        if (const auto* origin = std::get_if<Move>(&before->second.effect); origin && origin->dst == base && origin->size == 8) {
            const auto* value = std::get_if<EffectiveAddress>(&origin->src);
            if (!value || *value != EffectiveAddress{Zero, 0})
                return {};
        } else if (const auto* ext = std::get_if<Extend>(&before->second.effect); ext && ext->dst == index &&
            ext->size == 8 && ext->bits == 32 && !ext->field) {
            const auto* source = std::get_if<Register>(&ext->src);
            if (!source)
                return {};
            index = source->index;
        } else {
            break;
        }
        entry = before;
    }
    if (entry == instructions.begin())
        return {};
    const auto branch = std::prev(entry);
    const auto* guard = branch->second.end ? std::get_if<Branch>(&*branch->second.end) : nullptr;
    const auto* condition = guard ? std::get_if<FlagsCondition>(&guard->condition) : nullptr;
    if (!condition || condition->code != 7 || guard->other != entry->first || branch == instructions.begin())
        return {};
    const auto compare = std::prev(branch);
    const auto* check = std::get_if<Binary>(&compare->second.effect);
    const auto* limit = check ? std::get_if<Immediate>(&check->rhs) : nullptr;
    if (compare->second.next == branch->first && limit && check->flags && check->op == BinaryOp::Sub &&
        check->dst == Zero && check->lhs == index && limit->value < 4096)
        return limit->value + 1;
    return {};
}

void recoverRvaTable(Address pc, Jump& jump, const std::map<Address, Instruction>& instructions,
    std::span<const std::uint8_t> image, std::span<const GuestRegion> regions, References& references) {
    const auto* target = std::get_if<Register>(&jump.target);
    if (!target)
        return;
    const auto addAt = instructions.lower_bound(pc);
    if (addAt == instructions.begin())
        return;
    const auto add = std::prev(addAt);
    if (add == instructions.begin() || add->second.next != pc)
        return;
    const auto load = std::prev(add);
    if (load->second.next != add->first)
        return;
    const auto* sum = std::get_if<Binary>(&add->second.effect);
    const auto* move = std::get_if<Move>(&load->second.effect);
    const auto* base = sum ? std::get_if<Register>(&sum->rhs) : nullptr;
    const auto* source = move ? std::get_if<Memory>(&move->src) : nullptr;
    if (!sum || !move || !base || !source || sum->op != BinaryOp::Add || sum->size != 8 || sum->count || sum->invert ||
        sum->dst != target->index || sum->lhs != target->index || move->dst != target->index || move->size != 4)
        return;
    const auto& address = source->address;
    if (address.index == Zero || address.scale != 4 || address.base != base->index || address.base == target->index ||
        address.displacement < 0)
        return;
    recordJumpTable(jump, image, regions, references, std::size_t(address.displacement), 4, 256, false);
    if (!jump.destinations.empty() || load == instructions.begin())
        return;

    if (const auto bound = rvaTableBound(instructions, load, address.base, address.index)) {
        recordJumpTable(jump, image, regions, references, address.displacement, 4, *bound, true, 0, 1, false, true);
        if (!jump.destinations.empty())
            return;
    }

    const auto remap = std::prev(load);
    const auto* byte = std::get_if<Extend>(&remap->second.effect);
    const auto* indexes = byte ? std::get_if<Memory>(&byte->src) : nullptr;
    auto priorIndex = remap;
    for (unsigned i = 0; i < 4 && priorIndex != instructions.begin(); ++i) {
        const auto* move = std::get_if<Move>(&priorIndex->second.effect);
        if (!move || move->dst == address.index || std::holds_alternative<StackTop>(move->src) ||
            priorIndex->second.end || std::prev(priorIndex)->second.next != priorIndex->first)
            break;
        --priorIndex;
    }
    const auto* signByte = std::get_if<Extend>(&priorIndex->second.effect);
    if (remap->second.next == load->first && signByte && signByte->sign && signByte->size == 8 &&
        signByte->bits == 8 && !signByte->field && signByte->dst == address.index &&
        signByte->dst != address.base && std::holds_alternative<Memory>(signByte->src)) {
        const auto table = std::size_t(address.displacement);
        if (table >= image.size())
            return;
        auto first = table;
        for (unsigned i = 0; i < 128 && first >= 4 && executableEnd(first - 4, image.size(), regions); ++i) {
            Reader prior{image, Address(first - 4), true};
            const auto destination = Address(prior.read(4));
            if (destination < Address(table) - 65536 || destination >= Address(table) ||
                std::size_t(destination) >= executableEnd(destination, image.size(), regions))
                break;
            first -= 4;
        }
        recordJumpTable(jump, image, regions, references, first, 4, (table - first) / 4 + 128, false, 0, 1, false, true);
        return;
    }
    if (remap->second.next == load->first) {
        const auto* origin = std::get_if<Move>(&remap->second.effect);
        const auto* relative = origin ? std::get_if<EffectiveAddress>(&origin->src) : nullptr;
        if (relative && *relative == EffectiveAddress{Zero, 0} && origin->size == 8 && origin->dst == address.base) {
            recordJumpTable(jump, image, regions, references, address.displacement, 4, 256,
                false, 0, 1, false, true);
            if (!jump.destinations.empty())
                return;
        }
    }
    if (remap->second.next != load->first || !byte || byte->sign || byte->bits != 8 ||
        byte->dst != address.index || !indexes || indexes->address.base != address.base ||
        indexes->address.index == Zero || indexes->address.scale != 1 || indexes->address.displacement < 0 ||
        remap == instructions.begin())
        return;

    const auto bound = rvaTableBound(instructions, remap, address.base, indexes->address.index);
    if (!bound)
        return;
    const auto isImageData = [&](std::size_t first, std::size_t bytes) {
        return std::ranges::any_of(regions, [&](const GuestRegion& region) {
            return region.readable && !region.writable && first >= region.start &&
                first < region.end && bytes <= region.end - first;
        });
    };
    const auto indices = std::size_t(indexes->address.displacement);
    const auto length = *bound;
    const auto offsets = std::size_t(address.displacement);
    if (!isImageData(indices, length))
        return;
    const auto count = std::size_t(std::ranges::max(image.subspan(indices, length))) + 1;
    if (!isImageData(offsets, count * 4) || (offsets < indices + length && indices < offsets + count * 4))
        return;
    std::set<Address> destinations;
    for (const auto offset : image.subspan(indices, length)) {
        Reader item{image, Address(offsets + offset * 4), true};
        const auto targetPc = std::size_t(item.read(4));
        if (targetPc >= executableEnd(targetPc, image.size(), regions) ||
            (targetPc >= offsets && targetPc < offsets + count * 4) ||
            (targetPc >= indices && targetPc < indices + length))
            return;
        destinations.insert(targetPc);
    }
    if (destinations.size() < 2)
        return;
    jump.destinations.assign(destinations.begin(), destinations.end());
    references.tables.push_back({indices, length});
    references.tables.push_back({offsets, count * 4});
}

void recoverArmTable(Address pc, Jump& jump, const std::map<Address, Instruction>& instructions,
    std::span<const std::uint8_t> image, std::span<const GuestRegion> regions, References& references) {
    const auto* target = std::get_if<Register>(&jump.target);
    if (!target)
        return;
    auto cursor = pc;
    const auto previous = [&]() -> const Instruction* {
        auto next = instructions.lower_bound(cursor);
        if (next == instructions.begin() || (--next)->second.next != cursor)
            return nullptr;
        cursor = next->first;
        return &next->second;
    };
    const auto simpleWrite = [](const Effect& effect) -> std::optional<unsigned> {
        if (const auto* move = std::get_if<Move>(&effect); move && !std::holds_alternative<Memory>(move->src))
            return move->dst;
        if (const auto* field = std::get_if<Bitfield>(&effect))
            return field->dst;
        if (const auto* extend = std::get_if<Extend>(&effect); extend && std::holds_alternative<Register>(extend->src))
            return extend->dst;
        if (const auto* binary = std::get_if<Binary>(&effect); binary && !binary->flags && !binary->withCarry &&
            (std::holds_alternative<Immediate>(binary->rhs) || std::holds_alternative<Register>(binary->rhs)))
            return binary->dst;
        return {};
    };
    auto inst = previous();
    for (unsigned skipped = 0; inst && skipped < 4; ++skipped) {
        const auto write = simpleWrite(inst->effect);
        if (!write || *write == target->index || inst->end || inst->after)
            break;
        inst = previous();
    }
    const auto* sum = inst ? std::get_if<Binary>(&inst->effect) : nullptr;
    const auto* offsetReg = sum ? std::get_if<Register>(&sum->rhs) : nullptr;
    if (!sum || !offsetReg || sum->size != 8 || sum->op != BinaryOp::Add || sum->dst != target->index ||
        sum->lhs != target->index || sum->shift != ShiftOp::Left || sum->count > 2 || sum->flags || sum->extendBits)
        return;

    inst = previous();
    const auto* load = inst ? std::get_if<Extend>(&inst->effect) : nullptr;
    const auto* memory = load ? std::get_if<Memory>(&load->src) : nullptr;
    if (!load || !memory || load->dst != offsetReg->index || load->field != 0 ||
        (load->bits != 8 && load->bits != 16 && load->bits != 32))
        return;
    const auto& at = memory->address;
    const auto width = load->bits / 8;
    if (at.index == Zero || at.scale != width || at.displacement != 0 || target->index == offsetReg->index)
        return;

    inst = previous();
    const auto* code = inst ? std::get_if<Move>(&inst->effect) : nullptr;
    const auto* base = code ? std::get_if<EffectiveAddress>(&code->src) : nullptr;
    if (!code || !base || code->dst != target->index || code->size != 8 || base->base != Zero || base->index != Zero)
        return;

    inst = previous();
    const auto* add = inst ? std::get_if<Binary>(&inst->effect) : nullptr;
    const auto* displacement = add ? std::get_if<Immediate>(&add->rhs) : nullptr;
    if (!add || !displacement || add->dst != at.base || add->lhs != at.base || add->size != 8 ||
        add->op != BinaryOp::Add || add->flags || add->count)
        return;
    inst = previous();
    const auto* page = inst ? std::get_if<Move>(&inst->effect) : nullptr;
    const auto* pageValue = page ? std::get_if<Immediate>(&page->src) : nullptr;
    if (!page || !pageValue || page->dst != at.base || page->size != 8)
        return;
    auto tableEntry = cursor;
    inst = previous();
    for (unsigned skipped = 0; inst && skipped < 8 && !inst->end; ++skipped) {
        const auto write = simpleWrite(inst->effect);
        if (!write || inst->after || *write == at.index)
            return;
        tableEntry = cursor;
        inst = previous();
    }
    const auto* guard = inst && inst->end ? std::get_if<Branch>(&*inst->end) : nullptr;
    const auto* condition = guard ? std::get_if<FlagsCondition>(&guard->condition) : nullptr;
    if (!guard || !condition || condition->code != 8 || guard->other != tableEntry)
        return;
    inst = previous();
    const auto* check = inst ? std::get_if<Binary>(&inst->effect) : nullptr;
    const auto* limit = check ? std::get_if<Immediate>(&check->rhs) : nullptr;
    if (!check || !limit || check->op != BinaryOp::Sub || check->dst != Zero || check->lhs != at.index ||
        !check->flags || check->count || limit->value >= 4096)
        return;
    recordJumpTable(jump, image, regions, references, pageValue->value + displacement->value, width,
        limit->value + 1, true, base->displacement, 1u << sum->count, load->sign);
}

std::optional<Address> linkedArmPlt(const Instruction& first, Reader reader,
    const std::map<Address, Address>& pointers) {
    const auto* page = std::get_if<Move>(&first.effect);
    const auto* base = page ? std::get_if<Immediate>(&page->src) : nullptr;
    if (!page || page->size != 8 || page->dst != 16 || !base)
        return {};
    try {
        const auto second = decodeArm(reader);
        const auto* load = std::get_if<Move>(&second.effect);
        const auto* memory = load ? std::get_if<Memory>(&load->src) : nullptr;
        if (!load || !memory || load->size != 8 || (load->dst != 16 && load->dst != 17) || memory->address.base != 16 ||
            memory->address.index != Zero)
            return {};
        const auto slot = pointers.find(Address(base->value + memory->address.displacement));
        if (slot == pointers.end())
            return {};
        auto tail = decodeArm(reader);
        if (const auto* add = std::get_if<Binary>(&tail.effect)) {
            const auto* offset = std::get_if<Immediate>(&add->rhs);
            if (add->op != BinaryOp::Add || add->size != 8 || add->dst != 16 || add->lhs != 16 ||
                add->flags || add->count || add->invert || !offset || offset->value != std::uint64_t(memory->address.displacement))
                return {};
            tail = decodeArm(reader);
        }
        const auto* jump = tail.end ? std::get_if<Jump>(&*tail.end) : nullptr;
        const auto* target = jump ? std::get_if<Register>(&jump->target) : nullptr;
        if (target && target->index == load->dst)
            return slot->second;
    } catch (const std::runtime_error&) {
        // A failed look-ahead leaves the original instruction and its diagnostics intact.
    }
    return {};
}
}

std::size_t executableEnd(std::size_t pc, std::size_t imageSize, std::span<const GuestRegion> regions) {
    if (regions.empty())
        return imageSize;
    for (const auto& region : regions)
        if (region.executable && pc >= region.start && pc < region.end)
            return region.end;
    return 0;
}

Graph lift(Architecture architecture, std::span<const std::uint8_t> image,
    std::span<const GuestExport> exports, std::span<const GuestRegion> regions,
    std::vector<CodeRange>* code, References* references, std::span<const GuestBinding> bindings,
    CallingConvention convention, std::optional<std::size_t> tlsVector) {
    std::map<Address, Instruction> instructions;
    std::set<Address> entries;
    std::vector<Address> pending;
    std::map<Address, Address> fixedPointers;
    for (const auto& binding : bindings)
        if (binding.fixed)
            fixedPointers.emplace(binding.slot, binding.target);
    const auto bound = [&](const Value& value) -> std::optional<Address> {
        const auto* memory = std::get_if<Memory>(&value);
        if (memory && memory->address.base == Zero && memory->address.index == Zero) {
            if (const auto result = fixedPointers.find(memory->address.displacement); result != fixedPointers.end())
                return result->second;
        }
        return {};
    };
    const auto bindTarget = [&](Value& value) {
        if (const auto target = bound(value); target && *target >= 0 &&
            std::size_t(*target) < executableEnd(*target, image.size(), regions))
            value = immediate(*target);
    };
    const auto addEntry = [&](Address entry) {
        if (entries.insert(entry).second)
            pending.push_back(entry);
    };

    if (exports.empty())
        addEntry(0);
    for (const auto& entry : exports)
        addEntry(entry.offset);
    if (references)
        for (const auto target : references->functions)
            addEntry(target);

    constexpr unsigned maxBlockInstructions = 64;
    for (std::size_t i = 0; i < pending.size(); ++i) {
        auto pc = pending[i];
        for (unsigned count = 0; count < maxBlockInstructions; ++count) {
            if (instructions.contains(pc)) {
                addEntry(pc);
                break;
            }

            const auto end = pc < 0 ? 0 : executableEnd(pc, image.size(), regions);
            Reader reader{image.first(end), pc, !regions.empty()};
            Instruction instruction;
            try {
                if (pc < 0 || pc >= Address(end))
                    throw std::runtime_error(regions.empty() ? "guest address is outside the image"
                                                            : "guest address is outside executable segments");
                instruction = architecture == Architecture::Arm64 ? decodeArm(reader) : decodeX64(reader);
                if (auto* move = std::get_if<Move>(&instruction.effect);
                    move && std::holds_alternative<ThreadLocalStorage>(move->src)) {
                    if (!tlsVector || convention != CallingConvention::Microsoft)
                        throw std::runtime_error("Windows thread-local storage is unavailable");
                    move->src = EffectiveAddress{Zero, Address(*tlsVector)};
                    instruction.addressTaken = *tlsVector;
                }
                if (!fixedPointers.empty()) {
                    if (architecture == Architecture::Arm64) {
                        if (const auto target = linkedArmPlt(instruction, reader, fixedPointers); target && *target >= 0 &&
                            std::size_t(*target) < executableEnd(*target, image.size(), regions))
                            instruction.end = Jump{immediate(*target)};
                    }
                    if (auto* move = std::get_if<Move>(&instruction.effect); move && move->size == 8) {
                        if (const auto target = bound(move->src)) {
                            move->src = EffectiveAddress{Zero, *target};
                            instruction.addressTaken = *target;
                        }
                    }
                    if (instruction.end) {
                        if (auto* jump = std::get_if<Jump>(&*instruction.end))
                            bindTarget(jump->target);
                        if (auto* call = std::get_if<Call>(&*instruction.end))
                            bindTarget(call->target);
                    }
                }
                if (references && instruction.end) {
                    if (auto* jump = std::get_if<Jump>(&*instruction.end)) {
                        if (architecture == Architecture::Arm64)
                            recoverArmTable(pc, *jump, instructions, image, regions, *references);
                        else if (convention == CallingConvention::Microsoft)
                            recoverRvaTable(pc, *jump, instructions, image, regions, *references);
                        else
                            recoverRelativeX64Table(pc, *jump, instructions, image, regions, *references);
                    }
                }
            } catch (const std::runtime_error& error) {
                instruction.end = Trap{std::format("{} at guest offset {}", error.what(), pc)};
            }
            if (code && pc >= 0 && std::size_t(pc) < end)
                code->push_back({std::size_t(pc), std::size_t(reader.pc > pc ? reader.pc : pc + 1)});
            instruction.next = reader.pc;
            const auto& decoded = instructions.emplace(pc, std::move(instruction)).first->second;
            if (decoded.addressTaken && *decoded.addressTaken >= 0) {
                const auto address = *decoded.addressTaken;
                if (std::size_t(address) < executableEnd(address, image.size(), regions)) {
                    if (references)
                        references->functions.insert(address);
                    addEntry(address);
                } else if (references && std::size_t(address) < image.size()) {
                    references->data.insert(address);
                }
            }
            if (decoded.end) {
                visitSuccessors(*decoded.end, addEntry);
                break;
            }
            if (count + 1 == maxBlockInstructions) {
                addEntry(decoded.next);
                break;
            }
            pc = decoded.next;
        }
    }

    Graph graph;
    for (const auto entry : entries) {
        auto& block = graph[entry];
        auto pc = entry;
        for (;;) {
            const auto& instruction = instructions.at(pc);
            if (instruction.end) {
                block.end = *instruction.end;
                break;
            }
            block.effects.push_back(instruction.effect);
            if (instruction.after)
                block.effects.push_back(*instruction.after);
            pc = instruction.next;
            if (entries.contains(pc)) {
                block.end = Jump{immediate(pc)};
                block.hasTerminator = false;
                break;
            }
        }
    }
    return graph;
}
}
