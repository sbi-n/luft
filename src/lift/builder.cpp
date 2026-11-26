#include "decode.h"
#include "ir/analysis.h"

#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <format>
#include <functional>
#include <set>
#include <stdexcept>
#include <utility>

namespace ir {
namespace {
using namespace decode;

template<class... Ts>
struct Visit : Ts... { using Ts::operator()...; };

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
    // Instructions the compiler scheduled between the sum and the jump leave the target alone.
    for (unsigned skipped = 0; inst && skipped < 4 && !inst->end && inst->after.empty() &&
        !writesRegister(inst->effect, target->index); ++skipped)
        inst = previous();
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
        if (!inst->after.empty())
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
    for (unsigned skipped = 0; inst && !inst->end && inst->after.empty() && skipped < 4; ++skipped) {
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

using Instructions = std::map<Address, Instruction>;
// Conditional branches indexed by their taken and fallthrough targets.
using BranchIndex = std::map<Address, std::vector<Address>>;

// While lifting, backward scans may decode undiscovered bytes between known instructions. Jump table case
// bodies often sit between a hoisted table base and its dispatch, and are only discovered once the table is.
struct GapDecoder {
    std::function<std::optional<Instruction>(Address)> decode;
    Instructions speculative;
    // Registers whose values survive calls under the guest ABI.
    std::set<unsigned> preserved = {};
    // Conditional branches and direct jumps indexed by target, for predecessor searches.
    const std::map<Address, std::vector<Address>>* edges = nullptr;
    // Known function entries: values of registers are undefined there.
    const std::set<Address>* functions = nullptr;
    // Entries known only because code takes their address, which ADR also does for labels inside a function,
    // such as the base of a jump table's cases.
    const std::set<Address>* taken = nullptr;
    // The stack pointer, whose slots hold spilled values.
    unsigned stack = Zero;
    // Import slots of functions that never return.
    const std::set<Address>* noReturnSlots = nullptr;
};
thread_local GapDecoder* gapDecoder = nullptr;

// Whether a call can return to the instruction after it: not when it calls an import that never returns, through
// its slot or a stub (a PLT entry, or a Darwin stub) that jumps through the slot.
bool callReturns(const Instructions& instructions, const Call& call) {
    if (!gapDecoder || !gapDecoder->noReturnSlots || gapDecoder->noReturnSlots->empty())
        return true;
    const auto slotOf = [](const Value& target) -> std::optional<Address> {
        if (const auto* memory = std::get_if<Memory>(&target);
            memory && memory->address.base == Zero && memory->address.index == Zero)
            return memory->address.displacement;
        return std::nullopt;
    };
    auto slot = slotOf(call.target);
    if (const auto* start = std::get_if<Immediate>(&call.target); start && !slot) {
        std::map<unsigned, Address> constants, loaded;
        auto at = instructions.find(Address(start->value));
        for (unsigned steps = 0; at != instructions.end() && steps < 4; ++steps) {
            const auto& inst = at->second;
            if (const auto* move = std::get_if<Move>(&inst.effect); move && move->size == 8) {
                if (const auto* value = std::get_if<Immediate>(&move->src))
                    constants[move->dst] = Address(value->value);
                else if (const auto* memory = std::get_if<Memory>(&move->src);
                    memory && memory->address.index == Zero && constants.contains(memory->address.base))
                    loaded[move->dst] = constants[memory->address.base] + memory->address.displacement;
                else if (const auto found = slotOf(move->src))
                    loaded[move->dst] = *found;
            }
            if (inst.end) {
                if (const auto* jump = std::get_if<Jump>(&*inst.end)) {
                    if (const auto* reg = std::get_if<Register>(&jump->target); reg && loaded.contains(reg->index))
                        slot = loaded[reg->index];
                    else
                        slot = slotOf(jump->target);
                }
                break;
            }
            at = instructions.find(inst.next);
        }
    }
    return !slot || !gapDecoder->noReturnSlots->contains(*slot);
}

const Instruction* previousInstruction(const Instructions& instructions, Address& cursor) {
    auto at = instructions.lower_bound(cursor);
    if (at != instructions.begin() && std::prev(at)->second.next == cursor) {
        --at;
        cursor = at->first;
        return &at->second;
    }
    if (!gapDecoder)
        return nullptr;
    if (auto cached = gapDecoder->speculative.lower_bound(cursor); cached != gapDecoder->speculative.begin() &&
        std::prev(cached)->second.next == cursor) {
        --cached;
        cursor = cached->first;
        return &cached->second;
    }
    if (at == instructions.begin())
        return nullptr;
    const auto gapStart = std::prev(at)->second.next;
    if (gapStart >= cursor || cursor - gapStart > 1024)
        return nullptr;
    std::vector<std::pair<Address, Instruction>> decoded;
    for (auto pc = gapStart; pc < cursor;) {
        auto instruction = gapDecoder->decode(pc);
        if (!instruction || instruction->next <= pc)
            return nullptr;
        const auto next = instruction->next;
        decoded.emplace_back(pc, std::move(*instruction));
        pc = next;
        if (pc > cursor)
            return nullptr;
    }
    if (decoded.empty())
        return nullptr;
    for (auto& [pc, instruction] : decoded)
        gapDecoder->speculative.emplace(pc, std::move(instruction));
    const auto last = gapDecoder->speculative.find(decoded.back().first);
    cursor = last->first;
    return &last->second;
}

std::optional<Address> resolveRegister(const Instructions& instructions, Address pc, unsigned reg, unsigned depth = 0);
std::optional<Address> resolveLinear(const Instructions& instructions, Address pc, unsigned reg, unsigned depth);
std::optional<Address> resolveStackSlot(const Instructions& instructions, Address pc, Address offset, unsigned depth);

// Evaluates a definition of `reg` found just before `at`, or nothing when its value is not a constant.
std::optional<Address> constantDefinition(const Instructions& instructions, const Effect& effect, Address at,
    unsigned reg, unsigned depth) {
    if (const auto* move = std::get_if<Move>(&effect); move && move->size == 4 && move->dst == reg)
        if (const auto* value = std::get_if<Immediate>(&move->src))
            return Address(std::uint32_t(value->value));
    if (const auto* move = std::get_if<Move>(&effect); move && move->size == 8 && move->dst == reg) {
        if (const auto* value = std::get_if<Immediate>(&move->src))
            return Address(value->value);
        if (const auto* address = std::get_if<EffectiveAddress>(&move->src);
            address && address->base == Zero && address->index == Zero)
            return address->displacement;
        if (const auto* source = std::get_if<Register>(&move->src))
            return resolveRegister(instructions, at, source->index, depth + 1);
        // A reload of a spilled value, as compilers spill jump-table bases in large functions.
        if (const auto* memory = std::get_if<Memory>(&move->src); memory && gapDecoder &&
            gapDecoder->stack != Zero && memory->address.base == gapDecoder->stack && memory->address.index == Zero)
            return resolveStackSlot(instructions, at, memory->address.displacement, depth + 1);
    }
    if (const auto* add = std::get_if<Binary>(&effect); add && add->size == 8 && add->op == BinaryOp::Add &&
        add->dst == reg && !add->count && !add->extendBits && !add->invert && !add->withCarry)
        if (const auto* value = std::get_if<Immediate>(&add->rhs))
            if (const auto base = resolveRegister(instructions, at, add->lhs, depth + 1))
                return *base + Address(value->value);
    return std::nullopt;
}

// Resolves a register by searching predecessors through fallthrough, branch, and jump edges; every path
// that reaches `pc` must define the register to the same constant.
std::optional<Address> resolveThroughPredecessors(const Instructions& instructions, Address pc, unsigned reg,
    unsigned depth) {
    if (!gapDecoder || !gapDecoder->edges)
        return std::nullopt;
    std::optional<Address> found;
    std::set<Address> visited;
    std::vector<Address> work{pc};
    unsigned budget = 4096;
    while (!work.empty()) {
        const auto cursor = work.back();
        work.pop_back();
        if (!visited.insert(cursor).second)
            continue;
        if (--budget == 0)
            return std::nullopt;
        // Reaching the function's entry leaves the register with the caller's value. A taken address that
        // other code reaches is a label, and the search continues through its predecessors.
        if (cursor != pc && gapDecoder->functions && gapDecoder->functions->contains(cursor) &&
            !(gapDecoder->taken && gapDecoder->taken->contains(cursor)))
            return std::nullopt;
        std::vector<std::pair<Address, const Instruction*>> predecessors;
        if (auto at = instructions.lower_bound(cursor); at != instructions.begin()) {
            --at;
            const auto* end = at->second.end ? &*at->second.end : nullptr;
            const auto* call = end ? std::get_if<Call>(end) : nullptr;
            const bool fallsThrough = !end || std::holds_alternative<Branch>(*end) ||
                (call && callReturns(instructions, *call));
            if (at->second.next == cursor && fallsThrough)
                predecessors.emplace_back(at->first, &at->second);
        }
        if (const auto into = gapDecoder->edges->find(cursor); into != gapDecoder->edges->end())
            for (const auto source : into->second)
                if (const auto at = instructions.find(source); at != instructions.end())
                    predecessors.emplace_back(source, &at->second);
        if (predecessors.empty()) {
            // Code without known predecessors is entered through unresolved indirect jumps, typically the
            // table being recovered, whose cases ADR may take; only function entries leave the register undefined.
            if (gapDecoder->functions && gapDecoder->functions->contains(cursor) &&
                !(gapDecoder->taken && gapDecoder->taken->contains(cursor)))
                return std::nullopt;
            continue;
        }
        for (const auto& [address, inst] : predecessors) {
            if (inst->end && std::holds_alternative<Call>(*inst->end) && !gapDecoder->preserved.contains(reg))
                return std::nullopt;
            std::vector<const Effect*> effects{&inst->effect};
            for (const auto& effect : inst->after)
                effects.push_back(&effect);
            bool defined = false;
            for (auto it = effects.rbegin(); it != effects.rend(); ++it) {
                if (!writesRegister(**it, reg))
                    continue;
                const auto value = constantDefinition(instructions, **it, address, reg, depth);
                if (!value || (found && *found != *value))
                    return std::nullopt;
                found = value;
                defined = true;
                break;
            }
            if (!defined)
                work.push_back(address);
        }
    }
    return found;
}

// Resolves the eight-byte stack slot `offset` bytes above the stack pointer just before `pc`: every path there must
// store the same constant in it, and none may move the stack pointer after the store.
std::optional<Address> resolveStackSlot(const Instructions& instructions, Address pc, Address offset, unsigned depth) {
    if (!gapDecoder || !gapDecoder->edges || gapDecoder->stack == Zero || depth > 4)
        return std::nullopt;
    const auto sp = gapDecoder->stack;
    const auto entry = [&](Address at) {
        return gapDecoder->functions && gapDecoder->functions->contains(at) &&
            !(gapDecoder->taken && gapDecoder->taken->contains(at));
    };
    // A store that overlaps the slot without filling it, or stores something other than a register.
    constexpr unsigned Spoiled = ~0u;
    std::optional<Address> found;
    std::set<Address> visited;
    std::vector<Address> work{pc};
    unsigned budget = 4096;
    while (!work.empty()) {
        const auto cursor = work.back();
        work.pop_back();
        if (!visited.insert(cursor).second)
            continue;
        if (--budget == 0 || (cursor != pc && entry(cursor)))
            return std::nullopt;
        std::vector<std::pair<Address, const Instruction*>> predecessors;
        if (auto at = instructions.lower_bound(cursor); at != instructions.begin()) {
            --at;
            const auto* end = at->second.end ? &*at->second.end : nullptr;
            const auto* call = end ? std::get_if<Call>(end) : nullptr;
            const bool fallsThrough = !end || std::holds_alternative<Branch>(*end) ||
                (call && callReturns(instructions, *call));
            if (at->second.next == cursor && fallsThrough)
                predecessors.emplace_back(at->first, &at->second);
        }
        if (const auto into = gapDecoder->edges->find(cursor); into != gapDecoder->edges->end())
            for (const auto source : into->second)
                if (const auto at = instructions.find(source); at != instructions.end())
                    predecessors.emplace_back(source, &at->second);
        if (predecessors.empty()) {
            if (entry(cursor))
                return std::nullopt;
            continue;
        }
        for (const auto& [address, inst] : predecessors) {
            std::vector<const Effect*> effects{&inst->effect};
            for (const auto& effect : inst->after)
                effects.push_back(&effect);
            std::optional<unsigned> stored;
            for (auto it = effects.rbegin(); it != effects.rend() && !stored; ++it) {
                const auto& effect = **it;
                if (writesRegister(effect, sp))
                    return std::nullopt;
                // Which register the instruction stores to the slot; a store that only overlaps it spoils it.
                const auto consider = [&](unsigned size, Address at, unsigned reg) {
                    if (at == offset && size == 8)
                        stored = reg;
                    else if (at < offset + 8 && offset < at + Address(size))
                        stored = Spoiled;
                };
                if (const auto* store = std::get_if<Store>(&effect);
                    store && store->address.base == sp && store->address.index == Zero) {
                    const auto* source = std::get_if<Register>(&store->src);
                    consider(store->size, store->address.displacement, source ? source->index : Spoiled);
                } else if (const auto* pair = std::get_if<PairTransfer>(&effect);
                    pair && !pair->load && pair->address.base == sp && pair->address.index == Zero) {
                    consider(pair->size, pair->address.displacement, pair->first);
                    if (!stored)
                        consider(pair->size, pair->address.displacement + Address(pair->size), pair->second);
                }
            }
            if (!stored) {
                work.push_back(address);
                continue;
            }
            const auto value = *stored == Spoiled ? std::nullopt : resolveRegister(instructions, address, *stored, depth + 1);
            if (!value || (found && *found != *value))
                return std::nullopt;
            found = value;
        }
    }
    return found;
}

// Resolves a register to a constant just before `pc`. The predecessor search handles hoisted jump-table
// bases across loops; a contiguous backward scan covers code whose edges are not yet decoded.
std::optional<Address> resolveRegister(const Instructions& instructions, Address pc, unsigned reg, unsigned depth) {
    if (reg == Zero)
        return 0;
    if (depth > 4)
        return std::nullopt;
    if (const auto value = resolveThroughPredecessors(instructions, pc, reg, depth))
        return value;
    return resolveLinear(instructions, pc, reg, depth);
}

std::optional<Address> resolveLinear(const Instructions& instructions, Address pc, unsigned reg, unsigned depth) {
    if (reg == Zero)
        return 0;
    if (depth > 4)
        return std::nullopt;
    auto cursor = pc;
    for (unsigned steps = 0; steps < 768; ++steps) {
        const auto* inst = previousInstruction(instructions, cursor);
        if (!inst || (inst->end && std::holds_alternative<Call>(*inst->end) &&
            !(gapDecoder && gapDecoder->preserved.contains(reg))))
            return std::nullopt;
        std::vector<const Effect*> effects{&inst->effect};
        for (const auto& effect : inst->after)
            effects.push_back(&effect);
        for (auto it = effects.rbegin(); it != effects.rend(); ++it) {
            const auto& effect = **it;
            if (!writesRegister(effect, reg))
                continue;
            if (const auto* move = std::get_if<Move>(&effect); move && move->size == 8) {
                if (const auto* value = std::get_if<Immediate>(&move->src))
                    return Address(value->value);
                if (const auto* address = std::get_if<EffectiveAddress>(&move->src);
                    address && address->base == Zero && address->index == Zero)
                    return address->displacement;
                if (const auto* source = std::get_if<Register>(&move->src))
                    return resolveRegister(instructions, cursor, source->index, depth + 1);
            }
            if (const auto* add = std::get_if<Binary>(&effect); add && add->size == 8 && add->op == BinaryOp::Add &&
                !add->count && !add->extendBits && !add->invert && !add->withCarry) {
                if (const auto* value = std::get_if<Immediate>(&add->rhs))
                    if (const auto base = resolveRegister(instructions, cursor, add->lhs, depth + 1))
                        return *base + Address(value->value);
            }
            return std::nullopt;
        }
    }
    return std::nullopt;
}

// The constant a bounds check compares against: an immediate or a register holding a constant.
std::optional<std::uint64_t> compareLimit(const Instructions& instructions, Address at, const Binary& check) {
    if (const auto* value = std::get_if<Immediate>(&check.rhs))
        return check.size == 4 ? std::uint32_t(value->value) : value->value;
    if (const auto* source = std::get_if<Register>(&check.rhs))
        if (const auto value = resolveRegister(instructions, at, source->index); value && *value >= 0)
            return std::uint64_t(*value);
    return std::nullopt;
}

// A bounds check `cmp x, N` of any operand width, where x is a register or a memory operand.
struct BoundsCheck {
    unsigned reg = Zero;
    std::optional<EffectiveAddress> memory = {};
    std::uint64_t limit = 0;
    unsigned size = 8;
};

std::optional<BoundsCheck> boundsCheck(const Instructions& instructions, Address at, const Effect& effect) {
    if (const auto* check = std::get_if<Binary>(&effect); check && check->op == BinaryOp::Sub && check->dst == Zero &&
        check->flags && !check->count && !check->extendBits)
        if (const auto limit = compareLimit(instructions, at, *check))
            return BoundsCheck{check->lhs, std::nullopt, *limit, check->size};
    if (const auto* check = std::get_if<ByteBinary>(&effect); check && check->op == BinaryOp::Sub && !check->writeBack &&
        !check->lhsField && !check->reverse) {
        if (const auto* limit = std::get_if<Immediate>(&check->rhs)) {
            if (const auto* reg = std::get_if<Register>(&check->lhs))
                return BoundsCheck{reg->index, std::nullopt, limit->value & 0xff, 1};
            if (const auto* memory = std::get_if<Memory>(&check->lhs))
                return BoundsCheck{Zero, memory->address, limit->value & 0xff, 1};
        }
    }
    if (const auto* check = std::get_if<MemoryBinary>(&effect); check && check->op == BinaryOp::Sub && !check->writeBack) {
        if (const auto* limit = std::get_if<Immediate>(&check->rhs)) {
            const auto value = check->size == 2 ? limit->value & 0xffff : check->size == 4 ? limit->value & 0xffffffff :
                limit->value;
            if (const auto* reg = std::get_if<Register>(&check->dst))
                return BoundsCheck{reg->index, std::nullopt, value, check->size};
            if (const auto* memory = std::get_if<Memory>(&check->dst))
                return BoundsCheck{Zero, memory->address, value, check->size};
        }
    }
    return std::nullopt;
}

// Finds `cmp index, #N` followed by a branch that guards entry to the straight-line run containing `load`.
std::optional<std::size_t> guardedBound(const Instructions& instructions, const BranchIndex& branches, Address load,
    unsigned index, bool arm) {
    // Guards may branch to any instruction of the straight-line run, past alignment padding.
    std::vector<Address> starts{load};
    std::set<unsigned> aliases{index};
    std::vector<EffectiveAddress> memoryAliases;
    for (auto cursor = load;;) {
        const auto* inst = previousInstruction(instructions, cursor);
        if (!inst || inst->end)
            break;
        starts.push_back(cursor);
        // An extension, copy, or load into the index lets the guard compare the original value.
        if (const auto* extend = std::get_if<Extend>(&inst->effect); extend && aliases.contains(extend->dst) &&
            !extend->sign && !extend->field) {
            if (const auto* source = std::get_if<Register>(&extend->src))
                aliases.insert(source->index);
            else if (const auto* memory = std::get_if<Memory>(&extend->src))
                memoryAliases.push_back(memory->address);
        }
        if (const auto* move = std::get_if<Move>(&inst->effect); move && aliases.contains(move->dst)) {
            if (const auto* source = std::get_if<Register>(&move->src))
                aliases.insert(source->index);
            else if (const auto* memory = std::get_if<Memory>(&move->src))
                memoryAliases.push_back(memory->address);
        }
    }
    std::optional<std::size_t> best;
    for (const auto start : starts) {
    const auto into = branches.find(start);
    for (const auto pc : into == branches.end() ? std::vector<Address>{} : into->second) {
        const auto& inst = instructions.at(pc);
        const auto* branch = inst.end ? std::get_if<Branch>(&*inst.end) : nullptr;
        const auto* flags = branch ? std::get_if<FlagsCondition>(&branch->condition) : nullptr;
        if (!flags || (branch->taken != start && branch->other != start))
            continue;
        const bool taken = branch->taken == start;
        // Codes for "index <= N" and "index < N" on the path into the table.
        const unsigned lessEqual = arm ? 9 : 6, less = arm ? 3 : 2, greater = arm ? 8 : 7, greaterEqual = arm ? 2 : 3;
        std::optional<bool> inclusive;
        if (taken && flags->code == lessEqual) inclusive = true;
        else if (taken && flags->code == less) inclusive = false;
        else if (!taken && flags->code == greater) inclusive = true;
        else if (!taken && flags->code == greaterEqual) inclusive = false;
        if (!inclusive)
            continue;
        auto cursor = pc;
        const auto* compare = previousInstruction(instructions, cursor);
        const auto check = compare && !compare->end ? boundsCheck(instructions, cursor, compare->effect) : std::nullopt;
        const bool related = check && (check->memory ? std::ranges::find(memoryAliases, *check->memory) !=
            memoryAliases.end() : aliases.contains(check->reg));
        if (!related || check->limit >= 4096)
            continue;
        const auto bound = std::size_t(check->limit) + (*inclusive ? 1 : 0);
        if (!best || bound < *best)
            best = bound;
    }
    }
    return best;
}

// Recognizes `movslq (base, index, 4), target; add base, target; jmp *target` where the table base was
// materialized anywhere earlier in the function.
// What bounds a table that no compare guards: a switch over every value of an enumeration needs no bounds
// check, so its table ends where the next data the code refers to begins, and its cases stay in the function.
struct Unguarded {
    const std::set<Address>& boundaries;
    Address functionStart;
    Address functionEnd;
};

void recoverHoistedX64Table(Address pc, Jump& jump, const Instructions& instructions, const BranchIndex& branches,
    std::span<const std::uint8_t> image, std::span<const GuestRegion> regions, References& references,
    const Unguarded* unguarded = nullptr) {
    const auto* target = std::get_if<Register>(&jump.target);
    if (!target)
        return;
    auto cursor = pc;
    const auto* inst = previousInstruction(instructions, cursor);
    for (unsigned skipped = 0; inst && skipped < 4 && !inst->end && inst->after.empty() &&
        !writesRegister(inst->effect, target->index); ++skipped)
        inst = previousInstruction(instructions, cursor);
    const auto* add = inst ? std::get_if<Binary>(&inst->effect) : nullptr;
    const auto* base = add ? std::get_if<Register>(&add->rhs) : nullptr;
    if (!add || !base || add->op != BinaryOp::Add || add->size != 8 || add->count || add->dst != target->index ||
        add->lhs != target->index || base->index == target->index)
        return;
    // A table that no compare guards: its entries are cases before it, up to the next address the code refers to.
    const auto scanUnguarded = [&](Address table, Address codeBase) {
        const bool inlineData = executableEnd(std::size_t(table), image.size(), regions) != 0;
        const auto next = unguarded->boundaries.upper_bound(table);
        const auto limit = std::min<std::size_t>(1024, next == unguarded->boundaries.end() ? 1024 : (*next - table) / 4);
        recordJumpTable(jump, image, regions, references, std::size_t(table), 4, limit, false, codeBase, 1, true,
            inlineData);
        if (!jump.destinations.empty() && (jump.destinations.front() < unguarded->functionStart ||
            jump.destinations.back() >= unguarded->functionEnd)) {
            jump.destinations.clear();
            references.tables.pop_back();
        }
    };
    if (unguarded) {
        // Unoptimized code adds the entry to the table's address instead, so the target holds the table.
        auto scan = cursor;
        const Extend* entry = nullptr;
        for (unsigned skipped = 0; skipped < 4 && !entry; ++skipped) {
            const auto* prior = previousInstruction(instructions, scan);
            if (!prior || prior->end)
                break;
            if (const auto* extend = std::get_if<Extend>(&prior->effect); extend && extend->dst == base->index)
                entry = extend;
            else if (writesRegister(prior->effect, base->index) || writesRegister(prior->effect, target->index))
                break;
        }
        const auto* slot = entry ? std::get_if<Memory>(&entry->src) : nullptr;
        if (slot && entry->sign && entry->size == 8 && entry->bits == 32 && slot->address.base == target->index &&
            slot->address.index != Zero && slot->address.index != target->index && slot->address.scale == 4)
            if (const auto codeBase = resolveRegister(instructions, scan, target->index); codeBase && *codeBase >= 0) {
                scanUnguarded(*codeBase + slot->address.displacement, *codeBase);
                return;
            }
    }
    const Extend* load = nullptr;
    for (unsigned skipped = 0; skipped < 4 && !load; ++skipped) {
        inst = previousInstruction(instructions, cursor);
        if (!inst || inst->end)
            return;
        if (const auto* extend = std::get_if<Extend>(&inst->effect); extend && extend->dst == target->index)
            load = extend;
        else if (writesRegister(inst->effect, target->index) || writesRegister(inst->effect, base->index))
            return;
    }
    const auto* memory = load ? std::get_if<Memory>(&load->src) : nullptr;
    if (!memory || !load->sign || load->size != 8 || load->bits != 32 || memory->address.base != base->index ||
        memory->address.index == Zero || memory->address.scale != 4)
        return;
    const auto codeBase = resolveRegister(instructions, cursor, base->index);
    if (!codeBase || *codeBase < 0)
        return;
    const auto table = *codeBase + memory->address.displacement;
    if (table < 0)
        return;
    const auto bound = guardedBound(instructions, branches, cursor, memory->address.index, false);
    const bool inlineData = executableEnd(std::size_t(table), image.size(), regions) != 0;
    if (!bound && unguarded) {
        // Tables among the code end at the first entry that is not a case before them.
        scanUnguarded(table, *codeBase);
        return;
    }
    if (!bound)
        return;
    recordJumpTable(jump, image, regions, references, std::size_t(table), 4, *bound, true, *codeBase, 1, true, inlineData);
}

// Recognizes `ldr{b,h,} w, [base, index]; add target, code, w{, sxtb|lsl #n}; br target` with ADR/ADRP
// materializations of `code` and `base` anywhere earlier in the function.
void recoverHoistedArmTable(Address pc, Jump& jump, const Instructions& instructions, const BranchIndex& branches,
    std::span<const std::uint8_t> image, std::span<const GuestRegion> regions, References& references,
    const Unguarded* unguarded = nullptr) {
    const auto* target = std::get_if<Register>(&jump.target);
    if (!target)
        return;
    auto cursor = pc;
    const Binary* sum = nullptr;
    Address sumAt = pc;
    for (unsigned skipped = 0; skipped < 4 && !sum; ++skipped) {
        const auto* inst = previousInstruction(instructions, cursor);
        if (!inst || inst->end)
            return;
        if (const auto* binary = std::get_if<Binary>(&inst->effect); binary && binary->dst == target->index)
            sum = binary, sumAt = cursor;
        else if (writesRegister(inst->effect, target->index))
            return;
    }
    const auto* offsetReg = sum ? std::get_if<Register>(&sum->rhs) : nullptr;
    if (!sum || !offsetReg || sum->op != BinaryOp::Add || sum->size != 8 || sum->flags || sum->shift != ShiftOp::Left ||
        sum->count > 4 || (sum->extendBits && sum->extendBits != 8 && sum->extendBits != 16 && sum->extendBits != 32))
        return;
    const Effect* loadEffect = nullptr;
    Address loadAt = sumAt;
    cursor = sumAt;
    for (unsigned skipped = 0; skipped < 4 && !loadEffect; ++skipped) {
        const auto* inst = previousInstruction(instructions, cursor);
        if (!inst || inst->end)
            return;
        if (writesRegister(inst->effect, offsetReg->index))
            loadEffect = &inst->effect, loadAt = cursor;
    }
    if (!loadEffect)
        return;
    const Memory* memory = nullptr;
    unsigned width = 0;
    bool sign = sum->extendBits && sum->signExtend;
    if (const auto* extend = std::get_if<Extend>(loadEffect); extend && extend->dst == offsetReg->index && !extend->field) {
        memory = std::get_if<Memory>(&extend->src);
        width = extend->bits / 8;
        sign = sign || extend->sign;
    } else if (const auto* move = std::get_if<Move>(loadEffect); move && move->dst == offsetReg->index && move->size == 4) {
        memory = std::get_if<Memory>(&move->src);
        width = 4;
    }
    if (!memory || (width != 1 && width != 2 && width != 4) || memory->address.index == Zero ||
        (memory->address.scale != 1 && memory->address.scale != width) || memory->address.displacement != 0)
        return;
    if (sum->extendBits && sum->extendBits < width * 8)
        width = sum->extendBits / 8;
    const auto code = resolveRegister(instructions, sumAt, sum->lhs);
    const auto table = resolveRegister(instructions, loadAt, memory->address.base);
    if (!code || !table || *code < 0 || *table < 0)
        return;
    auto bound = guardedBound(instructions, branches, loadAt, memory->address.index, true);
    // A switch on the low bits of a value can mask the index instead of branching on its range.
    if (!bound && memory->address.scale == width) {
        auto at = instructions.find(loadAt);
        while (at != instructions.begin() && at != instructions.end() && !branches.contains(at->first) &&
            !(gapDecoder && gapDecoder->functions && gapDecoder->functions->contains(at->first))) {
            const auto next = at->first;
            const auto& inst = (--at)->second;
            if (inst.next != next || inst.end || !inst.after.empty())
                break;
            if (!writesRegister(inst.effect, memory->address.index))
                continue;
            if (const auto* mask = std::get_if<Binary>(&inst.effect); mask && mask->op == BinaryOp::And &&
                !mask->count && !mask->invert && !mask->extendBits && !mask->withCarry)
                if (const auto* bits = std::get_if<Immediate>(&mask->rhs); bits && bits->value < 4096 &&
                    (bits->value & (bits->value + 1)) == 0)
                    bound = bits->value + 1;
            break;
        }
    }
    if (!bound && unguarded) {
        const auto next = unguarded->boundaries.upper_bound(*table);
        const auto entries = next == unguarded->boundaries.end() ? 0 : std::size_t(*next - *table) / width;
        if (entries >= 2 && entries <= (width == 1 ? 256u : 1024u))
            bound = entries;
    }
    if (!bound)
        return;
    const bool inlineData = executableEnd(std::size_t(*table), image.size(), regions) != 0;
    recordJumpTable(jump, image, regions, references, std::size_t(*table), width, *bound, true, *code,
        1u << sum->count, sign, inlineData);
    if (unguarded && !jump.destinations.empty() &&
        (jump.destinations.front() < unguarded->functionStart || jump.destinations.back() >= unguarded->functionEnd)) {
        jump.destinations.clear();
        references.tables.pop_back();
    }
}

// Evaluates the code between a jump table's bounds check and its indirect jump once per index value.
// This covers dispatch sequences the pattern matchers miss, such as unoptimized code that spills the index.
class TableSimulator {
public:
    TableSimulator(const Instructions& instructions, std::span<const std::uint8_t> image,
        std::span<const GuestRegion> regions, Address start)
        : instructions(instructions), image(image), regions(regions), start(start) {}

    std::array<std::optional<std::uint64_t>, RegisterCount> registers{};
    std::map<std::uint64_t, std::uint64_t> memory;
    std::set<std::pair<std::size_t, std::size_t>> reads;
    bool failed = false;

    std::optional<std::uint64_t> get(unsigned reg) {
        if (reg == Zero)
            return 0;
        if (reg >= RegisterCount)
            return std::nullopt;
        if (!registers[reg]) {
            if (const auto value = resolveRegister(instructions, start, reg))
                registers[reg] = std::uint64_t(*value);
            else
                registers[reg] = Placeholder + std::uint64_t(reg) * 0x100000000ull;
        }
        return registers[reg];
    }

    void set(unsigned reg, std::optional<std::uint64_t> value, unsigned size) {
        if (reg == Zero || reg >= RegisterCount)
            return;
        if (value && size == 4)
            value = std::uint32_t(*value);
        else if (size < 4)
            value.reset();
        registers[reg] = value ? value : std::optional<std::uint64_t>(Unknown);
    }

    static bool known(std::optional<std::uint64_t> value) {
        return value && *value != Unknown;
    }

    std::optional<std::uint64_t> address(const EffectiveAddress& at) {
        const auto base = get(at.base);
        auto index = get(at.index);
        if (!known(base) || !known(index))
            return std::nullopt;
        if (at.indexWidth == IndexWidth::Unsigned32)
            index = std::uint32_t(*index);
        else if (at.indexWidth == IndexWidth::Signed32)
            index = std::uint64_t(std::int64_t(std::int32_t(*index)));
        return *base + *index * at.scale + std::uint64_t(at.displacement);
    }

    std::optional<std::uint64_t> load(std::optional<std::uint64_t> at, unsigned size) {
        if (!at)
            return std::nullopt;
        if (const auto stored = memory.find(*at); stored != memory.end())
            return size == 8 ? stored->second : stored->second & ((std::uint64_t(1) << (size * 8)) - 1);
        if (*at >= image.size() || size > image.size() - *at || (!regions.empty() &&
            !std::ranges::any_of(regions, [&](const GuestRegion& region) {
                return region.readable && !region.writable && *at >= region.start && *at + size <= region.end;
            })))
            return std::nullopt;
        std::uint64_t value = 0;
        for (unsigned i = 0; i < size; ++i)
            value |= std::uint64_t(image[*at + i]) << (8 * i);
        reads.emplace(std::size_t(*at), size);
        return value;
    }

    std::optional<std::uint64_t> operand(const Value& value, unsigned size) {
        if (const auto* imm = std::get_if<Immediate>(&value))
            return imm->value;
        if (const auto* reg = std::get_if<Register>(&value))
            return get(reg->index);
        if (const auto* at = std::get_if<EffectiveAddress>(&value))
            return address(*at);
        if (const auto* mem = std::get_if<Memory>(&value))
            return load(address(mem->address), size);
        return std::nullopt;
    }

    static std::uint64_t extend(std::uint64_t value, unsigned bits, bool sign) {
        if (bits >= 64)
            return value;
        value &= (std::uint64_t(1) << bits) - 1;
        if (sign && (value >> (bits - 1)) & 1)
            value |= ~((std::uint64_t(1) << bits) - 1);
        return value;
    }

    static std::uint64_t shifted(std::uint64_t value, ShiftOp op, unsigned count, unsigned size) {
        const unsigned bits = size * 8;
        if (bits == 32)
            value = std::uint32_t(value);
        if (!count)
            return value;
        switch (op) {
            case ShiftOp::Left: return value << count;
            case ShiftOp::LogicalRight: return value >> count;
            case ShiftOp::ArithmeticRight: return std::uint64_t(std::int64_t(extend(value, bits, true)) >> count);
            case ShiftOp::RotateRight: return value >> count | value << (bits - count);
            case ShiftOp::RotateLeft: return value << count | value >> (bits - count);
        }
        return value;
    }

    void execute(const Effect& effect) {
        std::visit(Visit{
            [&](const Nop&) {},
            [&](const Move& move) {
                if (std::holds_alternative<StackTop>(move.src)) {
                    const auto sp = get(4);
                    set(move.dst, known(sp) ? load(*sp, 8) : std::nullopt, 8);
                    if (known(sp))
                        set(4, *sp + 8, 8);
                    return;
                }
                set(move.dst, operand(move.src, move.size), move.size);
            },
            [&](const Extend& op) {
                std::optional<std::uint64_t> value;
                if (const auto* reg = std::get_if<Register>(&op.src)) {
                    if (const auto source = get(reg->index); known(source))
                        value = *source >> op.field;
                } else if (const auto* mem = std::get_if<Memory>(&op.src)) {
                    value = load(address(mem->address), op.bits / 8);
                }
                if (value)
                    value = extend(*value, op.bits, op.sign);
                set(op.dst, value, op.size);
            },
            [&](const Binary& op) {
                if (op.dst == Zero)
                    return;
                auto rhs = operand(op.rhs, op.size);
                const auto lhs = get(op.lhs);
                if (!known(lhs) || !known(rhs) || op.withCarry) {
                    set(op.dst, std::nullopt, 8);
                    return;
                }
                auto value = *rhs;
                if (op.extendBits)
                    value = extend(value, op.extendBits, op.signExtend) << op.count;
                else
                    value = shifted(value, op.shift, op.count, op.size);
                if (op.invert)
                    value = ~value;
                set(op.dst, fold(op.op, *lhs, value), op.size);
            },
            [&](const Shift& op) {
                const auto value = get(op.dst.index);
                set(op.dst.index, known(value) ? std::optional(shifted(*value, op.op, op.count, op.size)) : std::nullopt, op.size);
            },
            [&](const Bitfield& op) {
                const auto value = get(op.src.index);
                if (!known(value) || op.insert) {
                    set(op.dst, std::nullopt, 8);
                    return;
                }
                set(op.dst, extend(*value >> op.start, op.width, op.sign) << op.position, op.size);
            },
            [&](const Multiply& op) {
                const auto lhs = operand(op.lhs, op.size);
                const auto rhs = operand(op.rhs, op.size);
                const bool simple = op.operands == MultiplyOperands::Full && op.accumulator == Zero && !op.subtract;
                set(op.dst, simple && known(lhs) && known(rhs) ? std::optional(*lhs * *rhs) : std::nullopt, op.size);
            },
            [&](const Store& store) {
                const auto at = address(store.address);
                const auto value = operand(store.src, 8);
                if (at && known(value))
                    memory[*at] = store.size == 8 ? *value : *value & ((std::uint64_t(1) << (store.size * 8)) - 1);
                else if (at)
                    memory.erase(*at);
            },
            [&](const PairTransfer& pair) {
                if (pair.vector) {
                    if (pair.writeback)
                        set(pair.address.base, std::nullopt, 8);
                    return;
                }
                const auto first = address(pair.address);
                const auto second = first ? std::optional(*first + pair.size) : std::nullopt;
                if (pair.load) {
                    set(pair.first, load(first, pair.size), pair.size);
                    set(pair.second, load(second, pair.size), pair.size);
                } else if (first) {
                    for (const auto [reg, at] : {std::pair{pair.first, *first}, std::pair{pair.second, *second}}) {
                        if (const auto value = get(reg); known(value))
                            memory[at] = pair.size == 8 ? *value : std::uint32_t(*value);
                        else
                            memory.erase(at);
                    }
                }
                if (pair.writeback) {
                    const auto base = get(pair.address.base);
                    set(pair.address.base, known(base) ? std::optional(*base + std::uint64_t(pair.writeback)) : std::nullopt, 8);
                }
            },
            [&](const Push& push) {
                const auto sp = get(4);
                const auto value = operand(push.src, 8);
                if (!known(sp)) {
                    failed = true;
                    return;
                }
                set(4, *sp - 8, 8);
                if (known(value))
                    memory[*sp - 8] = *value;
            },
            [&](const auto& other) {
                for (unsigned reg = 0; reg < RegisterCount; ++reg)
                    if (writesRegister(Effect(other), reg))
                        set(reg, std::nullopt, 8);
            },
        }, effect);
    }

    void run(const Instruction& instruction) {
        execute(instruction.effect);
        for (const auto& effect : instruction.after)
            execute(effect);
    }

private:
    static constexpr std::uint64_t Placeholder = 0x7f0000000000ull;
    static constexpr std::uint64_t Unknown = 0xdead0000dead0000ull;
    const Instructions& instructions;
    std::span<const std::uint8_t> image;
    std::span<const GuestRegion> regions;
    Address start;
};

void recoverSimulatedTable(Address pc, Jump& jump, const Instructions& instructions, const BranchIndex& branches,
    std::span<const std::uint8_t> image, std::span<const GuestRegion> regions, References& references, bool arm) {
    const auto* target = std::get_if<Register>(&jump.target);
    if (!target)
        return;
    // The straight-line run that ends at the jump.
    std::vector<std::pair<Address, const Instruction*>> fullRun;
    auto cursor = pc;
    while (fullRun.size() < 24) {
        const auto* inst = previousInstruction(instructions, cursor);
        if (!inst || inst->end)
            break;
        fullRun.emplace_back(cursor, inst);
    }
    std::ranges::reverse(fullRun);
    for (std::size_t first = 0; first <= fullRun.size(); ++first) {
    const auto runStart = first < fullRun.size() ? fullRun[first].first : pc;
    std::vector<const Instruction*> run;
    for (auto i = first; i < fullRun.size(); ++i)
        run.push_back(fullRun[i].second);
    // The guard is a compare against a constant that branches into the run.
    const auto into = branches.find(runStart);
    for (const auto branchAt : into == branches.end() ? std::vector<Address>{} : into->second) {
        const auto& branchInstruction = instructions.at(branchAt);
        const auto* branch = branchInstruction.end ? std::get_if<Branch>(&*branchInstruction.end) : nullptr;
        const auto* flags = branch ? std::get_if<FlagsCondition>(&branch->condition) : nullptr;
        if (!flags || (branch->taken != runStart && branch->other != runStart))
            continue;
        const bool taken = branch->taken == runStart;
        const unsigned lessEqual = arm ? 9 : 6, less = arm ? 3 : 2, greater = arm ? 8 : 7, greaterEqual = arm ? 2 : 3;
        std::optional<bool> inclusive;
        if (taken && flags->code == lessEqual) inclusive = true;
        else if (taken && flags->code == less) inclusive = false;
        else if (!taken && flags->code == greater) inclusive = true;
        else if (!taken && flags->code == greaterEqual) inclusive = false;
        if (!inclusive)
            continue;
        auto compareAt = branchAt;
        const auto* compare = previousInstruction(instructions, compareAt);
        auto check = compare && !compare->end ? boundsCheck(instructions, compareAt, compare->effect) : std::nullopt;
        // ARM64 compares may also write their difference (SUBS x8, x8, #N).
        if (!check && compare && !compare->end)
            if (const auto* sub = std::get_if<Binary>(&compare->effect); sub && sub->op == BinaryOp::Sub && sub->flags &&
                !sub->count && !sub->extendBits)
                if (const auto limit = compareLimit(instructions, compareAt, *sub))
                    check = BoundsCheck{sub->lhs, std::nullopt, *limit, sub->size};
        if (!check || check->limit >= 4096)
            continue;
        const auto index = check->reg;
        const auto bound = std::size_t(check->limit) + (*inclusive ? 1 : 0);
        // Unoptimized code spills the index before comparing it, so begin at the earliest instruction that
        // still sees the compared value in its register.
        std::vector<const Instruction*> prefix{compare};
        auto prefixStart = compareAt;
        for (auto back = compareAt; !check->memory && prefix.size() < 10;) {
            const auto* inst = previousInstruction(instructions, back);
            if (!inst || inst->end || writesRegister(inst->effect, index) ||
                std::ranges::any_of(inst->after, [&](const Effect& e) { return writesRegister(e, index); }))
                break;
            prefix.insert(prefix.begin(), inst);
            prefixStart = back;
        }
        std::set<Address> destinations;
        std::set<std::pair<std::size_t, std::size_t>> reads;
        bool valid = bound >= 2;
        for (std::size_t value = 0; valid && value < bound; ++value) {
            TableSimulator simulator(instructions, image, regions, prefixStart);
            if (check->memory) {
                // The compared memory holds the index; later loads of it read the simulated value.
                const auto at = simulator.address(*check->memory);
                if (!at) {
                    valid = false;
                    break;
                }
                simulator.memory[*at] = value;
            } else {
                simulator.registers[index] = value;
            }
            for (const auto* inst : prefix)
                simulator.run(*inst);
            for (const auto* inst : run)
                simulator.run(*inst);
            const auto destination = simulator.registers[target->index];
            if (simulator.failed || !destination || *destination >= image.size() ||
                std::size_t(*destination) >= executableEnd(*destination, image.size(), regions) ||
                (arm && *destination % 4)) {
                valid = false;
                break;
            }
            destinations.insert(Address(*destination));
            reads.insert(simulator.reads.begin(), simulator.reads.end());
        }
        if (!valid || destinations.empty())
            continue;
        jump.destinations.assign(destinations.begin(), destinations.end());
        for (const auto& [at, size] : reads)
            references.tables.push_back({at, size});
        return;
    }
    }
}

// A table that no compare guards, read by dispatch code the pattern matchers miss, such as unoptimized code that
// spills the index: the straight-line run before the jump runs once per value of each register it could take the
// index from. The register whose value moves the table read by one entry is the index; the table ends at the next
// address the code refers to, or at the first entry that is not a case of the function.
void recoverUnguardedSimulatedTable(Address pc, Jump& jump, const Instructions& instructions,
    std::span<const std::uint8_t> image, std::span<const GuestRegion> regions, References& references,
    const Unguarded& unguarded, bool arm) {
    const auto* target = std::get_if<Register>(&jump.target);
    if (!target)
        return;
    std::vector<std::pair<Address, const Instruction*>> run;
    auto cursor = pc;
    while (run.size() < 24) {
        const auto* inst = previousInstruction(instructions, cursor);
        if (!inst || inst->end)
            break;
        run.emplace_back(cursor, inst);
    }
    if (run.empty())
        return;
    std::ranges::reverse(run);
    const auto runStart = run.front().first;
    const auto simulate = [&](unsigned index, std::uint64_t value, TableSimulator& simulator) {
        simulator.registers[index] = value;
        for (const auto& [at, inst] : run)
            simulator.run(*inst);
        return simulator.failed ? std::nullopt : simulator.registers[target->index];
    };
    const unsigned registers = arm ? 31 : 16, stack = arm ? 31 : 4;
    for (unsigned index = 0; index < registers; ++index) {
        if (index == stack || index == target->index)
            continue;
        TableSimulator first(instructions, image, regions, runStart), second(instructions, image, regions, runStart);
        if (!simulate(index, 0, first) || !simulate(index, 1, second))
            continue;
        // The table read that moves by its own width.
        std::optional<std::pair<std::size_t, std::size_t>> table;
        for (const auto& [at, size] : first.reads)
            if ((size == 1 || size == 2 || size == 4 || size == 8) && second.reads.contains({at + size, size}))
                table = std::pair{at, size};
        if (!table)
            continue;
        const auto [start, width] = *table;
        const auto next = unguarded.boundaries.upper_bound(Address(start));
        const auto limit = std::min<std::size_t>(1024,
            next == unguarded.boundaries.end() ? 1024 : std::size_t(*next - Address(start)) / width);
        std::set<Address> destinations;
        std::size_t count = 0;
        for (; count < limit; ++count) {
            TableSimulator simulator(instructions, image, regions, runStart);
            const auto destination = simulate(index, count, simulator);
            if (!destination || *destination >= image.size() ||
                std::size_t(*destination) >= executableEnd(*destination, image.size(), regions) ||
                (arm && *destination % 4) || Address(*destination) < unguarded.functionStart ||
                Address(*destination) >= unguarded.functionEnd ||
                (*destination >= start && *destination < start + limit * width))
                break;
            destinations.insert(Address(*destination));
        }
        if (destinations.size() < 2)
            continue;
        jump.destinations.assign(destinations.begin(), destinations.end());
        references.tables.push_back({start, count * width});
        return;
    }
}

std::optional<std::size_t> rvaTableBound(const std::map<Address, Instruction>& instructions,
    std::map<Address, Instruction>::const_iterator entry, unsigned base, unsigned index) {
    for (unsigned skipped = 0; entry != instructions.begin() && skipped < 2; ++skipped) {
        const auto before = std::prev(entry);
        if (before->second.next != entry->first || before->second.end)
            break;
        if (const auto* origin = std::get_if<Move>(&before->second.effect); origin && origin->dst == base && origin->size == 8) {
            // The base register holds the image base, which MSVC loads as __ImageBase.
            const auto* value = std::get_if<EffectiveAddress>(&origin->src);
            if (!value || value->base != Zero || value->index != Zero)
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
    const auto limit = check ? compareLimit(instructions, compare->first, *check) : std::nullopt;
    if (compare->second.next == branch->first && limit && check->flags && check->op == BinaryOp::Sub &&
        check->dst == Zero && check->lhs == index && *limit < 4096)
        return *limit + 1;
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
    // Tables hold RVAs, and the base register holds the image base the code adds to them.
    const auto imageBase = resolveRegister(instructions, load->first, address.base).value_or(0);
    if (imageBase < 0)
        return;
    const auto table = std::size_t(imageBase + address.displacement);
    recordJumpTable(jump, image, regions, references, table, 4, 256, false, imageBase);
    if (!jump.destinations.empty() || load == instructions.begin())
        return;

    if (const auto bound = rvaTableBound(instructions, load, address.base, address.index)) {
        recordJumpTable(jump, image, regions, references, table, 4, *bound, true, imageBase, 1, false, true);
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
        if (table >= image.size())
            return;
        auto first = table;
        for (unsigned i = 0; i < 128 && first >= 4 && executableEnd(first - 4, image.size(), regions); ++i) {
            Reader prior{image, Address(first - 4), true};
            const auto destination = imageBase + Address(prior.read(4));
            if (destination < Address(table) - 65536 || destination >= Address(table) ||
                std::size_t(destination) >= executableEnd(destination, image.size(), regions))
                break;
            first -= 4;
        }
        recordJumpTable(jump, image, regions, references, first, 4, (table - first) / 4 + 128, false, imageBase, 1,
            false, true);
        return;
    }
    if (remap->second.next == load->first) {
        const auto* origin = std::get_if<Move>(&remap->second.effect);
        const auto* relative = origin ? std::get_if<EffectiveAddress>(&origin->src) : nullptr;
        if (relative && relative->base == Zero && relative->index == Zero && origin->size == 8 &&
            origin->dst == address.base) {
            recordJumpTable(jump, image, regions, references, table, 4, 256, false, imageBase, 1, false, true);
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
    const auto indices = std::size_t(imageBase + indexes->address.displacement);
    const auto length = *bound;
    const auto offsets = table;
    if (!isImageData(indices, length))
        return;
    const auto count = std::size_t(std::ranges::max(image.subspan(indices, length))) + 1;
    if (!isImageData(offsets, count * 4) || (offsets < indices + length && indices < offsets + count * 4))
        return;
    std::set<Address> destinations;
    for (const auto offset : image.subspan(indices, length)) {
        Reader item{image, Address(offsets + offset * 4), true};
        const auto targetPc = std::size_t(imageBase + Address(item.read(4)));
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
        if (!write || *write == target->index || inst->end || !inst->after.empty())
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
        if (!write || !inst->after.empty() || *write == at.index)
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

// The page an ARM64 ADRP left in `reg` before `pc`, searching back along the fallthrough path. Code reuses a page
// long after its ADRP, past calls when the register is callee-saved.
std::optional<Address> adrpPage(const Instructions& instructions, Address pc, unsigned reg) {
    auto cursor = pc;
    for (unsigned steps = 0; steps < 64; ++steps) {
        const auto* inst = previousInstruction(instructions, cursor);
        if (!inst)
            return std::nullopt;
        if (inst->end && (std::holds_alternative<Jump>(*inst->end) || std::holds_alternative<Return>(*inst->end) ||
            std::holds_alternative<Trap>(*inst->end) || (std::holds_alternative<Call>(*inst->end) && (reg < 19 || reg > 28))))
            return std::nullopt;
        if (std::ranges::any_of(inst->after, [&](const Effect& effect) { return writesRegister(effect, reg); }))
            return std::nullopt;
        if (writesRegister(inst->effect, reg)) {
            const auto* move = std::get_if<Move>(&inst->effect);
            const auto* page = move && move->size == 8 && move->dst == reg ? std::get_if<Immediate>(&move->src) : nullptr;
            if (page && page->value % 4096 == 0)
                return Address(page->value);
            return std::nullopt;
        }
    }
    return std::nullopt;
}

// Whether the x86-64 function at `entry` loads its own return address before it moves RSP, as setjmp does
// (MSVC's static _setjmp, glibc's __sigsetjmp, musl's setjmp). longjmp later resumes the caller there.
bool readsReturnAddress(const std::map<Address, Instruction>& instructions, Address entry) {
    auto pc = entry;
    for (unsigned count = 0; count < 32; ++count) {
        const auto found = instructions.find(pc);
        if (found == instructions.end())
            return false;
        const auto& instruction = found->second;
        if (const auto* move = std::get_if<Move>(&instruction.effect); move && move->size == 8)
            if (const auto* memory = std::get_if<Memory>(&move->src); memory && memory->address == EffectiveAddress{4, 0})
                return true;
        if (writesRegister(instruction.effect, 4) ||
            std::ranges::any_of(instruction.after, [](const Effect& effect) { return writesRegister(effect, 4); }))
            return false;
        // An entry such as glibc's _setjmp may jump to the implementation that reads it.
        if (instruction.end) {
            const auto* jump = std::get_if<Jump>(&*instruction.end);
            const auto* target = jump && jump->destinations.empty() ? std::get_if<Immediate>(&jump->target) : nullptr;
            if (!target)
                return false;
            pc = Address(target->value);
            continue;
        }
        pc = instruction.next;
    }
    return false;
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
    CallingConvention convention, std::optional<std::size_t> tlsVector, std::size_t threadBlock,
    std::span<const std::pair<std::size_t, std::size_t>> functionRanges) {
    std::map<Address, Instruction> instructions;
    BranchIndex branches;
    std::set<Address> functionEntries;
    // Entries known only from addresses code takes; a direct call or an export makes one a function.
    std::set<Address> takenEntries;
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
    const auto recoverTable = [&](Address pc, Jump& jump, const std::set<Address>* boundaries = nullptr) {
        if (!references || !jump.destinations.empty() || !std::holds_alternative<Register>(jump.target))
            return;
        const bool arm = architecture == Architecture::Arm64;
        if (boundaries) {
            // The last resort, once every other table and reference is known. The function spans the entries
            // around the jump, past labels whose address the code only takes.
            auto after = functionEntries.upper_bound(pc);
            while (after != functionEntries.end() && takenEntries.contains(*after))
                ++after;
            auto before = functionEntries.upper_bound(pc);
            while (before != functionEntries.begin() && takenEntries.contains(*std::prev(before)))
                --before;
            const auto start = before == functionEntries.begin() ? Address(0) : *std::prev(before);
            Unguarded unguarded{*boundaries, start,
                after == functionEntries.end() ? Address(executableEnd(pc, image.size(), regions)) : *after};
            // An address taken inside a function may be a switch label or a computed goto.
            // Prefer the executable's function extent when it covers this dispatch.
            const auto range = std::ranges::upper_bound(functionRanges, std::size_t(pc), {},
                &std::pair<std::size_t, std::size_t>::first);
            if (range != functionRanges.begin() && std::size_t(pc) < std::prev(range)->second) {
                unguarded.functionStart = Address(std::prev(range)->first);
                unguarded.functionEnd = Address(std::prev(range)->second);
            }
            if (arm)
                recoverHoistedArmTable(pc, jump, instructions, branches, image, regions, *references, &unguarded);
            else
                recoverHoistedX64Table(pc, jump, instructions, branches, image, regions, *references, &unguarded);
            if (jump.destinations.empty())
                recoverUnguardedSimulatedTable(pc, jump, instructions, image, regions, *references, unguarded, arm);
        } else if (arm) {
            recoverArmTable(pc, jump, instructions, image, regions, *references);
            if (jump.destinations.empty())
                recoverHoistedArmTable(pc, jump, instructions, branches, image, regions, *references);
        } else {
            if (convention == CallingConvention::Microsoft)
                recoverRvaTable(pc, jump, instructions, image, regions, *references);
            if (jump.destinations.empty())
                recoverRelativeX64Table(pc, jump, instructions, image, regions, *references);
            if (jump.destinations.empty())
                recoverHoistedX64Table(pc, jump, instructions, branches, image, regions, *references);
        }
        if (jump.destinations.empty())
            recoverSimulatedTable(pc, jump, instructions, branches, image, regions, *references, arm);
        if (const auto* debug = std::getenv("LUFT_DEBUG_JUMP"); debug && std::strtoll(debug, nullptr, 0) == pc) {
            const auto* target = std::get_if<Register>(&jump.target);
            std::fprintf(stderr, "Luft: jump at %#llx resolved %zu destinations\n", (unsigned long long)pc,
                jump.destinations.size());
            for (const auto destination : jump.destinations)
                std::fprintf(stderr, "Luft:   -> %#llx\n", (unsigned long long)destination);
            for (unsigned reg = 0; target && reg < 16; ++reg)
                if (const auto value = resolveRegister(instructions, pc, reg))
                    std::fprintf(stderr, "Luft:   r%u = %#llx before the jump\n", reg, (unsigned long long)*value);
        }
    };

    if (exports.empty())
        addEntry(0);
    for (const auto& entry : exports) {
        addEntry(entry.offset);
        functionEntries.insert(entry.offset);
    }
    if (references)
        for (const auto target : references->functions) {
            addEntry(target);
            functionEntries.insert(target);
            if (references->taken.contains(target))
                takenEntries.insert(target);
        }

    // On Linux the thread block is the thread pointer that x86-64 FS and ARM64 TPIDR_EL0 hold.
    const Address threadPointer = convention != CallingConvention::Microsoft ? Address(threadBlock) : 0;
    GapDecoder gaps{[&](Address pc) -> std::optional<Instruction> {
        const auto end = pc < 0 ? 0 : executableEnd(pc, image.size(), regions);
        if (pc < 0 || pc >= Address(end))
            return std::nullopt;
        Reader reader{image.first(end), pc, !regions.empty(), threadPointer};
        try {
            auto instruction = architecture == Architecture::Arm64 ? decodeArm(reader) : decodeX64(reader);
            instruction.next = reader.pc;
            return instruction;
        } catch (const std::runtime_error&) {
            return std::nullopt;
        }
    }, {}};
    gaps.edges = &branches;
    gaps.functions = &functionEntries;
    gaps.taken = &takenEntries;
    gaps.stack = architecture == Architecture::Arm64 ? 31 : 4;
    gaps.noReturnSlots = references ? &references->noReturnSlots : nullptr;
    if (architecture == Architecture::Arm64)
        gaps.preserved = {19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29};
    else if (convention == CallingConvention::Microsoft)
        gaps.preserved = {3, 5, 6, 7, 12, 13, 14, 15};
    else
        gaps.preserved = {3, 5, 12, 13, 14, 15};
    struct GapScope {
        GapDecoder* previous;
        explicit GapScope(GapDecoder& gaps) : previous(gapDecoder) { gapDecoder = &gaps; }
        ~GapScope() { gapDecoder = previous; }
    } gapScope{gaps};

    constexpr unsigned maxBlockInstructions = 64;
    // Jump tables found after the first pass can expose more code, so lifting repeats until no table resolves.
    std::size_t lifted = 0;
    for (bool retry = true; retry;) {
    for (std::size_t i = lifted; i < pending.size(); ++i) {
        auto pc = pending[i];
        for (unsigned count = 0; count < maxBlockInstructions; ++count) {
            if (instructions.contains(pc)) {
                addEntry(pc);
                break;
            }

            const auto end = pc < 0 ? 0 : executableEnd(pc, image.size(), regions);
            Reader reader{image.first(end), pc, !regions.empty(), threadPointer};
            Instruction instruction;
            try {
                if (pc < 0 || pc >= Address(end))
                    throw std::runtime_error(regions.empty() ? "guest address is outside the image"
                                                            : "guest address is outside executable segments");
                instruction = architecture == Architecture::Arm64 ? decodeArm(reader) : decodeX64(reader);
                if (auto* move = std::get_if<Move>(&instruction.effect);
                    move && std::holds_alternative<ThreadLocalStorage>(move->src)) {
                    const auto offset = std::get<ThreadLocalStorage>(move->src).offset;
                    if (convention != CallingConvention::Microsoft)
                        throw std::runtime_error("Windows thread environment block is unavailable");
                    if (threadBlock) {
                        move->src = Memory{EffectiveAddress{Zero, Address(threadBlock) + offset}};
                        instruction.addressTaken = Address(threadBlock);
                    } else if (offset == 0x58 && tlsVector) {
                        move->src = EffectiveAddress{Zero, Address(*tlsVector)};
                        instruction.addressTaken = *tlsVector;
                    } else {
                        throw std::runtime_error("Windows thread environment block is unavailable");
                    }
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
                if (references && instruction.end)
                    if (auto* jump = std::get_if<Jump>(&*instruction.end))
                        recoverTable(pc, *jump);
                // ADRP and ADD form code addresses, such as callbacks passed to qsort, even far apart.
                if (architecture == Architecture::Arm64 && !regions.empty() && !instruction.addressTaken)
                    if (const auto* add = std::get_if<Binary>(&instruction.effect); add && add->op == BinaryOp::Add &&
                        add->size == 8 && !add->flags && !add->count && !add->extendBits && !add->invert &&
                        !add->withCarry && add->lhs < 31)
                        if (const auto* offset = std::get_if<Immediate>(&add->rhs); offset && offset->value < 4096)
                            if (const auto page = adrpPage(instructions, pc, add->lhs))
                                instruction.addressTaken = *page + Address(offset->value);
                // A return through a register holding a code address is a jump; libunwind pops ARM guarded
                // control stack entries with `adr x16, next; ret x16`.
                if (architecture == Architecture::Arm64 && instruction.end)
                    if (const auto* ret = std::get_if<Return>(&*instruction.end))
                        if (const auto* target = std::get_if<Register>(&ret->target); target && target->index != 30)
                            if (const auto value = resolveRegister(instructions, pc, target->index); value &&
                                *value >= 0 && std::size_t(*value) < executableEnd(*value, image.size(), regions))
                                instruction.end = Jump{immediate(*value)};
            } catch (const std::runtime_error& error) {
                instruction.end = Trap{std::format("{} at guest offset {}", error.what(), pc)};
            }
            if (code && pc >= 0 && std::size_t(pc) < end)
                code->push_back({std::size_t(pc), std::size_t(reader.pc > pc ? reader.pc : pc + 1)});
            instruction.next = reader.pc;
            const auto& decoded = instructions.emplace(pc, std::move(instruction)).first->second;
            if (const auto* branch = decoded.end ? std::get_if<Branch>(&*decoded.end) : nullptr) {
                branches[branch->taken].push_back(pc);
                if (branch->other != branch->taken)
                    branches[branch->other].push_back(pc);
            } else if (const auto* jump = decoded.end ? std::get_if<Jump>(&*decoded.end) : nullptr) {
                if (const auto* target = std::get_if<Immediate>(&jump->target))
                    branches[Address(target->value)].push_back(pc);
                for (const auto destination : jump->destinations)
                    branches[destination].push_back(pc);
            } else if (const auto* call = decoded.end ? std::get_if<Call>(&*decoded.end) : nullptr) {
                if (const auto* target = std::get_if<Immediate>(&call->target)) {
                    functionEntries.insert(Address(target->value));
                    takenEntries.erase(Address(target->value));
                    if (references)
                        references->taken.erase(Address(target->value));
                }
            }
            if (decoded.addressTaken && functionEntries.insert(*decoded.addressTaken).second) {
                takenEntries.insert(*decoded.addressTaken);
                if (references && !references->functions.contains(*decoded.addressTaken))
                    references->taken.insert(*decoded.addressTaken);
            }
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
    lifted = pending.size();
    retry = false;
    if (references) {
        for (auto& [pc, instruction] : instructions) {
            auto* jump = instruction.end ? std::get_if<Jump>(&*instruction.end) : nullptr;
            if (!jump || !jump->destinations.empty())
                continue;
            recoverTable(pc, *jump);
            for (const auto destination : jump->destinations) {
                addEntry(destination);
                branches[destination].push_back(pc);
            }
            retry |= !jump->destinations.empty();
        }
        if (!retry) {
            // Function entries bound tables among the code, and the addresses code takes there.
            std::set<Address> boundaries(references->data.begin(), references->data.end());
            boundaries.insert(functionEntries.begin(), functionEntries.end());
            for (const auto& table : references->tables)
                boundaries.insert(Address(table.start));
            for (auto& [pc, instruction] : instructions) {
                auto* jump = instruction.end ? std::get_if<Jump>(&*instruction.end) : nullptr;
                if (!jump || !jump->destinations.empty())
                    continue;
                recoverTable(pc, *jump, &boundaries);
                for (const auto destination : jump->destinations) {
                    addEntry(destination);
                    branches[destination].push_back(pc);
                }
                retry |= !jump->destinations.empty();
            }
        }
        // longjmp resumes the callers of setjmp-like functions at their return addresses, which therefore
        // become routines of their own.
        if (architecture == Architecture::X86_64) {
            std::map<Address, bool> setjmpLike;
            for (const auto& [pc, instruction] : instructions) {
                const auto* call = instruction.end ? std::get_if<Call>(&*instruction.end) : nullptr;
                const auto* target = call ? std::get_if<Immediate>(&call->target) : nullptr;
                if (!target || references->functions.contains(call->resume))
                    continue;
                auto [known, inserted] = setjmpLike.try_emplace(Address(target->value));
                if (inserted)
                    known->second = readsReturnAddress(instructions, known->first);
                if (!known->second)
                    continue;
                references->functions.insert(call->resume);
                functionEntries.insert(call->resume);
                takenEntries.erase(call->resume);
                references->taken.erase(call->resume);
                addEntry(call->resume);
                retry = true;
            }
        }
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
            block.effects.insert(block.effects.end(), instruction.after.begin(), instruction.after.end());
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
