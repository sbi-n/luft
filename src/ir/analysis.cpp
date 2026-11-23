#include "analysis.h"

#include <algorithm>
#include <ranges>
#include <stdexcept>

namespace ir {
namespace {
template<class... Ts>
struct Visit : Ts... { using Ts::operator()...; };
}

std::uint64_t fold(BinaryOp op, std::uint64_t lhs, std::uint64_t rhs) {
    switch (op) {
        case BinaryOp::Add: return lhs + rhs;
        case BinaryOp::Sub: return lhs - rhs;
        case BinaryOp::And: return lhs & rhs;
        case BinaryOp::Or: return lhs | rhs;
        case BinaryOp::Xor: return lhs ^ rhs;
    }
    throw std::logic_error("unknown binary IR operation");
}

std::optional<Address> jumpTarget(const Block& block) {
    if (const auto* jump = std::get_if<Jump>(&block.end))
        if (const auto* target = std::get_if<Immediate>(&jump->target))
            return Address(target->value);
    return {};
}

LoopExits recoverLoops(const Graph& graph) {
    std::map<Address, std::vector<Address>> forward, backward;
    for (const auto& [pc, block] : graph) {
        auto& edges = forward[pc];
        visitEdges(block, [&](Address target) { edges.push_back(target); });
        if (const auto* call = std::get_if<Call>(&block.end))
            edges.push_back(call->resume);
        for (const auto target : edges)
            backward[target].push_back(pc);
    }
    const auto components = [&](const std::set<Address>& scope) {
        std::vector<Address> finished;
        std::set<Address> seen;
        for (const auto pc : scope) {
            if (!seen.insert(pc).second)
                continue;
            std::vector<std::pair<Address, std::size_t>> work{{pc, 0}};
            while (!work.empty()) {
                auto& [node, next] = work.back();
                if (const auto& edges = forward[node]; next < edges.size()) {
                    const auto target = edges[next++];
                    if (scope.contains(target) && seen.insert(target).second)
                        work.emplace_back(target, 0);
                } else {
                    finished.push_back(node);
                    work.pop_back();
                }
            }
        }
        seen.clear();
        std::vector<std::set<Address>> result;
        for (const auto pc : finished | std::views::reverse) {
            if (!seen.insert(pc).second)
                continue;
            std::vector<Address> work{pc};
            for (std::size_t i = 0; i < work.size(); ++i)
                for (const auto target : backward[work[i]])
                    if (scope.contains(target) && seen.insert(target).second)
                        work.push_back(target);
            if (work.size() >= 2)
                result.emplace_back(work.begin(), work.end());
        }
        return result;
    };

    LoopExits loops;
    const auto canonicalExit = [&](Address address) {
        std::set<Address> path;
        while (path.insert(address).second) {
            const auto& block = graph.at(address);
            const auto next = jumpTarget(block);
            if (!next || !std::ranges::all_of(block.effects, [](const Effect& effect) {
                return std::holds_alternative<Nop>(effect);
            }))
                break;
            address = *next;
        }
        return address;
    };
    std::set<Address> all;
    for (const auto& [pc, block] : graph)
        all.insert(pc);
    auto pending = components(all);
    while (!pending.empty()) {
        auto component = std::move(pending.back());
        pending.pop_back();
        if (component.size() > 16)
            continue;
        std::set<Address> entries, exits;
        for (const auto node : component) {
            for (const auto predecessor : backward[node])
                if (!component.contains(predecessor))
                    entries.insert(node);
            for (const auto target : forward[node])
                if (!component.contains(target))
                    exits.insert(canonicalExit(target));
        }
        if (entries.size() != 1 || exits.empty() || exits.size() > 4)
            continue;
        const auto header = *entries.begin();
        loops.emplace(header, std::vector<Address>(exits.begin(), exits.end()));
        // Removing a natural loop's header exposes the loops nested inside it.
        component.erase(header);
        for (auto& child : components(component))
            pending.push_back(std::move(child));
    }
    return loops;
}

bool observesExitFlags(const Block& block, bool calls) {
    const auto* branch = std::get_if<Branch>(&block.end);
    if (branch && std::holds_alternative<FlagsCondition>(branch->condition))
        return true;
    const auto* jump = std::get_if<Jump>(&block.end);
    const bool indirect = jump && !std::holds_alternative<Immediate>(jump->target) && jump->destinations.empty();
    return indirect || (calls && (std::holds_alternative<Call>(block.end) || std::holds_alternative<Return>(block.end)));
}

bool writesFlags(const Effect& effect) {
    const auto* binary = std::get_if<Binary>(&effect);
    const auto* multiply = std::get_if<Multiply>(&effect);
    const auto* shift = std::get_if<ShiftRegister>(&effect);
    const auto* memory = std::get_if<MemoryBinary>(&effect);
    const auto* exchange = std::get_if<Exchange>(&effect);
    const auto* scan = std::get_if<BitScan>(&effect);
    return (binary && binary->flags) || (multiply && multiply->flags) ||
        (shift && shift->flags) || (exchange && exchange->add) ||
        std::holds_alternative<ByteBinary>(effect) || std::holds_alternative<ByteShift>(effect) ||
        std::holds_alternative<Shift>(effect) ||
        (memory && memory->flags) || std::holds_alternative<FloatCompare>(effect) ||
        std::holds_alternative<ConditionalCompare>(effect) || std::holds_alternative<BitTest>(effect) ||
        (scan && !scan->leadingCount);
}

bool readsFlags(const Effect& effect) {
    const auto* binary = std::get_if<MemoryBinary>(&effect);
    const auto* byte = std::get_if<ByteBinary>(&effect);
    const auto* shift = std::get_if<ShiftRegister>(&effect);
    const auto* immediateShift = std::get_if<Shift>(&effect);
    const auto* registerBinary = std::get_if<Binary>(&effect);
    return std::holds_alternative<ConditionalMove>(effect) || std::holds_alternative<SetCondition>(effect) ||
        std::holds_alternative<Select>(effect) || std::holds_alternative<ConditionalCompare>(effect) ||
        (binary && (binary->keepCarry || binary->withCarry)) || (byte && byte->keepCarry) || (shift && shift->flags) ||
        std::holds_alternative<ByteShift>(effect) ||
        (immediateShift && immediateShift->op >= ShiftOp::RotateRight) ||
        (registerBinary && registerBinary->withCarry) || std::holds_alternative<BitTest>(effect);
}

bool overwritesFlags(const Effect& effect) {
    const auto* binary = std::get_if<Binary>(&effect);
    const auto* memory = std::get_if<MemoryBinary>(&effect);
    const auto* byte = std::get_if<ByteBinary>(&effect);
    const auto* exchange = std::get_if<Exchange>(&effect);
    return (binary && binary->flags) || (memory && memory->flags && !memory->keepCarry) ||
        (byte && !byte->keepCarry) || (exchange && exchange->add) ||
        std::holds_alternative<FloatCompare>(effect) || std::holds_alternative<ConditionalCompare>(effect);
}

static bool readsIncomingFlags(const Block& block, bool calls) {
    for (const auto& effect : block.effects) {
        if (readsFlags(effect))
            return true;
        if (overwritesFlags(effect))
            return false;
    }
    return observesExitFlags(block, calls);
}

std::set<Address> liveFlagsAtEntry(const Graph& graph, bool calls) {
    std::set<Address> live;
    std::set<Address> writes;
    std::map<Address, std::vector<Address>> predecessors;
    std::vector<Address> work;
    const auto mark = [&](Address pc) {
        if (!writes.contains(pc) && live.insert(pc).second)
            work.push_back(pc);
    };
    for (const auto& [pc, block] : graph) {
        if (std::ranges::any_of(block.effects, overwritesFlags))
            writes.insert(pc);
        if (readsIncomingFlags(block, calls) && live.insert(pc).second)
            work.push_back(pc);
        visitEdges(block, [&](Address target) { predecessors[target].push_back(pc); });
    }
    for (std::size_t i = 0; i < work.size(); ++i)
        for (const auto predecessor : predecessors[work[i]])
            mark(predecessor);
    return live;
}

std::optional<std::uint64_t> knownAddress(const EffectiveAddress& address, const Constants& constants) {
    const auto base = address.base == Zero ? std::optional<std::uint64_t>(0) : constants[address.base];
    auto index = address.index == Zero ? std::optional<std::uint64_t>(0) : constants[address.index];
    if (index && address.indexWidth != IndexWidth::Full) {
        *index = std::uint32_t(*index);
        if (address.indexWidth == IndexWidth::Signed32 && *index >= 0x80000000)
            *index |= 0xffffffff00000000;
    }
    if (base && index)
        return *base + *index * address.scale + address.displacement;
    return {};
}

static bool touchesStack(const Effect& effect, unsigned sp) {
    const auto stackAddress = [sp](const EffectiveAddress& addr) {
        return addr.base == sp || addr.index == sp;
    };
    const auto value = [&](const Value& source) {
        return std::visit(Visit{
            [sp](const Register& r) { return r.index == sp; },
            stackAddress,
            [&](const Memory& m) { return stackAddress(m.address); },
            [](const StackTop&) { return true; },
            [](const StackGuard&) { return false; },
            [](const ThreadLocalStorage&) { return false; },
            [](const Immediate&) { return false; },
        }, source);
    };
    const auto xmm = [&](const VectorOperand& operand) {
        const auto* mem = std::get_if<VectorMemory>(&operand);
        return mem && stackAddress(mem->address);
    };
    return std::visit(Visit{
        [](const Nop&) { return false; },
        [&](const Move& m) { return m.dst == sp || value(m.src); },
        [&](const ByteMove& m) { return value(m.dst) || value(m.src); },
        [&](const Exchange& m) { return value(m.dst) || m.src.index == sp; },
        [&](const AtomicAdd& op) { return stackAddress(op.address); },
        [&](const Extend& ext) { return ext.dst == sp || value(ext.src); },
        [&](const ConditionalMove& m) { return m.dst == sp || value(m.src); },
        [sp](const Select& m) { return m.dst == sp || m.yes.index == sp || m.no.index == sp; },
        [&](const ConditionalCompare& c) { return c.lhs.index == sp || value(c.rhs); },
        [&](const Divide& div) { return value(div.divisor); },
        [sp](const DivideWord& div) { return div.dst == sp || div.lhs.index == sp || div.rhs.index == sp; },
        [&](const Multiply& mul) { return mul.dst == sp || mul.accumulator == sp || value(mul.lhs) || value(mul.rhs); },
        [&](const SetCondition& set) { return value(set.dst); },
        [&](const Binary& a) { return a.dst == sp || a.lhs == sp || value(a.rhs); },
        [&](const MemoryBinary& a) { return value(a.dst) || value(a.rhs); },
        [&](const Store& s) { return stackAddress(s.address) || value(s.src); },
        [&](const PairTransfer& p) { return stackAddress(p.address); },
        [](const Push&) { return true; },
        [sp](const KeepBits& k) { return k.dst == sp; },
        [&](const ByteBinary& c) { return value(c.lhs) || value(c.rhs); },
        [&](const ByteShift& s) { return value(s.dst); },
        [sp](const Shift& shift) { return shift.dst.index == sp; },
        [sp](const ShiftRegister& shift) { return shift.dst == sp || shift.src.index == sp || shift.count.index == sp; },
        [sp](const Bitfield& field) { return field.dst == sp || field.src.index == sp; },
        [&](const BitTest& op) { return value(op.target) || value(op.index); },
        [&](const BitScan& op) { return op.dst == sp || value(op.src); },
        [sp](const ByteSwap& op) { return op.dst == sp || op.src.index == sp; },
        [](const StringDirection&) { return false; },
        [](const RepeatStore&) { return true; },
        [](const CpuId&) { return false; },
        [&](const VectorBinary& b) { return xmm(b.src); },
        [&](const VectorMove& m) { return xmm(m.src) || xmm(m.dst); },
        [&](const VectorHalfMove& m) { return xmm(m.src) || xmm(m.dst); },
        [](const VectorShiftBytes&) { return false; },
        [&](const VectorIntToDouble& c) { return xmm(c.src); },
        [sp](const VectorSignMask& c) { return c.dst == sp; },
        [&](const VectorShuffleDwords& c) { return xmm(c.src); },
        [sp](const VectorTransfer& x) { return x.gp.index == sp; },
        [](const VectorImmediate&) { return false; },
        [](const VectorByteOperation&) { return false; },
        [&](const FloatBinary& a) { return xmm(a.src); },
        [&](const FloatCompare& a) { return a.rhs && xmm(*a.rhs); },
        [&](const FloatMask& a) { return xmm(a.src); },
        [&](const IntegerToFloat& c) { return value(c.src); },
        [&](const FloatToInteger& c) { return c.dst == sp || xmm(c.src); },
        [&](const FloatingControl& c) { return stackAddress(c.address); },
    }, effect);
}

Features detectFeatures(const Graph& graph, Address entry, bool arm,
    std::span<const std::size_t> initializers) {
    Features features;
    const unsigned sp = arm ? 31 : 4;
    std::set<Address> visited{entry};
    std::vector<Address> work{entry};
    const auto enqueue = [&](Address pc) {
        if (visited.insert(pc).second)
            work.push_back(pc);
    };
    if (!initializers.empty()) {
        features.calls = true;
        features.stack = true;
        for (const auto pc : initializers)
            enqueue(pc);
    }
    bool followedAddressTaken = false;
    const auto followAddressTaken = [&] {
        if (followedAddressTaken)
            return;
        followedAddressTaken = true;
        for (const auto& [pc, block] : graph)
            enqueue(pc);
    };
    for (std::size_t i = 0; i < work.size(); ++i) {
        const auto& block = graph.at(work[i]);
        for (const auto& effect : block.effects) {
            features.stack |= touchesStack(effect, sp);
            features.flags |= std::holds_alternative<Select>(effect) || std::holds_alternative<ConditionalCompare>(effect);
            if (const auto* op = std::get_if<Binary>(&effect))
                features.flags |= op->withCarry;
            if (const auto* op = std::get_if<MemoryBinary>(&effect))
                features.flags |= op->withCarry;
            if (const auto* move = std::get_if<ConditionalMove>(&effect)) {
                features.flags = true;
                features.parity |= move->condition == 10 || move->condition == 11;
            }
            if (const auto* set = std::get_if<SetCondition>(&effect)) {
                features.flags = true;
                features.parity |= set->condition == 10 || set->condition == 11;
            }
        }
        if (const auto target = jumpTarget(block)) {
            enqueue(*target);
        } else if (const auto* branch = std::get_if<Branch>(&block.end)) {
            if (const auto* flag = std::get_if<FlagsCondition>(&branch->condition)) {
                features.flags = true;
                features.parity |= !arm && (flag->code == 10 || flag->code == 11);
            }
            enqueue(branch->taken);
            enqueue(branch->other);
        } else if (const auto* call = std::get_if<Call>(&block.end)) {
            features.calls = true;
            features.stack |= !arm;
            enqueue(call->resume);
            if (const auto* target = std::get_if<Immediate>(&call->target))
                enqueue(Address(target->value));
            else
                followAddressTaken();
        } else if (std::holds_alternative<Jump>(block.end)) {
            followAddressTaken();
        }
    }
    return features;
}
}
