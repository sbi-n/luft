#include "lower.h"
#include "ir/analysis.h"

#include <array>
#include <bitset>
#include <format>

namespace luau {
using namespace ir;
namespace {
constexpr unsigned MaxOperations = 40;

struct LocalWord {
    std::string lo = "0";
    std::string hi = "0";
    std::optional<std::uint64_t> constant = 0;
    unsigned arguments = 0;
    std::bitset<MaxOperations> dependencies{};
};

LocalWord literal(std::uint64_t value) {
    return {std::to_string(std::uint32_t(value)), std::to_string(value >> 32), value};
}

LocalWord narrow(LocalWord value, unsigned size) {
    if (size == 8)
        return value;
    if (value.constant)
        return literal(std::uint32_t(*value.constant));
    value.hi = "0";
    return value;
}

}

std::optional<std::string> lowerDirect(const Graph& graph, Address entry, bool arm, CallingConvention convention) {
    const auto argumentRegs = argumentRegisters(arm, convention);
    const auto argCount = unsigned(argumentRegs.size());
    const auto usesStack = [&](unsigned reg) { return arm ? reg == 30 || reg == 31 : reg == 4; };
    std::array<LocalWord, 33> registers{};
    std::array<std::string, MaxOperations> definitions;
    for (unsigned i = 0; i < argCount; ++i) {
        registers[argumentRegs[i]] = {
            std::format("(arg{0} and arg{0}.lo or 0)", i + 1),
            std::format("(arg{0} and arg{0}.hi or 0)", i + 1), std::nullopt, 1u << i
        };
    }

    const auto value = [&](const Value& input) -> std::optional<LocalWord> {
        if (const auto* reg = std::get_if<Register>(&input); reg && !usesStack(reg->index))
            return registers[reg->index];
        if (const auto* imm = std::get_if<Immediate>(&input))
            return literal(imm->value);
        return std::nullopt;
    };

    std::set<Address> visited;
    unsigned operation = 0;
    for (auto pc = entry; visited.size() < 16 && visited.insert(pc).second;) {
        const auto& block = graph.at(pc);
        for (const auto& effect : block.effects) {
            if (std::holds_alternative<Nop>(effect))
                continue;
            if (++operation > MaxOperations)
                return std::nullopt;
            if (const auto* move = std::get_if<Move>(&effect)) {
                const auto source = value(move->src);
                if (!source || usesStack(move->dst) || move->size < 4)
                    return std::nullopt;
                if (move->dst != Zero)
                    registers[move->dst] = narrow(*source, move->size);
                continue;
            }
            const auto* binary = std::get_if<Binary>(&effect);
            if (!binary || binary->count != 0 || binary->invert || binary->extendBits || binary->withCarry ||
                usesStack(binary->dst) || usesStack(binary->lhs))
                return std::nullopt;
            const auto rhs = value(binary->rhs);
            if (!rhs)
                return std::nullopt;
            if (binary->dst == Zero)
                continue;
            // This path accepts no conditional edges, so flags have no consumers.
            const auto lhs = registers[binary->lhs];
            if (lhs.constant && rhs->constant) {
                registers[binary->dst] = narrow(literal(fold(binary->op, *lhs.constant, *rhs->constant)), binary->size);
                continue;
            }
            if ((binary->op == BinaryOp::Xor || binary->op == BinaryOp::Sub) &&
                lhs.lo == rhs->lo && (binary->size == 4 || lhs.hi == rhs->hi)) {
                registers[binary->dst] = literal(0);
                continue;
            }

            const auto name = "v" + std::to_string(operation);
            const auto lo = name + "lo";
            const auto hi = name + "hi";
            auto& body = definitions[operation - 1];
            if (binary->op == BinaryOp::Add || binary->op == BinaryOp::Sub) {
                const char op = binary->op == BinaryOp::Add ? '+' : '-';
                body += std::format("    local {0}sum = {1} {2} {3}\n    local {0}lo = {0}sum % 4294967296\n",
                    name, lhs.lo, op, rhs->lo);
                if (binary->size == 8)
                    body += std::format("    local {0}hi = ({1} {2} {3} + math.floor({0}sum / 4294967296)) % 4294967296\n",
                        name, lhs.hi, op, rhs->hi);
            } else {
                const auto op = bitOperation(binary->op);
                body += std::format("    local {} = bit32.{}({}, {})\n", lo, op, lhs.lo, rhs->lo);
                if (binary->size == 8)
                    body += std::format("    local {} = bit32.{}({}, {})\n", hi, op, lhs.hi, rhs->hi);
            }
            auto dependencies = lhs.dependencies | rhs->dependencies;
            dependencies.set(operation - 1);
            registers[binary->dst] = {lo, binary->size == 8 ? hi : "0", std::nullopt,
                lhs.arguments | rhs->arguments, dependencies};
        }

        if (const auto* ret = std::get_if<Return>(&block.end)) {
            const auto* link = std::get_if<Register>(&ret->target);
            if (arm ? !link || link->index != 30 : !std::holds_alternative<StackTop>(ret->target))
                return std::nullopt;
            const auto& result = registers[0];
            auto output = std::format("    {}readArguments({}, ...)\n",
                result.arguments ? "local args = " : "", argCount);
            for (unsigned i = 0; i < argCount; ++i)
                if (result.arguments & (1u << i))
                    output += std::format("    local arg{} = args[{}]\n", i + 1, i + 1);
            for (unsigned i = 0; i < operation; ++i)
                if (result.dependencies.test(i))
                    output += definitions[i];
            output += std::format("    return {{lo = {}, hi = {}}}\n", result.lo, result.hi);
            return output;
        }
        const auto* jump = std::get_if<Jump>(&block.end);
        const auto* target = jump ? std::get_if<Immediate>(&jump->target) : nullptr;
        if (!target)
            return std::nullopt;
        pc = Address(target->value);
    }

    return std::nullopt;
}
}
