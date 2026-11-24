#include "lower.h"
#include "ir/analysis.h"

#include <algorithm>
#include <array>
#include <format>
#include <ranges>
#include <set>
#include <stdexcept>
#include <utility>

namespace {
using namespace ir;
using luau::argumentRegisters;
using luau::bitOperation;
using luau::Data;
using luau::quoted;

template<class... Ts>
struct Visit : Ts... { using Ts::operator()...; };

constexpr std::array<std::string_view, 16> X64Conditions{
    "overflow", "not overflow", "carry", "not carry", "zero", "not zero",
    "carry or zero", "not carry and not zero", "negative", "not negative", "parity", "not parity",
    "negative ~= overflow", "negative == overflow", "zero or negative ~= overflow", "not zero and negative == overflow"
};

constexpr std::array<std::string_view, 16> ArmConditions{
    "zero", "not zero", "carry", "not carry", "negative", "not negative", "overflow", "not overflow",
    "carry and not zero", "not carry or zero", "negative == overflow", "negative ~= overflow",
    "not zero and negative == overflow", "zero or negative ~= overflow", "true", "true"
};

std::string functionName(Address pc) {
    return pc < 0 ? std::format("bad_{:x}", std::uint64_t(pc)) : std::format("function_{:x}", pc);
}

struct LuauWord {
    std::string lo;
    std::string hi;
    std::string pair() const { return lo + ", " + hi; }
};
constexpr unsigned LocalVectorRegisters = 20;

LuauWord wordLiteral(std::uint64_t word) {
    return {std::to_string(std::uint32_t(word)), std::to_string(word >> 32)};
}

class StructuredFunction {
public:
    StructuredFunction(const Graph& graph, const std::set<Address>& addressTaken,
        const LoopExits& loops, Data& data, Address entry, bool arm, CallingConvention convention,
        std::span<const std::size_t> initializers)
        : graph(graph), addressTaken(addressTaken), data(data), entry(entry), arm(arm), convention(convention),
          initializers(initializers), loops(loops), features(detectFeatures(graph, entry, arm, initializers)),
          flagsAtEntry(features.flags ? liveFlagsAtEntry(graph, features.calls) : std::set<Address>{}),
          useRoutineTable(graph.size() > 48) {
        for (const auto& [pc, block] : graph) {
            visitEdges(block, [&](Address target) { ++predecessors[target]; });
            if (const auto* call = std::get_if<Call>(&block.end))
                ++predecessors[call->resume];
        }
    }

    std::string lower() {
        const auto result = reg(0);
        addFunction(entry);
        for (const auto pc : initializers)
            addFunction(pc);
        std::string bodies;
        for (std::size_t i = 0; i < pending.size(); ++i) {
            const auto target = pending[i];
            body = std::format("    {} = function(expectedReturn: number): GuestRoutine?\n", routine(target));
            active.clear();
            regionEntry = target;
            remaining = 256;
            region(target, 2, {});
            body += "    end\n";
            bodies += body;
        }

        const auto argumentRegs = argumentRegisters(arm, convention);
        const auto argCount = unsigned(argumentRegs.size());
        const unsigned shadowSpace = !arm && convention == CallingConvention::Microsoft ? 32 : 0;
        if (features.stack)
            reg(arm ? 31 : 4);
        if (arm && features.calls)
            reg(30);
        std::string source = std::format("    local args = readArguments({}, ...)\n", argCount);
        if (needsMemory || features.stack)
            source += std::format("    resetMemory({})\n", features.stack);
        if (usesBudget)
            source += data.regions.empty() ? "    local budget = 1000000\n" : "    local budget = 40000000\n";
        if (usesDirection)
            source += "    local direction = 1\n";
        if (usesFloatingControl)
            source += "    local mxcsr, x87Control = 0x1f80, 0x037f\n";
        if (usesExceptionFilter)
            source += "    local exceptionFilterLo, exceptionFilterHi = 0, 0\n";
        if (usesLastError)
            source += "    local lastError = 0\n";
        if (usesFiberSlots)
            source += "    local fiberSlots: {[number]: {lo: number, hi: number, callbackLo: number, callbackHi: number}?} = {}\n"
                "    local fiberNext = 0\n";
        if (needsJumpFrames)
            source += "    local jumpFrames: JumpFrames = {}\n";
        if (usesExitCallbacks)
            source += "    local exitCallbacks: {() -> ()} = {}\n";
        for (const auto index : registers) {
            const auto cell = reg(index);
            if (features.stack && index == (arm ? 31u : 4u)) {
                source += std::format("    local {}, {} = stackTop, 0\n", cell.lo, cell.hi);
            } else if (arm && index == 30) {
                source += std::format("    local {}, {} = 4294967295, 0\n", cell.lo, cell.hi);
            } else {
                unsigned incoming = 0;
                for (unsigned arg = 0; arg < argCount; ++arg)
                    if (index == argumentRegs[arg])
                        incoming = arg + 1;
                if (incoming) {
                    source += std::format("    local arg{0} = args[{0}]\n"
                        "    local {1}, {2} = if arg{0} then arg{0}.lo else 0, if arg{0} then arg{0}.hi else 0\n",
                        incoming, cell.lo, cell.hi);
                } else {
                    source += std::format("    local {}, {} = 0, 0\n", cell.lo, cell.hi);
                }
            }
        }
        if (!xmmRegisters.empty() && *xmmRegisters.rbegin() >= LocalVectorRegisters)
            source += std::format("    local vectorLanes = table.create({}, 0)\n", (32 - LocalVectorRegisters) * 4);
        for (const auto index : xmmRegisters)
            if (index < LocalVectorRegisters)
                source += std::format("    local {} = 0, 0, 0, 0\n", joinLanes(xmm(VectorRegister{index})));
        if (features.flags)
            source += "    local carry, overflow, negative, zero, parity = false, false, false, false, false\n";
        if (useRoutineTable) {
            source += "    local routines: {[string]: GuestRoutine} = {}\n";
        } else {
            for (const auto target : pending)
                source += std::format("    local {}: GuestRoutine\n", functionName(target));
        }
        if (usesFunctionPointers)
            source += "    local functionPointers: {[number]: GuestRoutine?} = {}\n";
        source += bodies;
        if (usesFunctionPointers)
            for (const auto target : addressTaken)
                source += std::format("    functionPointers[{}] = {}\n", target, routine(target));
        if (!initializers.empty()) {
            const unsigned stackRegister = arm ? 31 : 4;
            const auto sp = reg(stackRegister);
            for (const auto pc : initializers) {
                for (const auto index : argumentRegs)
                    if (registers.contains(index))
                        source += std::format("    {} = 0, 0\n", reg(index).pair());
                if (arm)
                    source += std::format("    {} = 4294967295, 0\n", reg(30).pair());
                else
                    source += std::format("    {} -= {}\n    write(8, {}, 4294967295, 0)\n", sp.lo, 8 + shadowSpace, sp.lo);
                source += std::format("    runGuestRoutine({}, 4294967295)\n", routine(pc));
                if (shadowSpace)
                    source += std::format("    {} += {}\n", sp.lo, shadowSpace);
            }
            for (const auto index : registers) {
                if (index == stackRegister)
                    continue;
                unsigned incoming = 0;
                for (unsigned arg = 0; arg < argCount; ++arg)
                    if (index == argumentRegs[arg])
                        incoming = arg + 1;
                const auto cell = reg(index);
                if (incoming) {
                    source += std::format(
                        "    {1}, {2} = if arg{0} then arg{0}.lo else 0, if arg{0} then arg{0}.hi else 0\n",
                        incoming, cell.lo, cell.hi);
                } else if (arm && index == 30) {
                    source += std::format("    {} = 4294967295, 0\n", cell.pair());
                } else {
                    source += std::format("    {} = 0, 0\n", cell.pair());
                }
            }
            if (features.flags)
                source += "    carry, overflow, negative, zero, parity = false, false, false, false, false\n";
            if (usesDirection)
                source += "    direction = 1\n";
        }
        if (features.stack && !arm) {
            const auto sp = reg(4);
            const unsigned frameSize = 8 + shadowSpace;
            source += std::format("    {} -= {}\n    write(8, {}, 4294967295, 0)\n", sp.lo, frameSize, sp.lo);
        }
        source += std::format("    runGuestRoutine({}, 4294967295)\n", routine(entry));
        if (usesExitCallbacks) {
            source += std::format("    local result = {{lo = {}, hi = {}}}\n", result.lo, result.hi);
            source += "    while #exitCallbacks > 0 do\n"
                "        local callback = table.remove(exitCallbacks)\n"
                "        if callback then callback() end\n"
                "    end\n"
                "    return result\n";
        } else {
            source += std::format("    return {{lo = {}, hi = {}}}\n", result.lo, result.hi);
        }
        return source;
    }

    bool usesMemory() const { return needsMemory || features.stack; }
    bool usesFlags() const { return features.flags || needsAddFlags; }
    bool usesStackGuard() const { return needsStackGuard; }
    bool usesHeap() const { return needsHeap; }
    bool usesShift() const { return needsShift; }
    bool usesDivision() const { return needsDivision; }
    bool usesMultiply() const { return needsMultiply; }
    bool usesFloating() const { return needsFloating; }
    bool usesPrime() const { return needsPrime; }
    bool usesDecimal() const { return needsDecimal; }
    bool usesJumpFrames() const { return needsJumpFrames; }

private:
    const Graph& graph;
    const std::set<Address>& addressTaken;
    Data& data;
    Address entry;
    bool arm;
    CallingConvention convention;
    std::span<const std::size_t> initializers;
    const LoopExits& loops;
    Features features;
    std::set<Address> flagsAtEntry;
    bool useRoutineTable;
    bool needsMemory = false;
    bool needsStackGuard = false;
    bool needsHeap = false;
    bool needsShift = false;
    bool needsDivision = false;
    bool needsMultiply = false;
    bool needsFloating = false;
    bool needsPrime = false;
    bool needsDecimal = false;
    bool needsAddFlags = false;
    bool needsJumpFrames = false;
    bool usesFunctionPointers = false;
    bool usesExitCallbacks = false;
    bool usesBudget = false;
    bool usesDirection = false;
    bool usesFloatingControl = false;
    bool usesExceptionFilter = false;
    bool usesLastError = false;
    bool usesFiberSlots = false;
    std::set<unsigned> registers;
    std::set<unsigned> xmmRegisters;
    std::set<Address> functions;
    std::vector<Address> pending;
    std::set<Address> active;
    std::map<Address, unsigned> predecessors;
    Address regionEntry = 0;
    std::vector<Address> activeLoops;
    unsigned remaining = 0;
    std::string body;

    void addFunction(Address target) {
        if (functions.insert(target).second)
            pending.push_back(target);
    }

    std::string routine(Address address) const {
        return (useRoutineTable ? "routines." : "") + functionName(address);
    }

    LuauWord reg(unsigned index) {
        if (index == Zero)
            return wordLiteral(0);
        registers.insert(index);
        return {std::format("v{}lo", index), std::format("v{}hi", index)};
    }

    LuauWord stackGuard() {
        needsStackGuard = true;
        return {"stackGuardLo", "stackGuardHi"};
    }

    using Lanes = std::array<std::string, 4>;

    Lanes xmm(VectorRegister reg) {
        xmmRegisters.insert(reg.index);
        Lanes lanes;
        for (unsigned i = 0; i < lanes.size(); ++i) {
            lanes[i] = reg.index < LocalVectorRegisters ? std::format("x{}_{}", reg.index, i)
                : std::format("vectorLanes[{}]", (reg.index - LocalVectorRegisters) * 4 + i + 1);
        }
        return lanes;
    }

    static std::string joinLanes(const Lanes& lanes) {
        return std::format("{}, {}, {}, {}", lanes[0], lanes[1], lanes[2], lanes[3]);
    }

    void line(unsigned depth, std::string_view text) {
        body.append(depth * 4, ' ');
        body += text;
        body += '\n';
    }

    void trap(unsigned depth, std::string_view message) {
        line(depth, "error(" + quoted(message) + ", 0)");
    }

    std::string addressPair(const EffectiveAddress& addr, const Constants& constants) {
        if (const auto known = knownAddress(addr, constants))
            return wordLiteral(*known).pair();
        if (addr.index != Zero) {
            if (addr.base == Zero)
                data.materializeIndexed(std::uint64_t(addr.displacement));
            else if (const auto base = constants[addr.base])
                data.materializeIndexed(*base + addr.displacement);
            needsMemory = true;
            const auto index = reg(addr.index);
            const auto high = addr.indexWidth == IndexWidth::Full ? index.hi : addr.indexWidth == IndexWidth::Signed32 ?
                "if " + index.lo + " >= 2147483648 then 4294967295 else 0" : "0";
            return std::format("indexedOffset({}, {}, {}, {}, {})", reg(addr.base).pair(), index.lo, high,
                addr.scale, addr.displacement);
        }
        if (addr.displacement == 0)
            return reg(addr.base).pair();
        needsMemory = true;
        return std::format("offset({}, {})", reg(addr.base).pair(), addr.displacement);
    }

    std::string memoryError(std::uint64_t at, unsigned size) {
        if (const auto* import = data.unresolved(at, size))
            return std::format("unresolved binary import or relocation for {} at guest address {}", import->name, at);
        return std::format("guest memory range was not resolved during translation: {}", at);
    }

    std::string read(const EffectiveAddress& addr, unsigned size, const Constants& constants) {
        if (const auto known = knownAddress(addr, constants); known && *known < data.image.size()) {
            if (const auto word = data.immutableWord(*known, size))
                return size == 8 ? wordLiteral(*word).pair() : std::to_string(std::uint32_t(*word));
            if (!data.readable(*known, size) || data.unresolved(*known, size))
                return std::format("error({}, 0)", quoted(memoryError(*known, size)));
            data.materialize(*known, size);
        }
        needsMemory = true;
        const auto expression = std::format("read({}, address({}))", size, addressPair(addr, constants));
        return size == 8 ? expression : "(" + expression + ")";
    }

    std::optional<std::string> readVector(unsigned depth, const VectorOperand& operand, const Constants& constants) {
        if (const auto* reg = std::get_if<VectorRegister>(&operand))
            return joinLanes(xmm(*reg));
        const auto& mem = std::get<VectorMemory>(operand);
        if (const auto at = knownAddress(mem.address, constants); at && *at < data.image.size()) {
            if (mem.aligned && *at % 16 != 0) {
                needsMemory = true;
                return std::format("readXmm(address({}), true)", addressPair(mem.address, constants));
            }
            if (!data.readable(*at, 16) || data.unresolved(*at, 16)) {
                trap(depth, memoryError(*at, 16));
                return std::nullopt;
            }
            if (!data.writable(*at, 16)) {
                Lanes lanes;
                for (unsigned lane = 0; lane < lanes.size(); ++lane) {
                    std::uint32_t word = 0;
                    for (unsigned byte = 0; byte < 4; ++byte)
                        word |= std::uint32_t(data.image[*at + lane * 4 + byte]) << (byte * 8);
                    lanes[lane] = std::to_string(word);
                }
                return joinLanes(lanes);
            }
            data.materialize(*at, 16);
        }
        needsMemory = true;
        return std::format("readXmm(address({}), {})", addressPair(mem.address, constants), mem.aligned);
    }

    bool prepareWrite(unsigned depth, const EffectiveAddress& addr, unsigned size, const Constants& constants) {
        if (const auto at = knownAddress(addr, constants); at && *at < data.image.size()) {
            if (!data.writable(*at, size)) {
                trap(depth, "write to read-only guest image");
                return false;
            }
            if (data.unresolved(*at, size)) {
                trap(depth, memoryError(*at, size));
                return false;
            }
            data.materialize(*at, size);
        }
        needsMemory = true;
        return true;
    }

    void vectorBinary(unsigned depth, const VectorBinary& binary, const Constants& constants) {
        const auto dst = xmm(binary.dst);
        const auto lhsLanes = binary.lhs ? xmm(*binary.lhs) : dst;
        const auto* reg = std::get_if<VectorRegister>(&binary.src);
        if (reg && reg->index == binary.lhs.value_or(binary.dst).index &&
            (binary.op == VectorOp::Xor || binary.op == VectorOp::AndNot)) {
            line(depth, joinLanes(dst) + " = 0, 0, 0, 0");
            return;
        }
        const auto rhs = reg ? xmm(*reg) : Lanes{"source0", "source1", "source2", "source3"};
        if (!reg) {
            const auto source = readVector(depth, binary.src, constants);
            if (!source)
                return;
            line(depth++, "do");
            line(depth, "local " + joinLanes(rhs) + " = " + *source);
        }
        Lanes result{dst[0], dst[1], rhs[0], rhs[1]};
        if (binary.op == VectorOp::UnpackLowDwords) {
            result = {dst[0], rhs[0], dst[1], rhs[1]};
        } else if (binary.op == VectorOp::DotUnsignedBytes) {
            for (unsigned lane = 0; lane < binary.size / 4; ++lane) {
                auto sum = dst[lane];
                for (unsigned bit = 0; bit < 32; bit += 8)
                    sum += std::format(" + bit32.extract({}, {}, 8) * bit32.extract({}, {}, 8)",
                        lhsLanes[lane], bit, rhs[lane], bit);
                result[lane] = "(" + sum + ") % 4294967296";
            }
        } else if (binary.op == VectorOp::AccumulatePairs) {
            for (unsigned lane = 0; lane < 4; lane += 2) {
                const auto sum = std::format("({} + {} + {})", dst[lane], rhs[lane], rhs[lane + 1]);
                result[lane] = sum + " % 4294967296";
                result[lane + 1] = std::format("({} + math.floor({} / 4294967296)) % 4294967296", dst[lane + 1], sum);
            }
        } else if (binary.op == VectorOp::AddQwords || binary.op == VectorOp::SubQwords || binary.op == VectorOp::SumQwords) {
            const auto op = binary.op == VectorOp::SubQwords ? '-' : '+';
            const auto sum = [&](unsigned out, const Lanes& lhs, unsigned a, unsigned b) {
                const auto low = std::format("({} {} {})", lhs[a], op, rhs[b]);
                result[out] = low + " % 4294967296";
                result[out + 1] = std::format("({} {} {} + math.floor({} / 4294967296)) % 4294967296",
                    lhs[a + 1], op, rhs[b + 1], low);
            };
            if (binary.op == VectorOp::SumQwords) {
                sum(0, rhs, 0, 2);
                result[2] = result[3] = "0";
            } else {
                sum(0, lhsLanes, 0, 0);
                sum(2, lhsLanes, 2, 2);
            }
        } else if (binary.op == VectorOp::CompareZeroDwords || binary.op == VectorOp::CompareZeroQwords) {
            for (unsigned lane = 0; lane < 4; ++lane) {
                const auto condition = binary.op == VectorOp::CompareZeroDwords ? rhs[lane] + " == 0"
                    : rhs[lane] + " == 0 and " + rhs[lane ^ 1] + " == 0";
                result[lane] = "if " + condition + " then 4294967295 else 0";
            }
        } else if (binary.op == VectorOp::CompareUnsignedWords || binary.op == VectorOp::CompareUnsignedDwords) {
            for (unsigned lane = 0; lane < binary.size / 4; ++lane) {
                const auto& a = lhsLanes[lane];
                const auto& b = rhs[lane];
                result[lane] = binary.op == VectorOp::CompareUnsignedDwords ?
                    std::format("if {} >= {} then 4294967295 else 0", a, b) :
                    std::format("(if bit32.band({0}, 65535) >= bit32.band({1}, 65535) then 65535 else 0) + "
                        "(if bit32.rshift({0}, 16) >= bit32.rshift({1}, 16) then 4294901760 else 0)", a, b);
            }
        } else if (binary.op == VectorOp::AddDwords || binary.op == VectorOp::SubDwords) {
            const auto op = binary.op == VectorOp::AddDwords ? '+' : '-';
            for (unsigned lane = 0; lane < result.size(); ++lane)
                result[lane] = std::format("({} {} {}) % 4294967296", lhsLanes[lane], op, rhs[lane]);
        } else if (binary.op != VectorOp::UnpackLowQwords) {
            const auto name = binary.op == VectorOp::Xor ? "bxor" : binary.op == VectorOp::Or ? "bor" : "band";
            for (unsigned lane = 0; lane < result.size(); ++lane) {
                const auto lhs = binary.op == VectorOp::AndNot ? "bit32.bnot(" + dst[lane] + ")" : dst[lane];
                result[lane] = std::format("bit32.{}({}, {})", name, lhs, rhs[lane]);
            }
        }
        if (binary.size == 8)
            result[2] = result[3] = "0";
        line(depth, joinLanes(dst) + " = " + joinLanes(result));
        if (!reg)
            line(depth - 1, "end");
    }

    std::string floatOperand(const VectorOperand& operand, unsigned size, const Constants& constants) {
        std::string words;
        if (const auto* source = std::get_if<VectorRegister>(&operand)) {
            const auto lanes = xmm(*source);
            words = lanes[0] + ", " + lanes[1];
        } else {
            words = read(std::get<VectorMemory>(operand).address, size, constants);
            if (size == 4)
                words += ", 0";
        }
        return std::format("decodeFloat({}, {})", size, words);
    }

    void writeFloat(unsigned depth, VectorRegister dst, unsigned size, const std::string& floating) {
        const auto lanes = xmm(dst);
        const auto fields = size == 8 ? lanes[0] + ", " + lanes[1] : lanes[0];
        line(depth, std::format("{} = encodeFloat({}, {})", fields, size, floating));
        if (arm) {
            if (size == 4)
                line(depth, lanes[1] + " = 0");
            line(depth, lanes[2] + ", " + lanes[3] + " = 0, 0");
        }
    }

    std::string value(const Value& source, unsigned size, const Constants& constants) {
        return std::visit(Visit{
            [&](Register r) {
                const auto cell = reg(r.index);
                return size == 8 ? cell.pair() : cell.lo;
            },
            [&](Immediate i) {
                const auto word = wordLiteral(i.value);
                return size == 8 ? word.pair() : word.lo;
            },
            [&](EffectiveAddress addr) {
                if (const auto known = knownAddress(addr, constants))
                    data.materializeAddress(*known);
                if (size == 8)
                    return addressPair(addr, constants);
                if (const auto known = knownAddress(addr, constants))
                    return wordLiteral(*known).lo;
                if (addr.index == Zero && addr.displacement == 0)
                    return reg(addr.base).lo;
                return "(" + addressPair(addr, constants) + ")";
            },
            [&](Memory m) { return read(m.address, size, constants); },
            [](StackTop) { return std::string("savedLo, savedHi"); },
            [&](StackGuard) { return stackGuard().pair(); },
            [](ThreadLocalStorage) { return std::string("error(\"Windows thread-local storage is unavailable\", 0)"); },
        }, source);
    }

    void assign(unsigned depth, unsigned dst, unsigned size, const std::string& expression) {
        if (dst == Zero) {
            if (expression.find('(') != std::string::npos)
                line(depth, "do local _discard = " + expression + " end");
        } else {
            const auto cell = reg(dst);
            if (size == 8) {
                line(depth, std::format("{} = {}", cell.pair(), expression));
            } else if (size == 2) {
                line(depth, std::format("{0} = bit32.replace({0}, {1}, 0, 16)", cell.lo, expression));
            } else {
                line(depth, std::format("{} = {}, 0", cell.pair(), expression));
            }
        }
    }

    std::string byteValue(const Value& operand, unsigned field, const Constants& constants) {
        if (const auto* source = std::get_if<Register>(&operand))
            return std::format("bit32.extract({}, {}, 8)", reg(source->index).lo, field);
        return value(operand, 1, constants);
    }

    void assignByte(unsigned depth, const Value& target, unsigned field, std::string_view byte, Constants& constants) {
        if (const auto* dst = std::get_if<Register>(&target)) {
            const auto out = reg(dst->index);
            line(depth, std::format("{0} = bit32.replace({0}, {1}, {2}, 8)", out.lo, byte, field));
            constants[dst->index].reset();
        } else {
            const auto& at = std::get<Memory>(target).address;
            if (prepareWrite(depth, at, 1, constants))
                line(depth, std::format("write(1, address({}), {}, 0)", addressPair(at, constants), byte));
        }
    }

    void stackPush(unsigned depth, const LuauWord& word) {
        const auto sp = reg(4);
        line(depth, "do");
        line(depth + 1, "local valueLo, valueHi = " + word.pair());
        line(depth + 1, std::format("{} = offset({}, -8)", sp.pair(), sp.pair()));
        line(depth + 1, std::format("write(8, address({}), valueLo, valueHi)", sp.pair()));
        line(depth, "end");
    }

    void stackPop(unsigned depth) {
        const auto sp = reg(4);
        line(depth, std::format("local savedLo, savedHi = read(8, address({}))", sp.pair()));
        line(depth, std::format("{} = offset({}, 8)", sp.pair(), sp.pair()));
    }

    void binary(unsigned depth, const Binary& op, Constants& constants, bool flags) {
        if (op.dst == Zero && !flags)
            return;
        const auto lhs = reg(op.lhs);
        LuauWord rhs;
        std::optional<std::uint64_t> known;
        if (const auto* immediate = std::get_if<Immediate>(&op.rhs)) {
            rhs = wordLiteral(immediate->value);
            known = immediate->value;
        } else if (const auto* source = std::get_if<Register>(&op.rhs)) {
            rhs = reg(source->index);
            known = constants[source->index];
        } else if (std::holds_alternative<StackGuard>(op.rhs)) {
            rhs = stackGuard();
        } else {
            throw std::logic_error("unsupported IR operand for binary operation");
        }
        if (op.count != 0 || op.invert || op.extendBits || op.withCarry)
            known.reset();
        if (op.dst != Zero) {
            const auto previous = constants[op.lhs];
            constants[op.dst].reset();
            if (known && previous) {
                const auto result = fold(op.op, *previous, *known);
                constants[op.dst] = op.size == 8 ? result : std::uint32_t(result);
            }
        }

        const auto dst = op.dst == Zero ? LuauWord{"discardLo", "discardHi"} : reg(op.dst);
        line(depth, "do");
        if (op.extendBits) {
            needsShift = true;
            line(depth + 1, std::format("local shiftedLo, shiftedHi = bitfieldWord({}, 0, {}, {}, {}, {})",
                op.size, op.extendBits, op.count, op.signExtend, rhs.pair()));
            rhs = {"shiftedLo", "shiftedHi"};
        } else if (op.count != 0) {
            needsShift = true;
            line(depth + 1, std::format("local shiftedLo, shiftedHi = shiftParts({}, {}, {}, {})",
                unsigned(op.shift), op.size, op.count, rhs.pair()));
            rhs = {"shiftedLo", "shiftedHi"};
        }
        if (op.invert)
            rhs = {"bit32.bnot(" + rhs.lo + ")", "bit32.bnot(" + rhs.hi + ")"};
        if (op.op == BinaryOp::Add || op.op == BinaryOp::Sub) {
            const bool subtract = op.op == BinaryOp::Sub;
            if (flags || op.withCarry) {
                needsAddFlags = true;
                if (op.dst == Zero)
                    line(depth + 1, "local discardLo: number, discardHi: number = 0, 0");
                line(depth + 1, std::format("{}{} = addFlags({}, {}, {}, {}, {}{})",
                    dst.pair(), flags ? ", carry, overflow, negative, zero" : "",
                    subtract, arm, op.size, lhs.pair(), rhs.pair(),
                    op.withCarry ? (arm && subtract ? ", not carry" : ", carry") : ""));
            } else {
                const char symbol = subtract ? '-' : '+';
                line(depth + 1, std::format("local sum = {} {} {}", lhs.lo, symbol, rhs.lo));
                const auto high = op.size == 8 ?
                    std::format("({} {} {} + math.floor(sum / 4294967296)) % 4294967296", lhs.hi, symbol, rhs.hi) : "0";
                line(depth + 1, std::format("{} = sum % 4294967296, {}", dst.pair(), high));
            }
        } else {
            const auto helper = bitOperation(op.op);
            const auto high = op.size == 8 ? std::format("bit32.{}({}, {})", helper, lhs.hi, rhs.hi) : "0";
            line(depth + 1, std::format("{}{} = bit32.{}({}, {}), {}", op.dst == Zero ? "local " : "",
                dst.pair(), helper, lhs.lo, rhs.lo, high));
            if (flags) {
                line(depth + 1, "carry, overflow = false, false");
                line(depth + 1, std::format("negative, zero = {} >= 2147483648, {} == 0 and {} == 0",
                    op.size == 8 ? dst.hi : dst.lo, dst.lo, dst.hi));
            }
        }
        if (flags && features.parity)
            line(depth + 1, "parity = evenParity(" + dst.lo + ")");
        line(depth, "end");
    }

    void memoryBinary(unsigned depth, const MemoryBinary& op, Constants& constants, bool flags) {
        line(depth, "do");
        const auto limbs = [&](const Value& operand) {
            const auto expression = value(operand, op.size, constants);
            if (op.size == 2)
                return "bit32.band(" + expression + ", 65535), 0";
            return expression + (op.size == 4 ? ", 0" : "");
        };
        line(depth + 1, "local lhsLo, lhsHi = " + limbs(op.dst));
        line(depth + 1, "local rhsLo, rhsHi = " + limbs(op.rhs));
        if (op.writeBack || flags) {
            if (op.op == BinaryOp::Add || op.op == BinaryOp::Sub) {
                needsAddFlags = true;
                const auto results = flags ? "resultLo, resultHi, c, o, n, z" : "resultLo, resultHi";
                line(depth + 1, std::format("local {} = addFlags({}, false, {}, lhsLo, lhsHi, rhsLo, rhsHi{})",
                    results, op.op == BinaryOp::Sub, op.size, op.withCarry ? ", carry" : ""));
                if (flags)
                    line(depth + 1, op.keepCarry ? "overflow, negative, zero = o, n, z"
                                                  : "carry, overflow, negative, zero = c, o, n, z");
            } else {
                const auto helper = bitOperation(op.op);
                line(depth + 1, std::format("local resultLo, resultHi = bit32.{}(lhsLo, rhsLo), {}",
                    helper, op.size == 8 ? std::format("bit32.{}(lhsHi, rhsHi)", helper) : "0"));
                if (flags) {
                    line(depth + 1, "carry, overflow = false, false");
                    line(depth + 1, std::format("negative, zero = {} >= {}, resultLo == 0 and resultHi == 0",
                        op.size == 8 ? "resultHi" : "resultLo", op.size == 2 ? 32768u : 2147483648u));
                }
            }
            if (flags && features.parity)
                line(depth + 1, "parity = evenParity(resultLo)");
        }
        if (op.writeBack) {
            if (const auto* dst = std::get_if<Register>(&op.dst)) {
                assign(depth + 1, dst->index, op.size == 2 ? 2 : 8, op.size == 2 ? "resultLo" : "resultLo, resultHi");
                constants[dst->index].reset();
            } else {
                const auto& mem = std::get<Memory>(op.dst);
                if (prepareWrite(depth + 1, mem.address, op.size, constants))
                    line(depth + 1, std::format("write({}, address({}), resultLo, resultHi)", op.size,
                        addressPair(mem.address, constants)));
            }
        }
        line(depth, "end");
    }

    void effects(unsigned depth, const Block& block, Constants& constants) {
        std::set<const Effect*> liveWrites;
        if (features.flags) {
            bool live = observesExitFlags(block, features.calls);
            visitEdges(block, [&](Address target) { live |= flagsAtEntry.contains(target); });
            for (const auto& effect : block.effects | std::views::reverse) {
                if (live && writesFlags(effect))
                    liveWrites.insert(&effect);
                if (overwritesFlags(effect))
                    live = false;
                live |= readsFlags(effect);
            }
        }
        for (const auto& effect : block.effects) {
            const bool setFlags = liveWrites.contains(&effect);
            std::visit(Visit{
                [](const Nop&) {},
                [&](const Move& move) {
                    const bool pop = std::holds_alternative<StackTop>(move.src);
                    if (pop) {
                        line(depth, "do");
                        stackPop(depth + 1);
                        constants[4].reset();
                    }
                    const auto expr = value(move.src, move.size, constants);
                    assign(depth + pop, move.dst, move.size, expr);
                    if (pop)
                        line(depth, "end");
                    if (move.dst != Zero) {
                        std::optional<std::uint64_t> known;
                        if (const auto* imm = std::get_if<Immediate>(&move.src))
                            known = imm->value;
                        else if (const auto* source = std::get_if<Register>(&move.src))
                            known = constants[source->index];
                        else if (const auto* addr = std::get_if<EffectiveAddress>(&move.src))
                            known = knownAddress(*addr, constants);
                        else if (const auto* mem = std::get_if<Memory>(&move.src)) {
                            if (const auto at = knownAddress(mem->address, constants))
                                known = data.immutableWord(*at, move.size);
                        }
                        if (known && move.size == 4)
                            known = std::uint32_t(*known);
                        if (move.size < 4)
                            known.reset();
                        constants[move.dst] = known;
                    }
                },
                [&](const ByteMove& move) {
                    const auto byte = byteValue(move.src, move.srcField, constants);
                    if (const auto* regTarget = std::get_if<Register>(&move.dst)) {
                        const auto dst = reg(regTarget->index);
                        line(depth, std::format("{0} = bit32.replace({0}, {1}, {2}, 8)", dst.lo, byte, move.dstField));
                        constants[regTarget->index].reset();
                    } else {
                        const auto& mem = std::get<Memory>(move.dst);
                        if (prepareWrite(depth, mem.address, 1, constants))
                            line(depth, std::format("write(1, address({}), {}, 0)", addressPair(mem.address, constants),
                                byte));
                    }
                },
                [&](const Exchange& exchange) {
                    const auto source = reg(exchange.src.index);
                    const auto* dst = std::get_if<Register>(&exchange.dst);
                    const auto* mem = std::get_if<Memory>(&exchange.dst);
                    if (mem && !prepareWrite(depth, mem->address, exchange.size, constants))
                        return;
                    line(depth, "do");
                    if (dst) {
                        line(depth + 1, "local oldLo, oldHi = " + reg(dst->index).pair());
                    } else {
                        line(depth + 1, std::format("local at = address({})", addressPair(mem->address, constants)));
                        line(depth + 1, std::format("local oldLo, oldHi = read({}, at)", exchange.size));
                    }
                    if (exchange.add) {
                        needsAddFlags = true;
                        const auto assignFlags = setFlags ? ", c, o, n, z" : "";
                        line(depth + 1, std::format("local newLo, newHi{} = addFlags(false, false, {}, oldLo, oldHi, {})",
                            assignFlags, exchange.size, source.pair()));
                        if (setFlags) {
                            line(depth + 1, "carry, overflow, negative, zero = c, o, n, z");
                            if (features.parity)
                                line(depth + 1, "parity = evenParity(newLo)");
                        }
                    } else {
                        line(depth + 1, "local newLo, newHi = " + source.pair());
                    }
                    if (mem)
                        line(depth + 1, std::format("write({}, at, newLo, newHi)", exchange.size));
                    assign(depth + 1, exchange.src.index, exchange.size, exchange.size == 8 ? "oldLo, oldHi" : "oldLo");
                    if (dst) {
                        assign(depth + 1, dst->index, exchange.size, exchange.size == 8 ? "newLo, newHi" : "newLo");
                        constants[dst->index].reset();
                    }
                    constants[exchange.src.index].reset();
                    line(depth, "end");
                },
                [&](const AtomicAdd& op) {
                    if (!prepareWrite(depth, op.address, op.size, constants))
                        return;
                    needsAddFlags = true;
                    line(depth, "do");
                    line(depth + 1, "local at = address(" + addressPair(op.address, constants) + ")");
                    line(depth + 1, std::format("local oldLo, oldHi = read({}, at)", op.size));
                    line(depth + 1, std::format("local lo, hi = addFlags(false, true, {}, oldLo, oldHi, {})",
                        op.size, reg(op.src.index).pair()));
                    line(depth + 1, std::format("write({}, at, lo, hi)", op.size));
                    if (op.dst != Zero) {
                        assign(depth + 1, op.dst, op.size, op.size == 8 ? "oldLo, oldHi" : "oldLo");
                        constants[op.dst].reset();
                    }
                    line(depth, "end");
                },
                [&](const Extend& ext) {
                    line(depth, "do");
                    if (const auto* src = std::get_if<Register>(&ext.src)) {
                        line(depth + 1, std::format("local word = bit32.extract({}, {}, {})",
                            reg(src->index).lo, ext.field, ext.bits));
                    } else {
                        const auto& mem = std::get<Memory>(ext.src);
                        line(depth + 1, "local word = " + read(mem.address, ext.bits / 8, constants));
                    }
                    if (ext.sign) {
                        const auto bound = std::uint64_t(1) << ext.bits;
                        line(depth + 1, std::format("local negative = word >= {}", bound / 2));
                        const auto result = std::format("if negative then word + {} else word", (std::uint64_t(1) << 32) - bound);
                        assign(depth + 1, ext.dst, ext.size,
                            ext.size == 8 ? result + ", if negative then 4294967295 else 0" : result);
                    } else {
                        assign(depth + 1, ext.dst, ext.size, ext.size == 8 ? "word, 0" : "word");
                    }
                    constants[ext.dst].reset();
                    line(depth, "end");
                },
                [&](const ConditionalMove& move) {
                    const auto dst = reg(move.dst);
                    const auto source = value(move.src, move.size, constants);
                    line(depth, "do");
                    line(depth + 1, "local operandLo, operandHi = " + source + (move.size == 4 ? ", 0" : ""));
                    line(depth + 1, "if " + std::string(X64Conditions[move.condition]) + " then");
                    assign(depth + 2, move.dst, 8, "operandLo, operandHi");
                    line(depth + 1, "end");
                    if (move.size == 4)
                        line(depth + 1, dst.hi + " = 0");
                    line(depth, "end");
                    constants[move.dst].reset();
                },
                [&](const Select& select) {
                    if (select.dst == Zero)
                        return;
                    const auto yes = reg(select.yes.index);
                    const auto no = reg(select.no.index);
                    const auto branch = std::string(ArmConditions[select.condition]);
                    line(depth, "if " + branch + " then");
                    assign(depth + 1, select.dst, select.size, select.size == 8 ? yes.pair() : yes.lo);
                    line(depth, "else");
                    if (select.otherwise == SelectElse::Copy) {
                        assign(depth + 1, select.dst, select.size, select.size == 8 ? no.pair() : no.lo);
                    } else if (select.otherwise == SelectElse::Invert) {
                        const auto low = "bit32.bnot(" + no.lo + ")";
                        assign(depth + 1, select.dst, select.size,
                            select.size == 8 ? low + ", bit32.bnot(" + no.hi + ")" : low);
                    } else {
                        const auto negate = select.otherwise == SelectElse::Negate;
                        line(depth + 1, "local sum = " + (negate ? "-" + no.lo : no.lo + " + 1"));
                        const auto high = (negate ? "-" + no.hi : no.hi) + " + math.floor(sum / 4294967296)";
                        assign(depth + 1, select.dst, select.size,
                            select.size == 8 ? "sum % 4294967296, (" + high + ") % 4294967296"
                                             : "sum % 4294967296");
                    }
                    line(depth, "end");
                    constants[select.dst].reset();
                },
                [&](const Divide& div) {
                    needsDivision = true;
                    const auto quotient = reg(0);
                    const auto remainder = reg(2);
                    line(depth, std::format("{}, {} = unsignedDivide({}, {}, {}, {})", quotient.pair(), remainder.pair(),
                        div.size, quotient.pair(), remainder.pair(),
                        value(div.divisor, div.size, constants) + (div.size == 4 ? ", 0" : "")));
                    constants[0].reset();
                    constants[2].reset();
                },
                [&](const ConditionalCompare& compare) {
                    if (!setFlags)
                        return;
                    const auto condition = ArmConditions[compare.condition];
                    const auto rhs = value(compare.rhs, 8, constants);
                    line(depth, "if " + std::string(condition) + " then");
                    line(depth + 1, "local ignoredLo, ignoredHi");
                    line(depth + 1, std::format("ignoredLo, ignoredHi, carry, overflow, negative, zero = addFlags({}, true, {}, {}, {})",
                        compare.subtract, compare.size, reg(compare.lhs.index).pair(), rhs));
                    line(depth, "else");
                    line(depth + 1, std::format("carry, overflow, negative, zero = {}, {}, {}, {}",
                        bool(compare.otherwise & 2), bool(compare.otherwise & 1),
                        bool(compare.otherwise & 8), bool(compare.otherwise & 4)));
                    line(depth, "end");
                },
                [&](const DivideWord& div) {
                    if (div.dst == Zero)
                        return;
                    needsDivision = true;
                    assign(depth, div.dst, 8, std::format("divideWord({}, {}, {}, {})",
                        div.size, div.sign, reg(div.lhs.index).pair(), reg(div.rhs.index).pair()));
                    constants[div.dst].reset();
                },
                [&](const Multiply& mul) {
                    if (mul.dst == Zero)
                        return;
                    needsMultiply = true;
                    const auto dst = reg(mul.dst);
                    const bool narrow = mul.operands == MultiplyOperands::Signed32 || mul.operands == MultiplyOperands::Unsigned32;
                    const auto inputSize = narrow ? 4 : mul.size;
                    const auto lhs = value(mul.lhs, inputSize, constants);
                    const auto rhs = value(mul.rhs, inputSize, constants);
                    const auto high = inputSize == 4 ? ", 0" : "";
                    line(depth, "do");
                    line(depth + 1, "local lhsLo, lhsHi = " + lhs + high);
                    line(depth + 1, "local rhsLo, rhsHi = " + rhs + high);
                    if (mul.operands == MultiplyOperands::Signed32) {
                        line(depth + 1, "lhsHi = if lhsLo >= 2147483648 then 4294967295 else 0");
                        line(depth + 1, "rhsHi = if rhsLo >= 2147483648 then 4294967295 else 0");
                    }
                    const bool highResult = mul.operands == MultiplyOperands::SignedHigh || mul.operands == MultiplyOperands::UnsignedHigh;
                    const bool wideResult = mul.operands == MultiplyOperands::SignedWide || mul.operands == MultiplyOperands::UnsignedWide;
                    const bool flags = setFlags && mul.flags;
                    const auto call = highResult || wideResult || flags ?
                        std::format("signedMultiply({}, lhsLo, lhsHi, rhsLo, rhsHi{})", mul.size,
                            mul.operands == MultiplyOperands::UnsignedHigh ||
                            mul.operands == MultiplyOperands::UnsignedWide ? ", true" : "") :
                        mul.size == 4 ? "(multiply32(lhsLo, rhsLo)), 0" :
                        "multiplyLow(lhsLo, lhsHi, rhsLo, rhsHi)";
                    if (highResult) {
                        line(depth + 1, "local _, _, _, productLo, productHi = " + call);
                        line(depth + 1, dst.pair() + " = productLo, productHi");
                    } else if (wideResult) {
                        line(depth + 1, "local lo, hi, wideOverflow, upperLo, upperHi = " + call);
                        line(depth + 1, dst.pair() + " = lo, hi");
                        line(depth + 1, reg(2).pair() + " = upperLo, upperHi");
                        constants[2].reset();
                        if (flags)
                            line(depth + 1, "overflow = wideOverflow");
                    } else if (mul.accumulator != Zero || mul.subtract) {
                        const auto acc = reg(mul.accumulator);
                        const auto op = mul.subtract ? '-' : '+';
                        line(depth + 1, "local prodLo, prodHi = " + call);
                        line(depth + 1, std::format("local sum = {} {} prodLo", acc.lo, op));
                        const auto hi = mul.size == 8 ?
                            std::format("({} {} prodHi + math.floor(sum / 4294967296)) % 4294967296", acc.hi, op) : "0";
                        line(depth + 1, std::format("{} = sum % 4294967296, {}", dst.pair(), hi));
                    } else {
                        line(depth + 1, dst.pair() + (flags ? ", overflow" : "") + " = " + call);
                    }
                    if (flags)
                        line(depth + 1, "carry = overflow");
                    line(depth, "end");
                    constants[mul.dst].reset();
                },
                [&](const SetCondition& set) {
                    const auto byte = std::format("if {} then 1 else 0", X64Conditions[set.condition]);
                    if (const auto* regTarget = std::get_if<Register>(&set.dst)) {
                        const auto dst = reg(regTarget->index);
                        line(depth, std::format("{0} = bit32.replace({0}, {1}, {2}, 8)", dst.lo, byte, set.field));
                        constants[regTarget->index].reset();
                    } else {
                        const auto& mem = std::get<Memory>(set.dst);
                        if (prepareWrite(depth, mem.address, 1, constants))
                            line(depth, std::format("write(1, address({}), {}, 0)", addressPair(mem.address, constants),
                                byte));
                    }
                },
                [&](const Binary& op) { binary(depth, op, constants, setFlags); },
                [&](const MemoryBinary& op) { memoryBinary(depth, op, constants, setFlags && op.flags); },
                [&](const Store& store) {
                    if (prepareWrite(depth, store.address, store.size, constants))
                        line(depth, std::format("write({}, address({}), {})", store.size,
                            addressPair(store.address, constants), value(store.src, 8, constants)));
                },
                [&](const PairTransfer& pair) {
                    auto second = pair.address;
                    second.displacement += pair.size;
                    line(depth, "do");
                    if (pair.vector) {
                        const auto transfer = [&](unsigned index, const EffectiveAddress& address) {
                            const auto lanes = xmm(VectorRegister{index});
                            if (pair.size < 16) {
                                if (pair.load) {
                                    line(depth + 1, "do");
                                    line(depth + 2, "local lo, hi = " + read(address, pair.size, constants) +
                                        (pair.size == 4 ? ", 0" : ""));
                                    line(depth + 2, joinLanes(lanes) + " = lo, hi, 0, 0");
                                    line(depth + 1, "end");
                                } else if (prepareWrite(depth + 1, address, pair.size, constants)) {
                                    line(depth + 1, std::format("write({}, address({}), {}, {})", pair.size,
                                        addressPair(address, constants), lanes[0], lanes[1]));
                                }
                            } else if (pair.load) {
                                if (auto source = readVector(depth + 1, VectorMemory{address, false}, constants))
                                    line(depth + 1, joinLanes(lanes) + " = " + *source);
                            } else if (prepareWrite(depth + 1, address, 16, constants)) {
                                line(depth + 1, std::format("writeXmm(address({}), false, {})",
                                    addressPair(address, constants), joinLanes(lanes)));
                            }
                        };
                        transfer(pair.first, pair.address);
                        transfer(pair.second, second);
                    } else if (pair.load) {
                        const auto firstValue = pair.size == 8 ? "firstLo, firstHi" : "firstLo";
                        const auto secondValue = pair.size == 8 ? "secondLo, secondHi" : "secondLo";
                        line(depth + 1, std::format("local {} = {}", firstValue, read(pair.address, pair.size, constants)));
                        line(depth + 1, std::format("local {} = {}", secondValue, read(second, pair.size, constants)));
                        if (pair.sign) {
                            assign(depth + 1, pair.first, 8, "firstLo, if firstLo >= 2147483648 then 4294967295 else 0");
                            assign(depth + 1, pair.second, 8, "secondLo, if secondLo >= 2147483648 then 4294967295 else 0");
                        } else {
                            assign(depth + 1, pair.first, pair.size, firstValue);
                            assign(depth + 1, pair.second, pair.size, secondValue);
                        }
                        constants[pair.first] = pair.first == Zero ? Constants::value_type(0) : std::nullopt;
                        constants[pair.second] = pair.second == Zero ? Constants::value_type(0) : std::nullopt;
                    } else if (prepareWrite(depth + 1, pair.address, pair.size, constants) &&
                        prepareWrite(depth + 1, second, pair.size, constants)) {
                        line(depth + 1, std::format("write({}, address({}), {})",
                            pair.size, addressPair(pair.address, constants), reg(pair.first).pair()));
                        line(depth + 1, std::format("write({}, address({}), {})",
                            pair.size, addressPair(second, constants), reg(pair.second).pair()));
                    }
                    if (pair.writeback) {
                        const auto cell = reg(pair.address.base);
                        needsMemory = true;
                        line(depth + 1, std::format("{} = offset({}, {})", cell.pair(), cell.pair(), pair.writeback));
                        constants[pair.address.base].reset();
                    }
                    line(depth, "end");
                },
                [&](const Push& push) {
                    stackPush(depth, reg(push.src.index));
                    constants[4].reset();
                },
                [&](const KeepBits& keep) {
                    if (keep.dst == Zero)
                        return;
                    const auto dst = reg(keep.dst);
                    const auto& limb = keep.shift < 32 ? dst.lo : dst.hi;
                    line(depth, std::format("{0} = bit32.replace({0}, {1}, {2}, 16)", limb, keep.value, keep.shift % 32));
                    if (keep.size == 4)
                        line(depth, dst.hi + " = 0");
                    constants[keep.dst].reset();
                },
                [&](const ByteBinary& compare) {
                    line(depth, "do");
                    const auto lhs = byteValue(compare.lhs, compare.lhsField, constants);
                    const auto rhs = byteValue(compare.rhs, compare.rhsField, constants);
                    line(depth + 1, "local a, b = " + (compare.reverse ? rhs + ", " + lhs : lhs + ", " + rhs));
                    if (setFlags || compare.writeBack) {
                        if (compare.op == BinaryOp::Add || compare.op == BinaryOp::Sub) {
                            const bool subtract = compare.op == BinaryOp::Sub;
                            line(depth + 1, std::format("local total = a {} b", subtract ? '-' : '+'));
                            line(depth + 1, "local byte = total % 256");
                            if (setFlags) {
                                if (!compare.keepCarry)
                                    line(depth + 1, subtract ? "carry = total < 0" : "carry = total >= 256");
                                line(depth + 1, "zero, negative = byte == 0, byte >= 128");
                                line(depth + 1, std::format(
                                    "overflow = (((a >= 128) ~= (b >= 128)) == {}) and negative ~= (a >= 128)", subtract));
                            }
                        } else {
                            line(depth + 1, std::format("local byte = bit32.{}(a, b)", bitOperation(compare.op)));
                            if (setFlags)
                                line(depth + 1, "carry, overflow, zero, negative = false, false, byte == 0, byte >= 128");
                        }
                        if (setFlags && features.parity)
                            line(depth + 1, "parity = evenParity(byte)");
                    }
                    if (compare.writeBack)
                        assignByte(depth + 1, compare.lhs, compare.lhsField, "byte", constants);
                    line(depth, "end");
                },
                [&](const ByteShift& shift) {
                    if (shift.count && *shift.count == 0)
                        return;
                    const bool left = shift.op == ShiftOp::Left;
                    const bool sign = shift.op == ShiftOp::ArithmeticRight;
                    line(depth, "do");
                    const auto count = shift.count ? std::to_string(*shift.count) :
                        "bit32.band(" + reg(1).lo + ", 31)";
                    line(depth + 1, "local count = " + count);
                    line(depth + 1, "if count > 0 then");
                    line(depth + 2, "local source = " + byteValue(shift.dst, shift.field, constants));
                    const auto bits = sign ? "(if source >= 128 then source - 256 else source)" : "source";
                    const auto op = left ? "lshift" : sign ? "arshift" : "rshift";
                    line(depth + 2, std::format("local byte = bit32.band(bit32.{}({}, count), 255)", op, bits));
                    if (setFlags) {
                        const auto carry = left ? "count <= 8 and bit32.extract(source, 8 - count) ~= 0" :
                            sign ? "bit32.extract(source, math.min(count - 1, 7)) ~= 0" :
                            "count <= 8 and bit32.extract(source, count - 1) ~= 0";
                        line(depth + 2, std::format("carry, zero, negative = {}, byte == 0, byte >= 128", carry));
                        const auto overflow = left ? "count == 1 and negative ~= carry"
                            : sign ? "false" : "count == 1 and source >= 128";
                        line(depth + 2, std::format("overflow = {}", overflow));
                        if (features.parity)
                            line(depth + 2, "parity = evenParity(byte)");
                    }
                    assignByte(depth + 2, shift.dst, shift.field, "byte", constants);
                    line(depth + 1, "end");
                    line(depth, "end");
                },
                [&](const Shift& shift) {
                    needsShift = true;
                    const auto dst = reg(shift.dst.index);
                    const bool rotate = shift.op >= ShiftOp::RotateRight;
                    const auto writtenFlags = rotate ? ", carry, overflow" : ", carry, overflow, negative, zero";
                    line(depth, std::format("{}{} = {}({}, {}, {}, {})", dst.pair(),
                        setFlags ? writtenFlags : "", rotate ? "rotateWord" : "shiftWord",
                        unsigned(shift.op), shift.size, shift.count, dst.pair()));
                    if (setFlags && features.parity && !rotate)
                        line(depth, "parity = evenParity(" + dst.lo + ")");
                    constants[shift.dst.index].reset();
                },
                [&](const ShiftRegister& shift) {
                    if (shift.dst == Zero)
                        return;
                    needsShift = true;
                    const auto count = reg(shift.count.index).lo;
                    const auto input = reg(shift.src.index).pair();
                    if (shift.flags) {
                        const auto dst = reg(shift.dst);
                        line(depth, "do");
                        line(depth + 1, std::format("local count = {} % {}", count, shift.size * 8));
                        line(depth + 1, "if count ~= 0 then");
                        const bool rotate = shift.op >= ShiftOp::RotateRight;
                        const auto writtenFlags = rotate ? ", carry, overflow" : ", carry, overflow, negative, zero";
                        line(depth + 2, std::format("{}{} = {}({}, {}, count, {})",
                            dst.pair(), setFlags ? writtenFlags : "", rotate ? "rotateWord" : "shiftWord",
                            unsigned(shift.op), shift.size, input));
                        if (setFlags && features.parity && !rotate)
                            line(depth + 2, "parity = evenParity(" + dst.lo + ")");
                        line(depth + 1, "end");
                        line(depth, "end");
                    } else {
                        assign(depth, shift.dst, 8, std::format("shiftRegister({}, {}, {}, {})",
                            unsigned(shift.op), shift.size, count, input));
                    }
                    constants[shift.dst].reset();
                },
                [&](const Extract& op) {
                    if (op.dst == Zero)
                        return;
                    const auto high = reg(op.high.index);
                    const auto low = reg(op.low.index);
                    const auto blend = [](const std::string& lo, const std::string& hi, unsigned count) {
                        return std::format("bit32.bor(bit32.rshift({}, {}), bit32.lshift({}, {}))", lo, count, hi, 32 - count);
                    };
                    std::string result;
                    if (op.count == 0)
                        result = op.size == 8 ? low.pair() : low.lo;
                    else if (op.size == 4)
                        result = blend(low.lo, high.lo, op.count);
                    else if (op.count == 32)
                        result = low.hi + ", " + high.lo;
                    else if (op.count < 32)
                        result = blend(low.lo, low.hi, op.count) + ", " + blend(low.hi, high.lo, op.count);
                    else
                        result = blend(low.hi, high.lo, op.count - 32) + ", " + blend(high.lo, high.hi, op.count - 32);
                    assign(depth, op.dst, op.size, result);
                    constants[op.dst].reset();
                },
                [&](const Bitfield& field) {
                    if (field.dst == Zero)
                        return;
                    needsShift = true;
                    const auto extract = std::format("bitfieldWord({}, {}, {}, {}, {}, {})",
                        field.size, field.start, field.width, field.position, field.sign, reg(field.src.index).pair());
                    if (field.insert) {
                        const auto mask = (field.width == 64 ? UINT64_MAX : ((std::uint64_t(1) << field.width) - 1))
                            << field.position;
                        const auto preserve = wordLiteral(~mask);
                        const auto dst = reg(field.dst);
                        line(depth, "do");
                        line(depth + 1, "local lo, hi = " + extract);
                        const auto low = std::format("bit32.bor(bit32.band({}, {}), lo)", dst.lo, preserve.lo);
                        const auto high = std::format("bit32.bor(bit32.band({}, {}), hi)", dst.hi, preserve.hi);
                        assign(depth + 1, field.dst, field.size, field.size == 8 ? low + ", " + high : low);
                        line(depth, "end");
                    } else {
                        assign(depth, field.dst, field.size, extract);
                    }
                    constants[field.dst].reset();
                },
                [&](const BitScan& scan) {
                    if (scan.dst == Zero)
                        return;
                    line(depth, "do");
                    const auto input = value(scan.src, scan.size, constants);
                    line(depth + 1, scan.size == 8 ? "local lo, hi = " + input : "local lo, hi = " + input + ", 0");
                    if (scan.leadingCount) {
                        assign(depth + 1, scan.dst, 4, scan.size == 8 ?
                            "if hi ~= 0 then bit32.countlz(hi) else 32 + bit32.countlz(lo)" : "bit32.countlz(lo)");
                    } else {
                        if (setFlags)
                            line(depth + 1, "zero = lo == 0 and hi == 0");
                        line(depth + 1, "if lo ~= 0 or hi ~= 0 then");
                        const auto index = scan.reverse ? "if hi ~= 0 then 63 - bit32.countlz(hi) else 31 - bit32.countlz(lo)"
                            : "if lo ~= 0 then bit32.countrz(lo) else 32 + bit32.countrz(hi)";
                        assign(depth + 2, scan.dst, 4, index);
                        line(depth + 1, "end");
                    }
                    line(depth, "end");
                    constants[scan.dst].reset();
                },
                [&](const ByteSwap& op) {
                    const auto source = reg(op.src.index);
                    const std::string helper = op.reverseBits ? "reverseBits" : "bit32.byteswap";
                    needsShift |= op.reverseBits;
                    const auto lo = helper + "(" + source.lo + ")";
                    assign(depth, op.dst, op.size, op.size == 8 ?
                        helper + "(" + source.hi + "), " + lo : lo);
                    if (op.dst != Zero)
                        constants[op.dst].reset();
                },
                [&](const BitTest& bit) {
                    line(depth, "do");
                    const auto target = value(bit.target, bit.size, constants);
                    line(depth + 1, "local lo, hi = " + target + (bit.size == 4 ? ", 0" : ""));
                    line(depth + 1, std::format("local index = {} % {}", value(bit.index, 4, constants), bit.size * 8));
                    line(depth + 1, "local word = if index < 32 then lo else hi");
                    line(depth + 1, "local position = index % 32");
                    line(depth + 1, "local previous = bit32.extract(word, position)");
                    if (setFlags)
                        line(depth + 1, "carry = previous == 1");
                    if (bit.action != BitAction::Test) {
                        const auto updated = bit.action == BitAction::Set ? "1" :
                            bit.action == BitAction::Reset ? "0" : "1 - previous";
                        line(depth + 1, std::format("local updated = bit32.replace(word, {}, position)", updated));
                        line(depth + 1, "if index < 32 then lo = updated else hi = updated end");
                        if (const auto* dst = std::get_if<Register>(&bit.target)) {
                            assign(depth + 1, dst->index, 8, "lo, hi");
                            constants[dst->index].reset();
                        } else {
                            const auto& at = std::get<Memory>(bit.target).address;
                            if (prepareWrite(depth + 1, at, bit.size, constants))
                                line(depth + 1, std::format("write({}, address({}), lo, hi)", bit.size, addressPair(at, constants)));
                        }
                    }
                    line(depth, "end");
                },
                [&](const StringDirection& direction) {
                    usesDirection = true;
                    line(depth, std::format("direction = {}", direction.backward ? -1 : 1));
                },
                [&](const RepeatStore& store) {
                    usesDirection = true;
                    usesBudget = true;
                    needsMemory = true;
                    const auto value = reg(0);
                    const auto count = reg(1);
                    const auto dst = reg(7);
                    line(depth, std::format("if {} ~= 0 or {} > budget then error(\"guest instruction limit exceeded\", 0) end",
                        count.hi, count.lo));
                    line(depth, "budget -= " + count.lo);
                    line(depth, "for _ = 1, " + count.lo + " do");
                    line(depth + 1, std::format("write({}, address({}), {})", store.size, dst.pair(), value.pair()));
                    line(depth + 1, std::format("{} = offset({}, direction * {})", dst.pair(), dst.pair(), store.size));
                    line(depth, "end");
                    line(depth, count.pair() + " = 0, 0");
                    constants[1] = 0;
                    constants[7].reset();
                },
                [&](const CpuId&) {
                    const auto a = reg(0);
                    const auto b = reg(3);
                    const auto c = reg(1);
                    const auto d = reg(2);
                    // Feature-dependent code selects a baseline implementation in Luau.
                    line(depth, "if " + a.lo + " == 0 then");
                    assign(depth + 1, 0, 4, "1");
                    for (const auto index : {1u, 2u, 3u})
                        assign(depth + 1, index, 4, "0x7466754c");
                    line(depth, "else");
                    line(depth + 1, std::format("{}, {} = if {} == 0x80000000 then 0x80000000 else 0, 0",
                        a.lo, a.hi, a.lo));
                    line(depth + 1, std::format("{}, {}, {} = 0, 0, 0, 0, 0, 0", b.pair(), c.pair(), d.pair()));
                    line(depth, "end");
                    for (const auto index : {0u, 1u, 2u, 3u})
                        constants[index].reset();
                },
                [&](const VectorBinary& binary) { vectorBinary(depth, binary, constants); },
                [&](const InterleavedLoad4& load) {
                    for (unsigned reg = 0; reg < 4; ++reg) {
                        const auto dst = xmm(VectorRegister{(load.first.index + reg) % 32});
                        for (unsigned lane = 0; lane < 16 / load.elementSize; ++lane) {
                            auto address = load.address;
                            address.displacement += (lane * 4 + reg) * load.elementSize;
                            const auto word = lane * (load.elementSize / 4);
                            const auto fields = load.elementSize == 8 ? dst[word] + ", " + dst[word + 1] : dst[word];
                            line(depth, fields + " = " + read(address, load.elementSize, constants));
                        }
                    }
                },
                [&](const VectorSplat& op) {
                    const auto src = reg(op.src.index);
                    const auto repeated = op.elementSize == 1 ? "bit32.band(" + src.lo + ", 255) * 16843009" :
                        op.elementSize == 2 ? "bit32.band(" + src.lo + ", 65535) * 65537" : src.lo;
                    Lanes result{"0", "0", "0", "0"};
                    for (unsigned lane = 0; lane < op.size / 4; ++lane)
                        result[lane] = op.elementSize == 8 && lane % 2 ? src.hi : repeated;
                    line(depth, joinLanes(xmm(op.dst)) + " = " + joinLanes(result));
                },
                [&](const VectorWiden& op) {
                    const auto src = xmm(op.src);
                    const unsigned base = op.upper ? 2 : 0;
                    Lanes result;
                    if (op.bits == 16) {
                        for (unsigned lane = 0; lane < 4; ++lane) {
                            const auto value = std::format("bit32.extract({}, {}, 16)", src[base + lane / 2], (lane % 2) * 16);
                            result[lane] = op.shift ? std::format("bit32.lshift({}, {})", value, op.shift) : value;
                        }
                    } else {
                        for (unsigned lane = 0; lane < 2; ++lane) {
                            const auto& value = src[base + lane];
                            result[lane * 2] = op.shift ? std::format("bit32.lshift({}, {})", value, op.shift) : value;
                            result[lane * 2 + 1] = op.shift ? std::format("bit32.rshift({}, {})", value, 32 - op.shift) : "0";
                        }
                    }
                    line(depth, joinLanes(xmm(op.dst)) + " = " + joinLanes(result));
                },
                [&](const VectorMove& move) {
                    if (move.size < 16) {
                        std::string source;
                        if (const auto* src = std::get_if<VectorRegister>(&move.src)) {
                            const auto lanes = xmm(*src);
                            source = lanes[0] + ", " + (move.size == 8 ? lanes[1] : "0");
                        } else {
                            source = read(std::get<VectorMemory>(move.src).address, move.size, constants);
                            if (move.size == 4)
                                source += ", 0";
                        }
                        if (const auto* dst = std::get_if<VectorRegister>(&move.dst)) {
                            if (move.keepUpper) {
                                const auto lanes = xmm(*dst);
                                const auto fields = move.size == 8 ? lanes[0] + ", " + lanes[1] : lanes[0];
                                line(depth, fields + " = " + source);
                                return;
                            }
                            line(depth, "do");
                            line(depth + 1, "local lo, hi = " + source);
                            line(depth + 1, joinLanes(xmm(*dst)) + " = lo, hi, 0, 0");
                            line(depth, "end");
                        } else {
                            const auto& addr = std::get<VectorMemory>(move.dst).address;
                            if (prepareWrite(depth, addr, move.size, constants))
                                line(depth, std::format("write({}, address({}), {})", move.size, addressPair(addr, constants), source));
                        }
                        return;
                    }
                    const auto source = readVector(depth, move.src, constants);
                    if (!source)
                        return;
                    if (const auto* dst = std::get_if<VectorRegister>(&move.dst)) {
                        line(depth, joinLanes(xmm(*dst)) + " = " + *source);
                    } else {
                        const auto& mem = std::get<VectorMemory>(move.dst);
                        if (prepareWrite(depth, mem.address, 16, constants))
                            line(depth, std::format("writeXmm(address({}), {}, {})", addressPair(mem.address, constants),
                                mem.aligned, *source));
                    }
                },
                [&](const VectorTransfer& transfer) {
                    const auto lanes = xmm(transfer.xmm);
                    const auto gp = reg(transfer.gp.index);
                    if (transfer.lane && transfer.toXmm) {
                        const auto first = *transfer.lane * (transfer.size / 4);
                        if (transfer.size == 8)
                            line(depth, lanes[first] + ", " + lanes[first + 1] + " = " + gp.pair());
                        else
                            line(depth, lanes[first] + " = " + gp.lo);
                    } else if (transfer.toXmm) {
                        const auto words = transfer.size == 8 ? gp.pair() : gp.lo + ", 0";
                        line(depth, joinLanes(lanes) + " = " + words + ", 0, 0");
                    } else if (transfer.lane && transfer.gp.index != Zero) {
                        const auto lane = *transfer.lane;
                        assign(depth, transfer.gp.index, 4,
                            std::format("bit32.extract({}, {}, 16)", lanes[lane / 2], (lane % 2) * 16));
                        constants[transfer.gp.index].reset();
                    } else if (transfer.gp.index != Zero) {
                        assign(depth, transfer.gp.index, transfer.size,
                            transfer.size == 8 ? lanes[0] + ", " + lanes[1] : lanes[0]);
                        constants[transfer.gp.index].reset();
                    }
                },
                [&](const VectorHalfMove& move) {
                    const auto half = [&](VectorRegister value, bool high) {
                        const auto lanes = xmm(value);
                        const unsigned first = high ? 2 : 0;
                        return lanes[first] + ", " + lanes[first + 1];
                    };
                    const auto* from = std::get_if<VectorRegister>(&move.src);
                    const auto data = from ? half(*from, move.srcHigh)
                        : read(std::get<VectorMemory>(move.src).address, 8, constants);
                    if (const auto* to = std::get_if<VectorRegister>(&move.dst)) {
                        line(depth, half(*to, move.dstHigh) + " = " + data);
                    } else {
                        const auto& at = std::get<VectorMemory>(move.dst).address;
                        if (prepareWrite(depth, at, 8, constants))
                            line(depth, std::format("write(8, address({}), {})", addressPair(at, constants), data));
                    }
                },
                [&](const VectorShiftBytes& shift) {
                    const auto lanes = xmm(shift.dst);
                    Lanes result{"0", "0", "0", "0"};
                    const auto part = [&](int lane, std::string_view operation, unsigned bits) -> std::string {
                        if (lane < 0 || lane >= int(lanes.size()))
                            return "0";
                        return bits ? std::format("bit32.{}({}, {})", operation, lanes[lane], bits) : lanes[lane];
                    };
                    if (shift.count < 16) {
                        const int direction = shift.left ? -1 : 1;
                        const unsigned bits = shift.count % 4 * 8;
                        for (int lane = 0; lane < int(lanes.size()); ++lane) {
                            const auto from = lane + int(shift.count / 4) * direction;
                            result[lane] = part(from, shift.left ? "lshift" : "rshift", bits);
                            if (bits)
                                result[lane] = "bit32.bor(" + result[lane] + ", " +
                                    part(from + direction, shift.left ? "rshift" : "lshift", 32 - bits) + ")";
                        }
                    }
                    line(depth, joinLanes(lanes) + " = " + joinLanes(result));
                },
                [&](const VectorIntToDouble& op) {
                    needsFloating = true;
                    const auto* source = std::get_if<VectorRegister>(&op.src);
                    const auto lanes = xmm(op.dst);
                    std::string words;
                    if (source) {
                        const auto input = xmm(*source);
                        words = input[0] + ", " + input[1];
                    } else {
                        words = read(std::get<VectorMemory>(op.src).address, 8, constants);
                    }
                    line(depth, "do");
                    line(depth + 1, "local first, second = " + words);
                    line(depth + 1, lanes[0] + ", " + lanes[1] + " = encodeFloat(8, integerAsFloat(4, 8, true, first, 0))");
                    line(depth + 1, lanes[2] + ", " + lanes[3] + " = encodeFloat(8, integerAsFloat(4, 8, true, second, 0))");
                    line(depth, "end");
                },
                [&](const VectorSignMask& op) {
                    const auto lanes = xmm(op.src);
                    std::string bits = "0";
                    for (unsigned lane = 0; lane < 16 / op.size; ++lane)
                        bits += std::format(" + {} * bit32.extract({}, 31)", 1u << lane, lanes[(lane + 1) * (op.size / 4) - 1]);
                    assign(depth, op.dst, 4, bits);
                    constants[op.dst].reset();
                },
                [&](const VectorShuffle& op) {
                    const auto* source = std::get_if<VectorRegister>(&op.src);
                    const auto input = source ? xmm(*source) : Lanes{"lane0", "lane1", "lane2", "lane3"};
                    if (!source) {
                        const auto lanes = readVector(depth, op.src, constants);
                        if (!lanes)
                            return;
                        line(depth++, "do");
                        line(depth, "local " + joinLanes(input) + " = " + *lanes);
                    }
                    auto result = input;
                    if (op.highWords) {
                        const unsigned base = *op.highWords ? 2 : 0;
                        const auto pick = [&](unsigned i) {
                            const auto index = (op.mask >> (i * 2)) & 3;
                            return std::format("bit32.extract({}, {}, 16)", input[base + index / 2], (index % 2) * 16);
                        };
                        for (unsigned i = 0; i < 2; ++i)
                            result[base + i] = std::format("{} + 65536 * {}", pick(i * 2), pick(i * 2 + 1));
                    } else {
                        for (unsigned i = 0; i < result.size(); ++i)
                            result[i] = input[(op.mask >> (i * 2)) & 3];
                    }
                    line(depth, joinLanes(xmm(op.dst)) + " = " + joinLanes(result));
                    if (!source)
                        line(depth - 1, "end");
                },
                [&](const VectorImmediate& immediate) {
                    const auto& words = immediate.lanes;
                    line(depth, std::format("{} = {}, {}, {}, {}", joinLanes(xmm(immediate.dst)),
                        words[0], words[1], words[2], words[3]));
                },
                [&](const VectorByteOperation& op) {
                    needsShift = true;
                    const auto source = xmm(op.src);
                    Lanes result{"0", "0", "0", "0"};
                    for (unsigned lane = 0; lane < op.size / 4; ++lane) {
                        if (op.reduce)
                            result[0] += " + sumBytes(" + source[lane] + ")";
                        else
                            result[lane] = "populationByByte(" + source[lane] + ")";
                    }
                    line(depth, joinLanes(xmm(op.dst)) + " = " + joinLanes(result));
                },
                [&](const FloatBinary& op) {
                    if (op.op == FloatOp::Abs) {
                        const auto src = xmm(std::get<VectorRegister>(op.src));
                        const auto dst = joinLanes(xmm(op.dst));
                        const auto words = op.size == 8 ? src[0] + ", bit32.band(" + src[1] + ", 2147483647)"
                            : "bit32.band(" + src[0] + ", 2147483647), 0";
                        line(depth, dst + " = " + words + ", 0, 0");
                        return;
                    }
                    needsFloating = true;
                    const auto rhs = floatOperand(op.src, op.sourceSize, constants);
                    if (op.op >= FloatOp::Sqrt) {
                        const auto value = op.op == FloatOp::Sqrt ? "math.sqrt(" + rhs + ")" :
                            op.op == FloatOp::Ceil ? "math.ceil(" + rhs + ")" :
                            op.op == FloatOp::Floor ? "math.floor(" + rhs + ")" : rhs;
                        writeFloat(depth, op.dst, op.size, value);
                        return;
                    }
                    line(depth, "do");
                    line(depth + 1, "local lhs = " + floatOperand(op.dst, op.size, constants));
                    line(depth + 1, "local rhs = " + rhs);
                    if (op.op == FloatOp::Min || op.op == FloatOp::Max) {
                        const auto comparison = op.op == FloatOp::Min ? '<' : '>';
                        writeFloat(depth + 1, op.dst, op.size, std::format("if lhs {} rhs then lhs else rhs", comparison));
                    } else {
                        constexpr std::array operators{'+', '-', '*', '/'};
                        writeFloat(depth + 1, op.dst, op.size, std::format("lhs {} rhs", operators[unsigned(op.op)]));
                    }
                    line(depth, "end");
                },
                [&](const FloatCompare& compare) {
                    needsFloating = true;
                    line(depth, "do");
                    line(depth + 1, "local lhs = " + floatOperand(compare.lhs, compare.size, constants));
                    line(depth + 1, "local rhs = " + (compare.rhs ? floatOperand(*compare.rhs, compare.size, constants) : "0"));
                    if (setFlags) {
                        line(depth + 1, "local unordered = lhs ~= lhs or rhs ~= rhs");
                        if (arm)
                            line(depth + 1, "carry, zero, overflow, negative = not (lhs < rhs), lhs == rhs, unordered, lhs < rhs");
                        else
                            line(depth + 1, "carry, zero, overflow, negative = unordered or lhs < rhs, unordered or lhs == rhs, false, false");
                        if (features.parity)
                            line(depth + 1, "parity = unordered");
                    }
                    line(depth, "end");
                },
                [&](const FloatMask& compare) {
                    needsFloating = true;
                    constexpr std::array<std::string_view, 8> conditions{
                        "lhs == rhs", "lhs < rhs", "lhs <= rhs", "unordered",
                        "lhs ~= rhs", "not (lhs < rhs)", "not (lhs <= rhs)", "not unordered"
                    };
                    line(depth, "do");
                    line(depth + 1, "local lhs = " + floatOperand(compare.dst, compare.size, constants));
                    line(depth + 1, "local rhs = " + floatOperand(compare.src, compare.size, constants));
                    if (compare.predicate == 3 || compare.predicate == 7)
                        line(depth + 1, "local unordered = lhs ~= lhs or rhs ~= rhs");
                    const auto lanes = xmm(compare.dst);
                    line(depth + 1, std::format("{} = if {} then 4294967295 else 0", lanes[0], conditions[compare.predicate]));
                    if (compare.size == 8)
                        line(depth + 1, lanes[1] + " = " + lanes[0]);
                    line(depth, "end");
                },
                [&](const IntegerToFloat& op) {
                    needsFloating = true;
                    const auto words = value(op.src, op.integerSize, constants) + (op.integerSize == 4 ? ", 0" : "");
                    writeFloat(depth, op.dst, op.size, std::format("integerAsFloat({}, {}, {}, {})",
                        op.integerSize, op.size, op.sign, words));
                },
                [&](const FloatToInteger& op) {
                    needsFloating = true;
                    auto input = floatOperand(op.src, op.floatSize, constants);
                    if (op.rounding != Rounding::Truncate)
                        input = std::string(op.rounding == Rounding::Up ? "math.ceil(" : "math.floor(") + input + ")";
                    assign(depth, op.dst, 8, std::format("truncateFloat({}, {}, {}, {})", op.size, arm, op.sign,
                        input));
                    constants[op.dst].reset();
                },
                [&](const FloatingControl& control) {
                    usesFloatingControl = true;
                    const auto cell = control.size == 4 ? "mxcsr" : "x87Control";
                    if (control.load) {
                        line(depth, std::string(cell) + " = " + read(control.address, control.size, constants));
                        const auto check = control.size == 4 ? "bit32.band(mxcsr, 0xffffffc0) ~= 0x1f80" : "x87Control ~= 0x037f";
                        line(depth, std::format("if {} then error(\"unsupported guest floating-point control mode\", 0) end", check));
                    } else if (prepareWrite(depth, control.address, control.size, constants)) {
                        line(depth, std::format("write({}, address({}), {}, 0)", control.size,
                            addressPair(control.address, constants), cell));
                    }
                },
            }, effect);
        }
    }

    std::string condition(const Condition& node) {
        if (const auto* flags = std::get_if<FlagsCondition>(&node))
            return std::string((arm ? ArmConditions : X64Conditions)[flags->code]);
        if (const auto* test = std::get_if<TestBitCondition>(&node)) {
            const auto word = reg(test->reg);
            return std::format("bit32.extract({}, {}) {} 0", test->bit < 32 ? word.lo : word.hi,
                test->bit % 32, test->inverted ? "~=" : "==");
        }
        const auto& compare = std::get<ZeroCondition>(node);
        const auto v = reg(compare.reg);
        auto expression = v.lo + " == 0";
        if (compare.size == 8)
            expression += " and " + v.hi + " == 0";
        return compare.inverted ? "not (" + expression + ")" : expression;
    }

    std::optional<std::vector<Address>> backEdge(Address start, Address header) const {
        std::vector<Address> path;
        while (start != header) {
            if (path.size() >= 32 || std::ranges::find(path, start) != path.end())
                return {};
            path.push_back(start);
            const auto target = jumpTarget(graph.at(start));
            if (!target)
                return {};
            start = *target;
        }
        return path;
    }

    void tick(unsigned depth, std::size_t count) {
        usesBudget = true;
        line(depth, std::format("budget -= {}", count));
        line(depth, "if budget < 0 then error(\"guest instruction limit exceeded\", 0) end");
    }

    void region(Address pc, unsigned depth, Constants constants) {
        constants[Zero] = 0;
        if (!activeLoops.empty()) {
            const auto header = activeLoops.back();
            const auto& exits = loops.at(header);
            if (pc == header && active.contains(pc)) {
                line(depth, "continue");
                return;
            }
            if (const auto exit = std::ranges::find(exits, pc); exit != exits.end()) {
                if (exits.size() > 1)
                    line(depth, std::format("loopExit_{:x} = {}", header, exit - exits.begin() + 1));
                line(depth, "break");
                return;
            }
            if (remaining == 0) {
                outline(depth, pc);
                return;
            }
        }
        if (active.contains(pc)) {
            outline(depth, pc);
            return;
        }
        if (const auto loop = loops.find(pc); loop != loops.end() &&
            (activeLoops.empty() || activeLoops.back() != pc)) {
            const auto& exits = loop->second;
            const auto outerRemaining = remaining;
            remaining = 96;
            activeLoops.push_back(pc);
            if (exits.size() > 1)
                line(depth, std::format("local loopExit_{:x} = 0", pc));
            line(depth, "while true do");
            tick(depth + 1, 1);
            region(pc, depth + 1, {});
            line(depth, "end");
            activeLoops.pop_back();
            remaining = outerRemaining;
            if (exits.size() == 1) {
                region(exits.front(), depth, {});
            } else {
                for (std::size_t i = 0; i < exits.size(); ++i) {
                    line(depth, std::format("{} loopExit_{:x} == {} then", i == 0 ? "if" : "elseif", pc, i + 1));
                    region(exits[i], depth + 1, {});
                }
                line(depth, "else");
                trap(depth + 1, "invalid guest loop exit");
                line(depth, "end");
            }
            return;
        }
        active.insert(pc);
        // Share branch joins instead of duplicating their continuations.
        const auto join = predecessors.find(pc);
        if (activeLoops.empty() && pc != regionEntry && (remaining == 0 ||
            (join != predecessors.end() && join->second > 1))) {
            outline(depth, pc);
            active.erase(pc);
            return;
        }
        if (remaining)
            --remaining;
        const auto& block = graph.at(pc);
        const auto* branch = std::get_if<Branch>(&block.end);
        if (branch && activeLoops.empty()) {
            const auto taken = backEdge(branch->taken, pc);
            const auto other = backEdge(branch->other, pc);
            if (bool(taken) != bool(other)) {
                const auto& loop = taken ? *taken : *other;
                const auto exit = taken ? branch->other : branch->taken;
                auto loopConstants = Constants{};
                loopConstants[Zero] = 0;
                line(depth, "while true do");
                std::size_t count = 0;
                for (const auto address : loop) {
                    const auto& part = graph.at(address);
                    count += part.effects.size() + part.hasTerminator;
                }
                tick(depth + 1, block.effects.size() + block.hasTerminator);
                effects(depth + 1, block, loopConstants);
                const auto expression = condition(branch->condition);
                line(depth + 1, std::format("if {} then break end", taken ? "not (" + expression + ")" : expression));
                if (count)
                    tick(depth + 1, count);
                for (const auto address : loop)
                    effects(depth + 1, graph.at(address), loopConstants);
                line(depth, "end");
                region(exit, depth, {});
                active.erase(pc);
                return;
            }
        }
        const auto target = jumpTarget(block);
        if (target == pc) {
            line(depth, "while true do");
            tick(depth + 1, block.effects.size() + block.hasTerminator);
            Constants loop{};
            loop[Zero] = 0;
            effects(depth + 1, block, loop);
            line(depth, "end");
            active.erase(pc);
            return;
        }
        effects(depth, block, constants);
        if (target) {
            const auto* imported = arm ? findImport(Immediate{std::uint64_t(*target)}, constants, true) : nullptr;
            if (imported && emitImport(depth, *imported))
                returnFromFunction(depth, Return{Register{30}});
            else
                region(*target, depth, constants);
        } else if (branch) {
            line(depth, "if " + condition(branch->condition) + " then");
            region(branch->taken, depth + 1, constants);
            line(depth, "else");
            region(branch->other, depth + 1, constants);
            line(depth, "end");
        } else if (const auto* call = std::get_if<Call>(&block.end)) {
            const auto* imported = findImport(call->target, constants, true);
            const auto name = imported ? importName(*imported) : std::string_view{};
            if (convention != CallingConvention::Microsoft && (name == "_setjmp" || name == "setjmp")) {
                emitSetjmp(depth, call->resume);
            } else if (imported && emitImport(depth, *imported)) {
                region(call->resume, depth, {});
            } else if (const auto callee = resolveTarget(call->target, constants)) {
                addFunction(*callee);
                callPrologue(depth, call->resume);
                line(depth, std::format("runGuestRoutine({}, {})", routine(*callee), call->resume));
                region(call->resume, depth, {});
            } else if (emitImport(depth, call->target, constants)) {
                region(call->resume, depth, {});
            } else if (!imported && !addressTaken.empty() &&
                (std::holds_alternative<Register>(call->target) || std::holds_alternative<Memory>(call->target))) {
                emitFunctionPointer(depth, call->target, call->resume, constants);
            } else {
                indirect(depth, pc, call->target, constants);
            }
        } else if (const auto* jump = std::get_if<Jump>(&block.end)) {
            if (!jump->destinations.empty()) {
                const auto selector = reg(std::get<Register>(jump->target).index);
                bool first = true;
                for (const auto destination : jump->destinations) {
                    line(depth, std::format("{} {} == {} and {} == 0 then", first ? "if" : "elseif",
                        selector.lo, destination, selector.hi));
                    region(destination, depth + 1, {});
                    first = false;
                }
                line(depth, "else");
                trap(depth + 1, std::format("guest jump table target is outside the resolved cases at {:#x}", pc));
                line(depth, "end");
            } else if (const auto target = resolveTarget(jump->target, constants))
                region(*target, depth, constants);
            else if (emitImport(depth, jump->target, constants))
                returnFromFunction(depth, arm ? Return{Register{30}} : Return{StackTop{}});
            else if (!addressTaken.empty() && (std::holds_alternative<Register>(jump->target) ||
                (std::holds_alternative<Memory>(jump->target) && !findImport(jump->target, constants, true)))) {
                includeFunctionPointers();
                needsMemory = true;
                line(depth, std::format("local callee = functionPointers[address({})]", value(jump->target, 8, constants)));
                line(depth, std::format("if not callee then error(\"unknown guest tail-call target at {:#x}\", 0) end", pc));
                line(depth, "return callee");
            }
            else
                indirect(depth, pc, jump->target, constants);
        } else if (const auto* ret = std::get_if<Return>(&block.end)) {
            returnFromFunction(depth, *ret);
        } else {
            trap(depth, std::get<Trap>(block.end).message);
        }
        active.erase(pc);
    }

    void outline(unsigned depth, Address pc) {
        addFunction(pc);
        tick(depth, 1);
        line(depth, "return " + routine(pc));
    }

    void callPrologue(unsigned depth, Address resume) {
        if (arm)
            assign(depth, 30, 8, wordLiteral(resume).pair());
        else
            stackPush(depth, wordLiteral(resume));
        tick(depth, 1);
    }

    void includeFunctionPointers() {
        if (usesFunctionPointers)
            return;
        usesFunctionPointers = true;
        for (const auto entry : addressTaken)
            addFunction(entry);
    }

    void runCallback(unsigned depth, std::string_view callback) {
        if (arm)
            line(depth, "local linkLo, linkHi = " + reg(30).pair());
        callPrologue(depth, 4294967295);
        line(depth, std::format("runGuestRoutine({}, 4294967295)", callback));
        if (arm)
            assign(depth, 30, 8, "linkLo, linkHi");
    }

    void emitFunctionPointer(unsigned depth, const Value& target, Address resume, const Constants& constants) {
        includeFunctionPointers();
        needsMemory = true;
        line(depth, "do");
        line(depth + 1, std::format("local callee = functionPointers[address({})]", value(target, 8, constants)));
        line(depth + 1, "if not callee then error(\"unknown guest function pointer\", 0) end");
        callPrologue(depth + 1, resume);
        line(depth + 1, std::format("runGuestRoutine(callee, {})", resume));
        line(depth, "end");
        region(resume, depth, {});
    }

    void emitSetjmp(unsigned depth, Address resume) {
        if (!activeLoops.empty()) {
            trap(depth, "setjmp inside a recovered loop is unsupported");
            return;
        }
        needsJumpFrames = true;
        needsMemory = true;
        const auto environment = reg(argumentRegisters(arm, convention)[0]);
        constexpr std::array x64Saved{3u, 4u, 5u, 12u, 13u, 14u, 15u};
        constexpr std::array armSaved{19u, 20u, 21u, 22u, 23u, 24u, 25u, 26u, 27u, 28u, 29u, 30u, 31u};
        const auto nonvolatile = arm ? std::span<const unsigned>(armSaved) : std::span<const unsigned>(x64Saved);
        line(depth, "do");
        if (arm)
            assign(depth + 1, 30, 8, wordLiteral(resume).pair());
        for (const auto index : nonvolatile) {
            const auto saved = reg(index);
            line(depth + 1, std::format("local saved{}lo, saved{}hi = {}", index, index, saved.pair()));
        }
        if (arm) {
            for (unsigned index = 8; index <= 15; ++index) {
                const auto vector = xmm(VectorRegister{index});
                line(depth + 1, std::format("local savedVector{}Lo, savedVector{}Hi = {}, {}",
                    index, index, vector[0], vector[1]));
            }
        }
        line(depth + 1, std::format("protectJump(jumpFrames, address({}), function(jumpValue: number): ()",
            environment.pair()));
        assign(depth + 2, 0, 8, "jumpValue, 0");
        line(depth + 2, "local function resumeRoutine(expectedReturn: number): GuestRoutine?");
        region(resume, depth + 3, {});
        line(depth + 2, "end");
        line(depth + 2, "runGuestRoutine(resumeRoutine, expectedReturn)");
        line(depth + 1, "end, function()");
        for (const auto index : nonvolatile)
            line(depth + 2, std::format("{} = saved{}lo, saved{}hi", reg(index).pair(), index, index));
        if (arm) {
            for (unsigned index = 8; index <= 15; ++index) {
                const auto vector = xmm(VectorRegister{index});
                line(depth + 2, std::format("{}, {} = savedVector{}Lo, savedVector{}Hi",
                    vector[0], vector[1], index, index));
            }
        }
        line(depth + 1, "end)");
        line(depth + 1, "return nil");
        line(depth, "end");
    }

    void returnFromFunction(unsigned depth, const Return& ret) {
        if (arm) {
            const auto value = reg(std::get<Register>(ret.target).index);
            line(depth, std::format("if {} ~= expectedReturn or {} ~= 0 then", value.lo, value.hi));
            trap(depth + 1, "indirect ARM64 return is unsupported");
            line(depth, "end");
        } else if (features.stack) {
            stackPop(depth);
            if (ret.stackAdjust) {
                const auto sp = reg(4);
                line(depth, std::format("{} = offset({}, {})", sp.pair(), sp.pair(), ret.stackAdjust));
            }
            line(depth, "if savedLo ~= expectedReturn or savedHi ~= 0 then");
            trap(depth + 1, "indirect x86-64 return is unsupported");
            line(depth, "end");
        }
        line(depth, "return nil");
    }

    const GuestImport* findImport(const Value& target, const Constants& constants, bool throughThunk = false) const {
        if (arm) {
            if (!throughThunk)
                return nullptr;
            const auto address = resolveTarget(target, constants);
            if (!address || !graph.contains(*address))
                return nullptr;
            const auto& block = graph.at(*address);
            if (block.effects.size() != 2)
                return nullptr;
            const auto* page = std::get_if<Move>(&block.effects[0]);
            const auto* load = std::get_if<Move>(&block.effects[1]);
            const auto* jump = std::get_if<Jump>(&block.end);
            const auto* pointer = jump ? std::get_if<Register>(&jump->target) : nullptr;
            const auto* base = page ? std::get_if<Immediate>(&page->src) : nullptr;
            const auto* memory = load ? std::get_if<Memory>(&load->src) : nullptr;
            if (!base || !memory || !pointer || page->size != 8 || load->size != 8 ||
                page->dst != memory->address.base || pointer->index != load->dst || memory->address.index != Zero)
                return nullptr;
            const auto slot = base->value + memory->address.displacement;
            const auto* import = data.unresolved(slot, 8);
            return import && import->start == slot && import->size == 8 ? import : nullptr;
        }
        if (throughThunk) {
            if (const auto address = resolveTarget(target, constants)) {
                const auto& block = graph.at(*address);
                const auto* jump = std::get_if<Jump>(&block.end);
                if (jump && std::ranges::all_of(block.effects, [](const Effect& effect) {
                    return std::holds_alternative<Nop>(effect);
                }))
                    return findImport(jump->target, constants);
            }
        }
        const auto* memory = std::get_if<Memory>(&target);
        if (!memory)
            return nullptr;
        const auto address = knownAddress(memory->address, constants);
        const auto* import = address ? data.unresolved(*address, 8) : nullptr;
        if (!import || !import->callable || import->start != *address || import->size != 8)
            return nullptr;
        return import;
    }

    bool emitImport(unsigned depth, const Value& target, const Constants& constants) {
        const auto* import = findImport(target, constants);
        return import && emitImport(depth, *import);
    }

    std::string_view importName(const GuestImport& import) const {
        auto name = import.name;
        if (import.leadingUnderscore && name.starts_with('_'))
            name.remove_prefix(1);
        return name;
    }

    void emitFiberImport(unsigned depth, std::string_view name) {
        usesFiberSlots = true;
        usesLastError = true;
        const auto args = argumentRegisters(arm, convention);
        const auto index = reg(args[0]);
        const auto value = reg(args[1]);
        if (name == "FlsAlloc") {
            line(depth, std::format("fiberSlots[fiberNext] = {{lo = 0, hi = 0, callbackLo = {}, callbackHi = {}}}",
                index.lo, index.hi));
            assign(depth, 0, 4, "fiberNext");
            line(depth, "fiberNext += 1");
            return;
        }
        line(depth, "do");
        line(depth + 1, "local slot = fiberSlots[" + index.lo + "]");
        line(depth + 1, "if not slot then");
        line(depth + 2, "lastError = 87");
        assign(depth + 2, 0, 4, "0");
        line(depth + 1, "else");
        if (name == "FlsGetValue") {
            line(depth + 2, "if slot.lo == 0 and slot.hi == 0 then lastError = 0 end");
            assign(depth + 2, 0, 8, "slot.lo, slot.hi");
        } else if (name == "FlsSetValue") {
            line(depth + 2, "slot.lo, slot.hi = " + value.pair());
            assign(depth + 2, 0, 4, "1");
        } else {
            line(depth + 2, "fiberSlots[" + index.lo + "] = nil");
            line(depth + 2, "if (slot.lo ~= 0 or slot.hi ~= 0) and (slot.callbackLo ~= 0 or slot.callbackHi ~= 0) then");
            includeFunctionPointers();
            needsMemory = true;
            line(depth + 3, "local callback = functionPointers[address(slot.callbackLo, slot.callbackHi)]");
            line(depth + 3, "if not callback then error(\"unknown guest fiber cleanup function\", 0) end");
            assign(depth + 3, args[0], 8, "slot.lo, slot.hi");
            if (!arm)
                line(depth + 3, reg(4).lo + " -= 32");
            callPrologue(depth + 3, 4294967295);
            line(depth + 3, "runGuestRoutine(callback, 4294967295)");
            if (!arm)
                line(depth + 3, reg(4).lo + " += 32");
            line(depth + 2, "end");
            assign(depth + 2, 0, 4, "1");
        }
        line(depth + 1, "end");
        line(depth, "end");
    }

    bool emitWindowsImport(unsigned depth, const GuestImport& import) {
        auto library = std::string(import.library);
        for (auto& ch : library)
            if (ch >= 'A' && ch <= 'Z')
                ch += 'a' - 'A';
        if (library != "kernel32.dll" && library != "kernelbase.dll" &&
            !library.starts_with("api-ms-win-core-heap-"))
            return false;

        const auto name = import.name;
        if (name == "EncodePointer" || name == "DecodePointer") {
            const auto pointer = reg(argumentRegisters(arm, convention)[0]);
            assign(depth, 0, 8, std::format("bit32.bxor({}, 0xa5a55a5a), bit32.bxor({}, 0x5a5aa5a5)",
                pointer.lo, pointer.hi));
            return true;
        }
        if (name == "LoadLibraryExW") {
            // PE imports are resolved at translation time. This guest has no optional dynamic DLLs.
            usesLastError = true;
            line(depth, "lastError = 126");
            assign(depth, 0, 8, "0, 0");
            return true;
        }
        if (name == "VirtualProtect") {
            needsMemory = true;
            usesLastError = true;
            const auto args = argumentRegisters(arm, convention);
            assign(depth, 0, 4, std::format("protectMemory({}, {}, {}, {})",
                reg(args[0]).pair(), reg(args[1]).pair(), reg(args[2]).lo, reg(args[3]).pair()));
            line(depth, "if " + reg(0).lo + " == 0 then lastError = 87 end");
            return true;
        }
        if (name == "FlsAlloc" || name == "FlsGetValue" || name == "FlsSetValue" || name == "FlsFree") {
            emitFiberImport(depth, name);
            return true;
        }
        if (name == "GetLastError" || name == "SetLastError") {
            usesLastError = true;
            if (name == "GetLastError")
                assign(depth, 0, 4, "lastError");
            else
                line(depth, "lastError = " + reg(argumentRegisters(arm, convention)[0]).lo);
            return true;
        }
        if (name == "SetUnhandledExceptionFilter") {
            usesExceptionFilter = true;
            const auto handler = reg(argumentRegisters(arm, convention)[0]);
            const auto result = reg(0);
            line(depth, std::format("{}, exceptionFilterLo, exceptionFilterHi = exceptionFilterLo, exceptionFilterHi, {}",
                result.pair(), handler.pair()));
            return true;
        }
        if (name == "GetProcessHeap") {
            assign(depth, 0, 8, "0xffeeffe0, 0");
            return true;
        }
        if (name == "AcquireSRWLockExclusive" || name == "AcquireSRWLockShared" ||
            name == "TryAcquireSRWLockExclusive" || name == "TryAcquireSRWLockShared" ||
            name == "ReleaseSRWLockExclusive" || name == "ReleaseSRWLockShared" || name == "InitializeSRWLock") {
            needsMemory = true;
            const auto pointer = reg(argumentRegisters(arm, convention)[0]);
            const auto op = name.starts_with("Release") ? "release" : name.starts_with("Try") ? "try" :
                name == "InitializeSRWLock" ? "initialize" : "acquire";
            const auto call = std::format("srwLock({}, {}, {})", quoted(op), name.ends_with("Shared"), pointer.pair());
            if (name.starts_with("Try"))
                assign(depth, 0, 4, call);
            else
                line(depth, call);
            return true;
        }
        if (name == "WakeAllConditionVariable" || name == "WakeConditionVariable") {
            // There are no waiters in the single-threaded guest.
            needsMemory = true;
            line(depth, "do local _ = read(1, address(" + reg(argumentRegisters(arm, convention)[0]).pair() + ")) end");
            return true;
        }
        if (name == "InitializeCriticalSection" || name == "InitializeCriticalSectionEx" ||
            name == "InitializeCriticalSectionAndSpinCount" || name == "EnterCriticalSection" ||
            name == "TryEnterCriticalSection" || name == "LeaveCriticalSection" || name == "DeleteCriticalSection") {
            needsMemory = true;
            const auto args = argumentRegisters(arm, convention);
            const auto operation = name.starts_with("Initialize") ? "initialize" :
                name == "DeleteCriticalSection" ? "delete" : name == "LeaveCriticalSection" ? "leave" : "enter";
            const auto flags = name == "InitializeCriticalSectionEx" ? reg(args[2]).lo : "0";
            const auto call = std::format("criticalSection({}, {}, {})", quoted(operation), reg(args[0]).pair(), flags);
            if (name == "InitializeCriticalSectionEx" || name == "InitializeCriticalSectionAndSpinCount" ||
                name == "TryEnterCriticalSection")
                assign(depth, 0, 8, call);
            else
                line(depth, call);
            return true;
        }
        if (name != "HeapAlloc" && name != "HeapReAlloc" && name != "HeapFree" && name != "HeapSize")
            return false;
        needsMemory = true;
        needsHeap = true;
        const auto arguments = argumentRegisters(arm, convention);
        const auto size = name == "HeapReAlloc" ? ", " + reg(arguments[3]).pair() : "";
        assign(depth, 0, 8, std::format("processHeap({}, {}, {}, {}{})", quoted(name),
            reg(arguments[0]).pair(), reg(arguments[1]).lo, reg(arguments[2]).pair(), size));
        return true;
    }

    bool emitImport(unsigned depth, const GuestImport& import) {
        if (convention == CallingConvention::Microsoft)
            return emitWindowsImport(depth, import);
        const auto name = importName(import);
        const auto arguments = argumentRegisters(arm, convention);
        if (!arm && !import.leadingUnderscore && name == "__tls_get_addr") {
            std::string valid;
            for (const auto& region : data.regions) {
                if (!region.threadLocal)
                    continue;
                const auto size = region.end - region.start;
                if (!data.emitted.contains(region.start))
                    data.materialize(region.start, unsigned(size));
                if (!valid.empty())
                    valid += " or ";
                valid += std::format("(base == {} and offset < {})", region.start, size);
            }
            if (valid.empty())
                return false;
            needsMemory = true;
            line(depth, "do");
            line(depth + 1, "local descriptor = address(" + reg(arguments[0]).pair() + ")");
            line(depth + 1, "local base = address(read(8, descriptor))");
            line(depth + 1, "local offset = address(read(8, descriptor + 8))");
            line(depth + 1, "if not (" + valid + ") then error(\"invalid guest ELF TLS descriptor\", 0) end");
            assign(depth + 1, 0, 8, "base + offset, 0");
            line(depth, "end");
            return true;
        }
        if (name == "memchr" || name == "wmemchr") {
            needsMemory = true;
            const bool wide = name == "wmemchr";
            line(depth, "do");
            line(depth + 1, "local first = address(" + reg(arguments[0]).pair() + ")");
            line(depth + 1, "local count = address(" + reg(arguments[2]).pair() + ")");
            const auto byte = reg(arguments[1]).lo;
            line(depth + 1, "local needle = " + (wide ? byte : "bit32.band(" + byte + ", 255)"));
            line(depth + 1, "local found = 0");
            line(depth + 1, "for i = 0, count - 1 do");
            line(depth + 2, std::format("local at = first + i * {}", wide ? 4 : 1));
            line(depth + 2, std::format("if read({}, at) == needle then found = at; break end", wide ? 4 : 1));
            line(depth + 1, "end");
            assign(depth + 1, 0, 8, "found, 0");
            line(depth, "end");
            return true;
        }
        if (name == "pthread_mutex_lock" || name == "pthread_mutex_unlock" || name == "pthread_mutex_trylock") {
            needsMemory = true;
            assign(depth, 0, 4, std::format("pthreadMutex({}, {})", quoted(name), reg(arguments[0]).pair()));
            return true;
        }
        if (name == "pthread_cond_broadcast" || name == "pthread_cond_signal") {
            // There are no waiters in the single-threaded guest.
            needsMemory = true;
            line(depth, "do local _ = read(1, address(" + reg(arguments[0]).pair() + ")) end");
            assign(depth, 0, 4, "0");
            return true;
        }
        if (!import.leadingUnderscore && (name == "__newlocale" || name == "newlocale")) {
            needsMemory = true;
            needsHeap = true;
            line(depth, "do");
            line(depth + 1, "local label = address(" + reg(arguments[1]).pair() + ")");
            line(depth + 1, "if label == 0 then error(\"missing guest locale name\", 0) end");
            line(depth + 1, "local size = stringLength(label, 0)");
            line(depth + 1, "local first = read(1, label)");
            line(depth + 1, "if size ~= 0 and (size ~= 1 or first ~= 67) and (size ~= 5 or first ~= 80 or "
                "read(1, label + 1) ~= 79 or read(1, label + 2) ~= 83 or read(1, label + 3) ~= 73 or read(1, label + 4) ~= 88) then");
            line(depth + 2, "error(\"only the C locale is available to the guest\", 0)");
            line(depth + 1, "end");
            assign(depth + 1, 0, 8, "cLocale()");
            line(depth, "end");
            return true;
        }
        if (!import.leadingUnderscore && (name == "__duplocale" || name == "duplocale" ||
            name == "__freelocale" || name == "freelocale")) {
            needsMemory = true;
            needsHeap = true;
            const auto locale = reg(arguments[0]);
            line(depth, "if " + locale.lo + " ~= cLocale() or " + locale.hi +
                " ~= 0 then error(\"unsupported guest locale object\", 0) end");
            if (name.ends_with("duplocale"))
                assign(depth, 0, 8, "cLocale()");
            return true;
        }
        if (!import.leadingUnderscore && (name == "__uselocale" || name == "uselocale")) {
            needsMemory = true;
            needsHeap = true;
            assign(depth, 0, 8, "useCLocale(" + reg(arguments[0]).pair() + ")");
            return true;
        }
        if (!import.leadingUnderscore && (name == "wctob" || name == "btowc")) {
            const auto input = reg(arguments[0]);
            assign(depth, 0, 4, std::format("if {} < 128 then {} else 4294967295", input.lo, input.lo));
            return true;
        }
        if (!import.leadingUnderscore && (name == "__wctype_l" || name == "wctype_l")) {
            needsMemory = true;
            assign(depth, 0, 8, "wideClass(" + reg(arguments[0]).pair() + ")");
            return true;
        }
        if (!import.leadingUnderscore && (name == "__iswctype_l" || name == "iswctype_l")) {
            needsMemory = true;
            needsHeap = true;
            assign(depth, 0, 4, "testWideClass(" + reg(arguments[0]).lo + ", " + reg(arguments[1]).lo + ")");
            return true;
        }
        if (name == "__cxa_guard_acquire" || name == "__cxa_guard_release" || name == "__cxa_guard_abort") {
            needsMemory = true;
            line(depth, "do");
            line(depth + 1, "local guard = address(" + reg(arguments[0]).pair() + ")");
            if (name == "__cxa_guard_acquire") {
                line(depth + 1, "if read(1, guard) ~= 0 then");
                assign(depth + 2, 0, 4, "0");
                line(depth + 1, "else");
                line(depth + 2, "if read(1, guard + 1) ~= 0 then error(\"recursive guest static initialization\", 0) end");
                line(depth + 2, "write(1, guard + 1, 1, 0)");
                assign(depth + 2, 0, 4, "1");
                line(depth + 1, "end");
            } else {
                if (name == "__cxa_guard_release")
                    line(depth + 1, "write(1, guard, 1, 0)");
                line(depth + 1, "write(1, guard + 1, 0, 0)");
            }
            line(depth, "end");
            return true;
        }
        if (name == "_ZNSt3__119__shared_weak_count14__release_weakEv") {
            includeFunctionPointers();
            needsMemory = true;
            line(depth, "do");
            line(depth + 1, "local object = address(" + reg(arguments[0]).pair() + ")");
            line(depth + 1, "local lo, hi = read(8, object + 16)");
            line(depth + 1, "if lo == 0 and hi == 0 then");
            line(depth + 2, "local vtable = address(read(8, object))");
            line(depth + 2, "local callback = functionPointers[address(read(8, vtable + 32))]");
            line(depth + 2, "if not callback then error(\"unknown guest weak reference destructor\", 0) end");
            runCallback(depth + 2, "callback");
            line(depth + 1, "else");
            line(depth + 2, "lo, hi = offset(lo, hi, -1)");
            line(depth + 2, "write(8, object + 16, lo, hi)");
            line(depth + 1, "end");
            line(depth, "end");
            return true;
        }
        if (name == "pthread_once" && !import.leadingUnderscore) {
            includeFunctionPointers();
            needsMemory = true;
            line(depth, "do");
            line(depth + 1, "local control = address(" + reg(arguments[0]).pair() + ")");
            line(depth + 1, "local state = read(4, control)");
            line(depth + 1, "if state == 0 then");
            line(depth + 2, "local callback = functionPointers[address(" + reg(arguments[1]).pair() + ")]");
            line(depth + 2, "if not callback then error(\"unknown guest pthread_once callback\", 0) end");
            line(depth + 2, "write(4, control, 1, 0)");
            runCallback(depth + 2, "callback");
            line(depth + 2, "write(4, control, 2, 0)");
            line(depth + 1, "elseif bit32.band(state, 2) == 0 then");
            line(depth + 2, "error(\"recursive guest pthread_once\", 0)");
            line(depth + 1, "end");
            assign(depth + 1, 0, 4, "0");
            line(depth, "end");
            return true;
        }
        if (name == "_ZNSt3__18to_charsEPcS0_d") {
            needsMemory = true;
            needsFloating = true;
            needsDecimal = true;
            line(depth, "do");
            line(depth + 1, "local first = address(" + reg(arguments[0]).pair() + ")");
            line(depth + 1, "local last = address(" + reg(arguments[1]).pair() + ")");
            const auto bits = xmm(VectorRegister{0});
            line(depth + 1, "local text = formatDouble(" + floatOperand(VectorRegister{0}, 8, {}) +
                ", " + bits[0] + ", " + bits[1] + ")");
            line(depth + 1, "if first + #text <= last then");
            line(depth + 2, "for i = 1, #text do write(1, first + i - 1, string.byte(text, i), 0) end");
            assign(depth + 2, 0, 8, "first + #text, 0");
            assign(depth + 2, arm ? 1 : 2, 4, "0");
            line(depth + 1, "else");
            assign(depth + 2, 0, 8, "last, 0");
            assign(depth + 2, arm ? 1 : 2, 4, import.leadingUnderscore ? "84" : "75");
            line(depth + 1, "end");
            line(depth, "end");
            return true;
        }
        if (name == "__popcountdi2") {
            line(depth, "do");
            line(depth + 1, "local count = 0");
            line(depth + 1, "for _, word in {" + reg(arguments[0]).pair() + "} do");
            line(depth + 2, "word -= bit32.band(bit32.rshift(word, 1), 0x55555555)");
            line(depth + 2, "word = bit32.band(word, 0x33333333) + bit32.band(bit32.rshift(word, 2), 0x33333333)");
            line(depth + 2, "word = bit32.band(word + bit32.rshift(word, 4), 0x0f0f0f0f)");
            line(depth + 2, "count += bit32.band(word + bit32.rshift(word, 8) + bit32.rshift(word, 16) + bit32.rshift(word, 24), 63)");
            line(depth + 1, "end");
            assign(depth + 1, 0, 4, "count");
            line(depth, "end");
            return true;
        }
        if (name == "_ZNSt3__16__sortIRNS_6__lessIttEEPtEEvT0_S5_T_" ||
            name == "_ZNSt3__16__sortIRNS_6__lessIjjEEPjEEvT0_S5_T_") {
            needsMemory = true;
            const auto width = name.find("IttE") != std::string_view::npos ? 2 : 4;
            line(depth, "do");
            line(depth + 1, "local first = address(" + reg(arguments[0]).pair() + ")");
            line(depth + 1, "local last = address(" + reg(arguments[1]).pair() + ")");
            line(depth + 1, std::format("if first > last or (last - first) % {} ~= 0 then error(\"invalid guest sort range\", 0) end", width));
            line(depth + 1, "local values: {number} = {}");
            line(depth + 1, std::format("for at = first, last - {}, {} do", width, width));
            line(depth + 2, std::format("values[#values + 1] = read({}, at)", width));
            line(depth + 1, "end");
            line(depth + 1, "table.sort(values)");
            line(depth + 1, "for i, item in values do");
            line(depth + 2, std::format("write({}, first + (i - 1) * {}, item, 0)", width, width));
            line(depth + 1, "end");
            line(depth, "end");
            return true;
        }
        if (name == "_ZNSt3__112__next_primeEm") {
            needsPrime = true;
            assign(depth, 0, 8, "nextPrime(" + reg(arguments[0]).pair() + ")");
            return true;
        }
        if (name == "__cxa_atexit") {
            usesExitCallbacks = true;
            includeFunctionPointers();
            needsMemory = true;
            line(depth, "do");
            const auto argument = reg(arguments[1]);
            const auto first = reg(arguments[0]);
            line(depth + 1, std::format("local callback = functionPointers[address({})]", first.pair()));
            line(depth + 1, "if not callback then error(\"unknown guest exit callback\", 0) end");
            line(depth + 1, std::format("local argLo, argHi = {}", argument.pair()));
            line(depth + 1, "table.insert(exitCallbacks, function()");
            assign(depth + 2, arguments[0], 8, "argLo, argHi");
            callPrologue(depth + 2, 4294967295);
            line(depth + 2, "runGuestRoutine(callback, 4294967295)");
            line(depth + 1, "end)");
            assign(depth + 1, 0, 4, "0");
            line(depth, "end");
            return true;
        }
        if (name == "longjmp" || name == "_longjmp" || name == "__longjmp_chk") {
            needsJumpFrames = true;
            needsMemory = true;
            line(depth, std::format("jumpToFrame(jumpFrames, address({}), {})",
                reg(arguments[0]).pair(), reg(arguments[1]).lo));
            return true;
        }
        if (name == "strcmp") {
            needsMemory = true;
            assign(depth, 0, 8, std::format("compareStrings({}, {})",
                reg(arguments[0]).pair(), reg(arguments[1]).pair()));
            return true;
        }
        if (name == "strlen") {
            needsMemory = true;
            assign(depth, 0, 8, "stringLength(" + reg(arguments[0]).pair() + ")");
            return true;
        }
        if (name == "memcmp") {
            needsMemory = true;
            assign(depth, 0, 8, std::format("compareMemory({}, {}, {})",
                reg(arguments[0]).pair(), reg(arguments[1]).pair(), reg(arguments[2]).pair()));
            return true;
        }
        if (name == "memcpy" || name == "memmove") {
            needsMemory = true;
            assign(depth, 0, 8, std::format("copyMemory({}, {}, {})",
                reg(arguments[0]).pair(), reg(arguments[1]).pair(), reg(arguments[2]).pair()));
            return true;
        }
        if (name == "memset" || name == "bzero") {
            needsMemory = true;
            const auto dst = reg(arguments[0]);
            const auto value = reg(arguments[1]);
            if (name == "memset")
                assign(depth, 0, 8, std::format("fillMemory({}, {}, {})", dst.pair(), value.lo, reg(arguments[2]).pair()));
            else
                line(depth, std::format("fillMemory({}, 0, {})", dst.pair(), value.pair()));
            return true;
        }
        if (name == "_Znwm" || name == "_Znam" || name == "_ZnwmRKSt9nothrow_t" || name == "_ZnamRKSt9nothrow_t") {
            needsMemory = true;
            needsHeap = true;
            assign(depth, 0, 8, std::format("allocateCpp({}, {})",
                reg(arguments[0]).pair(), name == "_Znwm" || name == "_Znam"));
            return true;
        }
        if (name == "_ZdlPv" || name == "_ZdaPv" || name == "_ZdlPvm" || name == "_ZdaPvm") {
            needsMemory = true;
            needsHeap = true;
            line(depth, std::format("resize({}, 0, 0)", reg(arguments[0]).pair()));
            return true;
        }
        if (name != "realloc" && name != "free" && name != "malloc")
            return false;

        needsMemory = true;
        needsHeap = true;
        const auto first = reg(arguments[0]);
        if (name == "realloc")
            assign(depth, 0, 8, std::format("resize({}, {})", first.pair(), reg(arguments[1]).pair()));
        else if (name == "malloc")
            assign(depth, 0, 8, std::format("resize(0, 0, {})", first.pair()));
        else
            line(depth, std::format("resize({}, 0, 0)", first.pair()));
        return true;
    }

    std::optional<Address> resolveTarget(const Value& target, const Constants& constants) const {
        if (const auto* direct = std::get_if<Immediate>(&target))
            return Address(direct->value);
        if (const auto* source = std::get_if<Register>(&target))
            if (const auto value = constants[source->index]; value && graph.contains(Address(*value)))
                return Address(*value);
        return std::nullopt;
    }

    void indirect(unsigned depth, Address pc, const Value& target, const Constants& constants) {
        if (const auto* mem = std::get_if<Memory>(&target))
            if (auto at = knownAddress(mem->address, constants); at && data.unresolved(*at, 8)) {
                trap(depth, memoryError(*at, 8));
                return;
            }
        trap(depth, std::format("indirect control flow was not resolved during translation at {:#x}", pc));
    }
};

}

namespace luau {
std::string lowerModule(const ir::Graph& graph, const ir::References& references,
    Architecture architecture, std::span<const GuestExport> exports,
    std::span<const GuestRegion> regions, std::span<const GuestImport> imports,
    std::span<const GuestObject> objects, std::span<const std::size_t> initializers,
    std::span<const std::uint8_t> image, std::span<const ir::CodeRange> code, CallingConvention convention) {
    const bool arm = architecture == Architecture::Arm64;
    const auto loops = recoverLoops(graph);
    Data data{image, regions, imports, code, objects, {}};
    for (const auto address : references.data)
        data.materializeAddress(address);
    for (const auto& table : references.tables)
        if (!data.unresolved(table.start, unsigned(table.size)))
            data.materialize(table.start, unsigned(table.size));
    bool memory = false;
    bool flags = false;
    bool stackGuard = false;
    bool heap = false;
    bool shifts = false;
    bool division = false;
    bool multiply = false;
    bool floating = false;
    bool prime = false;
    bool structured = false;
    bool decimal = false;
    bool jumpFrames = false;
    std::map<Address, std::string> functions;
    const auto lower = [&](Address entry) {
        if (functions.contains(entry))
            return;
        if (auto direct = initializers.empty() ? lowerDirect(graph, entry, arm, convention) : std::nullopt) {
            functions.emplace(entry, std::move(*direct));
        } else {
            structured = true;
            StructuredFunction emitter(graph, references.functions, loops, data, entry, arm, convention, initializers);
            auto body = emitter.lower();
            memory |= emitter.usesMemory();
            flags |= emitter.usesFlags();
            stackGuard |= emitter.usesStackGuard();
            heap |= emitter.usesHeap();
            shifts |= emitter.usesShift();
            division |= emitter.usesDivision();
            multiply |= emitter.usesMultiply();
            floating |= emitter.usesFloating();
            prime |= emitter.usesPrime();
            decimal |= emitter.usesDecimal();
            jumpFrames |= emitter.usesJumpFrames();
            functions.emplace(entry, std::move(body));
        }
    };
    if (exports.empty())
        lower(0);
    for (const auto& entry : exports)
        lower(entry.offset);

    const RuntimeFeatures runtime{flags, shifts, division, multiply, jumpFrames, memory, stackGuard, heap, floating, prime,
        structured, decimal};
    return printModule(functions, exports, runtime, data);
}
}
