#include "lower.h"
#include "ir/analysis.h"

#include <algorithm>
#include <array>
#include <cstdlib>
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
        std::span<const std::size_t> initializers, const ProgramOptions& program)
        : graph(graph), addressTaken(addressTaken), data(data), entry(entry), arm(arm), convention(convention),
          initializers(initializers), program(program), loops(loops),
          features(withProgramStack(detectFeatures(graph, entry, arm, initializers), program)),
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
        if (!data.landingPads.empty())
            includeFunctionPointers();
        addFunction(entry);
        for (const auto pc : initializers)
            addFunction(pc);
        std::vector<std::string> bodies;
        std::set<Address> importRoutines;
        for (std::size_t i = 0;;) {
            for (; i < pending.size(); ++i) {
                const auto target = pending[i];
                body = std::format("    {} = function(expectedReturn: number): any\n", routine(target));
                active.clear();
                regionEntry = target;
                remaining = 256;
                region(target, 2, {});
                body += "    end\n";
                bodies.push_back(std::move(body));
            }
            // Imports whose addresses escape into registers become callable through function pointers.
            bool emitted = false;
            for (const auto& [token, import] : std::map(importTokens)) {
                if (!usesFunctionPointers || !importRoutines.insert(token).second)
                    continue;
                emitted = true;
                body = std::format("    {} = function(expectedReturn: number): any\n", routine(token));
                active.clear();
                tailCall = true;
                const bool emitted = emitImport(2, *import);
                tailCall = false;
                if (emitted)
                    returnFromFunction(2, arm ? Return{Register{30}} : Return{StackTop{}});
                else
                    trap(2, std::format("unsupported guest import {} called through a pointer", importName(*import)));
                body += "    end\n";
                bodies.push_back(std::move(body));
            }
            if (!emitted && i == pending.size())
                break;
        }

        const auto argumentRegs = argumentRegisters(arm, convention);
        const auto argCount = unsigned(argumentRegs.size());
        const unsigned shadowSpace = !arm && convention == CallingConvention::Microsoft ? 32 : 0;
        if (features.stack)
            reg(arm ? 31 : 4);
        if (arm && features.calls)
            reg(30);
        std::string source = std::format("    local args = readArguments({}, ...)\n", argCount);
        if (needsMemory || features.stack || !initializers.empty())
            source += std::format("    resetMemory({})\n", features.stack || !initializers.empty());
        if (usesBudget)
            source += std::format("    local budget = {}\n", program.instructionLimit ? program.instructionLimit :
                std::uint64_t(1) << 53);
        if (usesDirection)
            source += "    local direction = 1\n";
        if (usesFloatingControl)
            source += "    local mxcsr, x87Control = 0x1f80, 0x037f\n";
        if (needsJumpFrames)
            source += "    local jumpFrames: JumpFrames = {}\n";
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
            for (const auto token : importRoutines)
                source += std::format("    local {}: GuestRoutine\n", functionName(token));
        }
        if (usesFunctionPointers)
            source += "    local functionPointers: {[number]: any} = resumeRoutines\n";
        if (usesSeh)
            source += exceptionHelpers();
        source += groupRoutines(bodies);
        if (usesFunctionPointers) {
            for (const auto target : addressTaken)
                source += std::format("    functionPointers[{}] = {}\n", target, routine(target));
            for (const auto token : importRoutines)
                source += std::format("    functionPointers[{}] = {}\n", token, routine(token));
        }
        if (!initializers.empty()) {
            // Static constructors run once per module, before the first export call.
            source += "    if not process.initialized then\n        process.initialized = true\n";
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
                source += std::format("    checkUnwound(runGuestRoutine({}, 4294967295))\n", routine(pc));
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
            source += "    end\n";
        }
        if (isProgram()) {
            needsProcess = true;
            source += "    local argc, argv, envp = processArguments()\n";
            const auto args = argumentRegs;
            if (program.startup == Startup::ElfStack) {
                // _start finds argc, argv, and envp on the initial stack and never returns.
                const auto sp = reg(arm ? 31 : 4);
                source += std::format("    {} = processStack(stackTop, argc, argv, envp), 0\n", sp.pair());
                source += std::format("    {} = 0, 0\n", reg(arm ? 0 : 2).pair());
            } else if (program.startup == Startup::MainArguments) {
                source += std::format("    {} = argc, 0\n    {} = argv, 0\n    {} = envp, 0\n    {} = envp, 0\n",
                    reg(args[0]).pair(), reg(args[1]).pair(), reg(args[2]).pair(), reg(args[3]).pair());
            }
        }
        if (features.stack && !arm && program.startup != Startup::ElfStack) {
            const auto sp = reg(4);
            const unsigned frameSize = 8 + shadowSpace;
            source += std::format("    {} -= {}\n    write(8, {}, 4294967295, 0)\n", sp.lo, frameSize, sp.lo);
        }
        source += std::format("    checkUnwound(runGuestRoutine({}, 4294967295))\n", routine(entry));
        if (isProgram())
            source += std::format("    exitProcess({}, true)\n", result.lo);
        // Exit callbacks registered with __cxa_atexit stay queued until the guest process exits.
        source += std::format("    return {{lo = {}, hi = {}}}\n", result.lo, result.hi);
        return source;
    }

    // A Luau function holds at most 32767 child closures. Larger programs define their routines inside
    // group functions, each a child of the entry.
    std::string groupRoutines(const std::vector<std::string>& bodies) const {
        std::size_t limit = 30000, group = 16000;
        if (const auto* forced = std::getenv("LUFT_ROUTINE_GROUP"))
            limit = group = std::max<std::size_t>(1, std::strtoull(forced, nullptr, 10));
        std::string source;
        if (bodies.size() <= limit || !useRoutineTable) {
            for (const auto& body : bodies)
                source += body;
            return source;
        }
        for (std::size_t first = 0, index = 0; first < bodies.size(); first += group, ++index) {
            source += std::format("    local function defineRoutines{}()\n", index);
            for (auto i = first; i < std::min(bodies.size(), first + group); ++i)
                source += bodies[i];
            source += std::format("    end\n    defineRoutines{}()\n", index);
        }
        return source;
    }

    bool usesMemory() const { return needsMemory || features.stack; }
    bool usesFlags() const { return features.flags || needsAddFlags; }
    bool usesStackGuard() const { return needsStackGuard; }
    bool usesHeap() const { return needsHeap; }
    bool usesSehRuntime() const { return usesSeh; }
    bool usesLandingPadTable() const { return usesLandingPads; }
    bool usesShift() const { return needsShift; }
    bool usesDivision() const { return needsDivision; }
    bool usesMultiply() const { return needsMultiply; }
    bool usesFloating() const { return needsFloating; }
    bool usesPrime() const { return needsPrime; }
    bool usesDecimal() const { return needsDecimal; }
    bool usesJumpFrames() const { return needsJumpFrames; }
    bool usesVector() const { return needsVector; }
    bool usesProcess() const { return needsProcess; }
    bool usesX87() const { return needsX87; }

private:
    const Graph& graph;
    const std::set<Address>& addressTaken;
    Data& data;
    Address entry;
    bool arm;
    CallingConvention convention;
    std::span<const std::size_t> initializers;
    const ProgramOptions& program;
    const LoopExits& loops;
    Features features;

    static Features withProgramStack(Features features, const ProgramOptions& program) {
        if (program.startup != Startup::Library)
            features.stack = features.calls = true;
        return features;
    }

    bool isProgram() const { return program.startup != Startup::Library; }
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
    bool needsVector = false;
    bool needsProcess = false;
    bool needsX87 = false;
    bool tailCall = false;
    // Where the caller resumes while an import call is emitted.
    std::optional<Address> callResume;
    bool usesSeh = false;
    bool usesLandingPads = false;
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
            if (const auto* import = data.unresolved(*known, size); import && import->callable && size == 8 &&
                import->start == *known && import->size == 8) {
                // An import's address read in place, as weak references are tested, is its placeholder.
                const auto token = ImportToken + import->start;
                importTokens.emplace(Address(token), import);
                return wordLiteral(token).pair();
            }
            if ((!data.readable(*known, size) && !data.materialized(*known)) || data.unresolved(*known, size))
                return std::format("error({}, 0)", quoted(memoryError(*known, size)));
            if (data.readable(*known, size))
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
            if ((!data.readable(*at, 16) && !data.materialized(*at)) || data.unresolved(*at, 16)) {
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

    // Returns the lanes of a vector operand. Memory operands load into locals named prefix0..prefix3, so
    // callers must open a block first.
    std::optional<Lanes> operandLanes(unsigned depth, const VectorOperand& operand, const Constants& constants,
        std::string_view prefix) {
        if (const auto* reg = std::get_if<VectorRegister>(&operand))
            return xmm(*reg);
        const auto source = readVector(depth, operand, constants);
        if (!source)
            return std::nullopt;
        Lanes lanes;
        for (unsigned i = 0; i < lanes.size(); ++i)
            lanes[i] = std::format("{}{}", prefix, i);
        line(depth, "local " + joinLanes(lanes) + " = " + *source);
        return lanes;
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
                const auto lhs = binary.op == VectorOp::AndNot ? "bit32.bnot(" + lhsLanes[lane] + ")" : lhsLanes[lane];
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

    void stackPush(unsigned depth, const LuauWord& word) { stackPush(depth, word.pair()); }

    void stackPush(unsigned depth, const std::string& word) {
        const auto sp = reg(4);
        line(depth, "do");
        line(depth + 1, "local valueLo, valueHi = " + word);
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

    void effects(unsigned depth, Address pc, const Block& block, Constants& constants) {
        if (program.trace)
            line(depth, std::format("guestTrace[guestTraceAt] = {}; guestTraceAt = guestTraceAt % 32 + 1", pc));
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
                    if (const auto* import = importSlot(move.src, constants); import && move.size == 8 && move.dst != Zero) {
                        // Loading an import's address yields a placeholder that a later indirect call resolves.
                        const auto token = ImportToken + import->start;
                        importTokens.emplace(Address(token), import);
                        assign(depth, move.dst, 8, wordLiteral(token).pair());
                        constants[move.dst] = token;
                        return;
                    }
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
                    line(depth, std::format("{}, {} = {}({}, {}, {}, {})", quotient.pair(), remainder.pair(),
                        div.sign ? "signedDivide" : "unsignedDivide", div.size, quotient.pair(), remainder.pair(),
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
                    stackPush(depth, value(push.src, 8, constants));
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
                            line(depth + 1, std::format("local total = a {} b{}", subtract ? '-' : '+',
                                compare.withCarry ? std::format(" {} (if carry then 1 else 0)", subtract ? '-' : '+') : ""));
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
                        if (shift.size == 4 && !arm) {
                            // A 32-bit operation still zero-extends its destination when the count is zero.
                            line(depth + 1, "else");
                            line(depth + 2, std::format("{}, {} = {}, 0", dst.lo, dst.hi, reg(shift.src.index).lo));
                        }
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
                [&](const X87& op) {
                    needsX87 = true;
                    needsMemory = true;
                    const auto at = op.memory ? std::format("address({})", addressPair(*op.memory, constants)) :
                        std::string("0");
                    const auto call = std::format("x87Execute({}, {}, {})", op.opcode, op.modrm, at);
                    const bool compareFlags = !op.memory && (op.opcode == 0xdb || op.opcode == 0xdf) &&
                        op.modrm >= 0xe8 && op.modrm < 0xf8;
                    const bool conditional = !op.memory && (op.opcode == 0xda || op.opcode == 0xdb) && op.modrm < 0xe0;
                    if (compareFlags) {
                        if (setFlags) {
                            line(depth, "zero, parity, carry = " + call);
                            line(depth, "overflow, negative = false, false");
                        } else {
                            line(depth, call);
                        }
                    } else if (!op.memory && op.opcode == 0xdf && op.modrm == 0xe0) {
                        line(depth, std::format("{0} = bit32.replace({0}, {1}, 0, 16)", reg(0).lo, call));
                        constants[0].reset();
                    } else if (conditional) {
                        // FCMOVcc tests CF, ZF, and PF like the unsigned integer conditions.
                        constexpr std::array<std::string_view, 4> tests{"carry", "zero", "carry or zero", "parity"};
                        const auto test = std::string(tests[(op.modrm >> 3) & 3]);
                        line(depth, std::format("if {}({}) then {} end", op.opcode == 0xdb ? "not " : "", test, call));
                    } else {
                        line(depth, call);
                    }
                },
                [&](const DoubleShift& op) {
                    needsShift = true;
                    const auto dst = reg(op.dst);
                    assign(depth, op.dst, 8, std::format("doubleShift({}, {}, {}, {}, {})", op.left, op.size,
                        reg(1).lo, dst.pair(), reg(op.src.index).pair()));
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
                    if (scan.dst == Zero && !setFlags)
                        return;
                    line(depth, "do");
                    const auto input = value(scan.src, scan.size, constants);
                    line(depth + 1, scan.size == 8 ? "local lo, hi = " + input : "local lo, hi = " + input + ", 0");
                    if (scan.population || scan.counts) {
                        if (scan.population) {
                            needsShift = true;
                            line(depth + 1, "local count = sumBytes(populationByByte(lo)) + sumBytes(populationByByte(hi))");
                        } else if (scan.reverse) {
                            line(depth + 1, scan.size == 8 ? "local count = if hi ~= 0 then bit32.countlz(hi) else 32 + bit32.countlz(lo)"
                                                           : "local count = bit32.countlz(lo)");
                        } else {
                            line(depth + 1, scan.size == 8 ? "local count = if lo ~= 0 then bit32.countrz(lo) else 32 + bit32.countrz(hi)"
                                                           : "local count = bit32.countrz(lo)");
                        }
                        if (setFlags) {
                            if (scan.population)
                                line(depth + 1, "carry, overflow, negative, zero = false, false, false, count == 0");
                            else
                                line(depth + 1, "carry, zero = lo == 0 and hi == 0, count == 0");
                            if (features.parity)
                                line(depth + 1, scan.population ? "parity = false" : "parity = parity");
                        }
                        if (scan.dst != Zero)
                            assign(depth + 1, scan.dst, 4, "count");
                        line(depth, "end");
                        if (scan.dst != Zero)
                            constants[scan.dst].reset();
                        return;
                    }
                    if (scan.dst == Zero) {
                        line(depth + 1, "zero = lo == 0 and hi == 0");
                        line(depth, "end");
                        return;
                    }
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
                [&](const StringMove& move) {
                    usesDirection = true;
                    needsMemory = true;
                    const auto source = reg(6);
                    const auto target = reg(7);
                    const auto count = reg(1);
                    const auto step = std::format("direction * {}", move.size);
                    if (move.repeat) {
                        usesBudget = true;
                        line(depth, std::format("if {} ~= 0 or {} > budget then error(\"guest instruction limit exceeded\", 0) end",
                            count.hi, count.lo));
                        line(depth, "budget -= " + count.lo);
                        line(depth, "if " + count.lo + " > 0 then");
                        // Forward copies of non-overlapping ranges become one buffer copy.
                        line(depth + 1, std::format("local from, to = address({}), address({})", source.pair(), target.pair()));
                        line(depth + 1, std::format("local bytes = {} * {}", count.lo, move.size));
                        line(depth + 1, "if direction == 1 and (to + bytes <= from or from + bytes <= to) then");
                        line(depth + 2, "copyMemory(to, 0, from, 0, bytes, 0)");
                        line(depth + 2, std::format("{} = offset({}, bytes)", source.pair(), source.pair()));
                        line(depth + 2, std::format("{} = offset({}, bytes)", target.pair(), target.pair()));
                        line(depth + 1, "else");
                        line(depth + 2, "for _ = 1, " + count.lo + " do");
                        line(depth + 3, std::format("write({}, address({}), read({}, address({})))", move.size, target.pair(),
                            move.size, source.pair()));
                        line(depth + 3, std::format("{} = offset({}, {})", source.pair(), source.pair(), step));
                        line(depth + 3, std::format("{} = offset({}, {})", target.pair(), target.pair(), step));
                        line(depth + 2, "end");
                        line(depth + 1, "end");
                        line(depth, "end");
                        line(depth, count.pair() + " = 0, 0");
                        constants[1] = 0;
                    } else {
                        line(depth, std::format("write({}, address({}), read({}, address({})))", move.size, target.pair(),
                            move.size, source.pair()));
                        line(depth, std::format("{} = offset({}, {})", source.pair(), source.pair(), step));
                        line(depth, std::format("{} = offset({}, {})", target.pair(), target.pair(), step));
                    }
                    constants[6].reset();
                    constants[7].reset();
                },
                [&](const CompareExchange& exchange) {
                    if (!prepareWrite(depth, exchange.address, exchange.size, constants))
                        return;
                    needsAddFlags = true;
                    const auto accumulator = reg(0);
                    const auto source = reg(exchange.src.index);
                    line(depth, "do");
                    line(depth + 1, "local at = address(" + addressPair(exchange.address, constants) + ")");
                    line(depth + 1, std::format("local oldLo, oldHi = read({}, at)", exchange.size));
                    line(depth + 1, std::format("local _, _, c, o, n, z = addFlags(true, false, {}, {}, oldLo, oldHi)",
                        exchange.size, exchange.size == 8 ? accumulator.pair() : accumulator.lo + ", 0"));
                    if (setFlags) {
                        line(depth + 1, "carry, overflow, negative, zero = c, o, n, z");
                        if (features.parity)
                            line(depth + 1, std::format("parity = evenParity(({} - oldLo) % 256)", accumulator.lo));
                    }
                    line(depth + 1, "if z then");
                    line(depth + 2, std::format("write({}, at, {})", exchange.size,
                        exchange.size == 8 ? source.pair() : source.lo + ", 0"));
                    line(depth + 1, "else");
                    assign(depth + 2, 0, exchange.size, exchange.size == 8 ? "oldLo, oldHi" : "oldLo");
                    line(depth + 1, "end");
                    line(depth, "end");
                    constants[0].reset();
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
                            const auto low = move.size >= 4 ? lanes[0] :
                                std::format("bit32.extract({}, 0, {})", lanes[0], move.size * 8);
                            source = low + ", " + (move.size == 8 ? lanes[1] : "0");
                        } else {
                            source = read(std::get<VectorMemory>(move.src).address, move.size, constants);
                            if (move.size < 8)
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
                    const auto bits = transfer.size * 8;
                    const auto offset = transfer.lane.value_or(0) * bits;
                    if (transfer.lane && transfer.toXmm) {
                        const auto first = offset / 32;
                        if (transfer.size == 8)
                            line(depth, lanes[first] + ", " + lanes[first + 1] + " = " + gp.pair());
                        else if (transfer.size == 4)
                            line(depth, lanes[first] + " = " + gp.lo);
                        else
                            line(depth, std::format("{0} = bit32.replace({0}, {1}, {2}, {3})", lanes[first], gp.lo,
                                offset % 32, bits));
                    } else if (transfer.toXmm) {
                        const auto words = transfer.size == 8 ? gp.pair() : gp.lo + ", 0";
                        line(depth, joinLanes(lanes) + " = " + words + ", 0, 0");
                    } else if (transfer.lane && transfer.gp.index != Zero) {
                        const auto first = offset / 32;
                        if (transfer.size == 8)
                            assign(depth, transfer.gp.index, 8, lanes[first] + ", " + lanes[first + 1]);
                        else if (transfer.size == 4)
                            assign(depth, transfer.gp.index, 4, lanes[first]);
                        else
                            assign(depth, transfer.gp.index, 4,
                                std::format("bit32.extract({}, {}, {})", lanes[first], offset % 32, bits));
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
                    line(depth + 1, "local lhs = " + floatOperand(op.lhs.value_or(op.dst), op.size, constants));
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
                    auto converted = std::format("integerAsFloat({}, {}, {}, {})", op.integerSize, op.size, op.sign, words);
                    if (op.fractionBits)
                        converted = std::format("{} / {}", converted, std::uint64_t(1) << op.fractionBits);
                    writeFloat(depth, op.dst, op.size, converted);
                },
                [&](const FloatToInteger& op) {
                    needsFloating = true;
                    auto input = floatOperand(op.src, op.floatSize, constants);
                    if (op.fractionBits)
                        input = std::format("{} * {}", input, std::uint64_t(1) << op.fractionBits);
                    if (op.rounding == Rounding::NearestEven || op.rounding == Rounding::Away)
                        needsVector = true;
                    if (op.rounding != Rounding::Truncate)
                        input = std::string(op.rounding == Rounding::Up ? "math.ceil(" : op.rounding == Rounding::Down ?
                            "math.floor(" : op.rounding == Rounding::NearestEven ? "roundEven(" : "roundAway(") + input + ")";
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
                [&](const VectorLanes& op) {
                    needsVector = true;
                    line(depth, "do");
                    if (const auto rhs = operandLanes(depth + 1, op.rhs, constants, "rhs")) {
                        const auto lhs = op.lhs ? xmm(*op.lhs) : xmm(op.dst);
                        line(depth + 1, std::format("{} = laneOperation({}, {}, {}, {}, {})", joinLanes(xmm(op.dst)),
                            unsigned(op.op), op.element, op.size, joinLanes(lhs), joinLanes(*rhs)));
                    }
                    line(depth, "end");
                },
                [&](const VectorFloatLanes& op) {
                    needsVector = true;
                    line(depth, "do");
                    if (auto rhs = operandLanes(depth + 1, op.rhs, constants, "rhs")) {
                        if (op.rhsLane) {
                            const auto source = *rhs;
                            for (unsigned i = 0; i < 4; ++i)
                                (*rhs)[i] = op.element == 4 ? source[*op.rhsLane] : source[*op.rhsLane * 2 + i % 2];
                        }
                        const auto lhs = op.lhs ? xmm(*op.lhs) : xmm(op.dst);
                        line(depth + 1, std::format("{} = vectorFloatLanes({}, {}, {}, {}, {})", joinLanes(xmm(op.dst)),
                            unsigned(op.op), op.element, op.size, joinLanes(lhs), joinLanes(*rhs)));
                    }
                    line(depth, "end");
                },
                [&](const VectorShiftLanes& op) {
                    needsVector = true;
                    line(depth, "do");
                    std::string count = std::to_string(op.count);
                    if (op.countOperand) {
                        const auto lanes = operandLanes(depth + 1, *op.countOperand, constants, "count");
                        if (!lanes) {
                            line(depth, "end");
                            return;
                        }
                        count = std::format("if {} ~= 0 or {} > 255 then 255 else {}", (*lanes)[1], (*lanes)[0], (*lanes)[0]);
                    }
                    line(depth + 1, std::format("{} = vectorShift({}, {}, {}, {}, {})", joinLanes(xmm(op.dst)),
                        unsigned(op.op), op.element, op.size, count, joinLanes(xmm(op.src))));
                    line(depth, "end");
                },
                [&](const VectorPermute& op) {
                    line(depth, "do");
                    const auto first = operandLanes(depth + 1, op.first, constants, "first");
                    const auto second = first ? operandLanes(depth + 1, op.second, constants, "second") : std::nullopt;
                    if (first && second) {
                        const auto previous = xmm(op.dst);
                        const auto source = [&](unsigned index) -> const Lanes& {
                            return index < 16 ? *first : index < 32 ? *second : previous;
                        };
                        Lanes result;
                        for (unsigned lane = 0; lane < 4; ++lane) {
                            const auto* bytes = &op.bytes[lane * 4];
                            const auto start = bytes[0];
                            const bool whole = start != 255 && start % 4 == 0 && bytes[1] == start + 1 &&
                                bytes[2] == start + 2 && bytes[3] == start + 3;
                            if (whole) {
                                result[lane] = source(start)[(start % 16) / 4];
                                continue;
                            }
                            std::vector<std::string> parts;
                            for (unsigned k = 0; k < 4;) {
                                const auto index = bytes[k];
                                if (index == 255) {
                                    ++k;
                                    continue;
                                }
                                const auto& word = source(index)[(index % 16) / 4];
                                const bool half = k % 2 == 0 && index % 2 == 0 && bytes[k + 1] == index + 1;
                                const auto width = half ? 16u : 8u;
                                auto part = std::format("bit32.extract({}, {}, {})", word, (index % 4) * 8, width);
                                if (k)
                                    part = std::format("bit32.lshift({}, {})", part, k * 8);
                                parts.push_back(part);
                                k += half ? 2 : 1;
                            }
                            if (parts.empty())
                                result[lane] = "0";
                            else if (parts.size() == 1)
                                result[lane] = parts.front();
                            else {
                                result[lane] = "bit32.bor(" + parts.front();
                                for (std::size_t i = 1; i < parts.size(); ++i)
                                    result[lane] += ", " + parts[i];
                                result[lane] += ")";
                            }
                        }
                        line(depth + 1, joinLanes(previous) + " = " + joinLanes(result));
                    }
                    line(depth, "end");
                },
                [&](const VectorConvert& op) {
                    needsVector = true;
                    line(depth, "do");
                    if (const auto src = operandLanes(depth + 1, op.src, constants, "source")) {
                        const auto dst = xmm(op.dst);
                        line(depth + 1, std::format("{} = vectorConvert({}, {}, {}, {}, {}, {}, {})", joinLanes(dst),
                            unsigned(op.kind), op.element, op.upper, op.shift, op.size, joinLanes(dst), joinLanes(*src)));
                    }
                    line(depth, "end");
                },
                [&](const VectorReduce& op) {
                    needsVector = true;
                    const auto call = std::format("vectorReduce({}, {}, {}, {})", unsigned(op.op), op.element, op.size,
                        joinLanes(xmm(op.src)));
                    if (op.op == ReduceOp::SignMask) {
                        if (op.gp != Zero) {
                            assign(depth, op.gp, 4, "(" + call + ")");
                            constants[op.gp].reset();
                        }
                    } else {
                        const auto dst = xmm(op.dst);
                        line(depth, "do");
                        line(depth + 1, "local lo, hi = " + call);
                        line(depth + 1, joinLanes(dst) + " = lo, hi, 0, 0");
                        line(depth, "end");
                    }
                },
                [&](const VectorBlend& op) {
                    line(depth, "do");
                    const auto yes = operandLanes(depth + 1, op.yes, constants, "yes");
                    const auto no = yes ? operandLanes(depth + 1, op.no, constants, "no") : std::nullopt;
                    if (yes && no) {
                        const auto mask = xmm(op.mask);
                        Lanes result;
                        for (unsigned lane = 0; lane < 4; ++lane) {
                            auto bits = mask[lane];
                            if (op.laneSign) {
                                const auto top = op.element == 8 ? mask[lane | 1] : mask[lane];
                                bits = "(if " + top + " >= 2147483648 then 4294967295 else 0)";
                            }
                            result[lane] = std::format("bit32.bor(bit32.band({0}, {1}), bit32.band(bit32.bnot({0}), {2}))",
                                bits, (*yes)[lane], (*no)[lane]);
                        }
                        line(depth + 1, joinLanes(xmm(op.dst)) + " = " + joinLanes(result));
                    }
                    line(depth, "end");
                },
                [&](const ScalarFloat& op) {
                    const auto dst = xmm(op.dst);
                    line(depth, "do");
                    const auto src = operandLanes(depth + 1, op.src, constants, "source");
                    if (!src) {
                        line(depth, "end");
                        return;
                    }
                    const auto top = op.size == 8 ? 1u : 0u;
                    if (op.op == ScalarFloatOp::Negate) {
                        if (op.size == 8)
                            line(depth + 1, std::format("{}, {} = {}, bit32.bxor({}, 0x80000000)", dst[0], dst[1], (*src)[0], (*src)[1]));
                        else
                            line(depth + 1, std::format("{} = bit32.bxor({}, 0x80000000)", dst[0], (*src)[0]));
                    } else {
                        needsFloating = true;
                        needsVector = true;
                        const auto value = std::format("decodeFloat({}, {}, {})", op.size, (*src)[0], op.size == 8 ? (*src)[1] : "0");
                        const auto lhs = op.lhs ? xmm(*op.lhs) : dst;
                        const auto other = std::format("decodeFloat({}, {}, {})", op.size, lhs[0], op.size == 8 ? lhs[1] : "0");
                        std::string result;
                        switch (op.op) {
                            case ScalarFloatOp::RoundNearestEven: result = "roundEven(" + value + ")"; break;
                            case ScalarFloatOp::RoundAway: result = "roundAway(" + value + ")"; break;
                            case ScalarFloatOp::Floor: result = "math.floor(" + value + ")"; break;
                            case ScalarFloatOp::Ceil: result = "math.ceil(" + value + ")"; break;
                            case ScalarFloatOp::Truncate: result = "roundTruncate(" + value + ")"; break;
                            case ScalarFloatOp::NegateMultiply: result = "-(" + other + " * " + value + ")"; break;
                            default:
                                result = std::format("scalarMinMax({}, {}, {})", unsigned(op.op) - unsigned(ScalarFloatOp::MinNumber),
                                    other, value);
                                break;
                        }
                        const auto fields = op.size == 8 ? dst[0] + ", " + dst[1] : dst[0];
                        line(depth + 1, std::format("{} = encodeFloat({}, {})", fields, op.size, result));
                    }
                    if (op.clearUpper) {
                        for (unsigned lane = top + 1; lane < 4; ++lane)
                            line(depth + 1, dst[lane] + " = 0");
                    }
                    line(depth, "end");
                },
                [&](const FusedMultiply& op) {
                    needsFloating = true;
                    const auto lanes = [&](VectorRegister reg) {
                        const auto words = xmm(reg);
                        return std::format("decodeFloat({}, {}, {})", op.size, words[0], op.size == 8 ? words[1] : "0");
                    };
                    const auto dst = xmm(op.dst);
                    const auto fields = op.size == 8 ? dst[0] + ", " + dst[1] : dst[0];
                    line(depth, std::format("{} = encodeFloat({}, {}{} * {} {} {})", fields, op.size, op.negateProduct ? "-" : "",
                        lanes(op.a), lanes(op.b), op.negateAddend ? '-' : '+', lanes(op.c)));
                    if (op.clearUpper)
                        for (unsigned lane = op.size == 8 ? 2 : 1; lane < 4; ++lane)
                            line(depth, dst[lane] + " = 0");
                },
                [&](const FloatSelect& op) {
                    const auto dst = xmm(op.dst);
                    const auto yes = xmm(op.yes);
                    const auto no = xmm(op.no);
                    const auto count = op.size == 8 ? 2u : 1u;
                    std::string chosen;
                    for (unsigned lane = 0; lane < 4; ++lane) {
                        if (lane)
                            chosen += ", ";
                        chosen += lane < count ? std::format("if {} then {} else {}", ArmConditions[op.condition], yes[lane], no[lane]) : "0";
                    }
                    line(depth, joinLanes(dst) + " = " + chosen);
                },
                [&](const FloatConditionalCompare& op) {
                    if (!setFlags)
                        return;
                    needsFloating = true;
                    line(depth, std::format("if {} then", ArmConditions[op.condition]));
                    line(depth + 1, "local lhs = " + floatOperand(op.lhs, op.size, constants));
                    line(depth + 1, "local rhs = " + (op.rhs ? floatOperand(*op.rhs, op.size, constants) : std::string("0")));
                    line(depth + 1, "carry, zero, overflow, negative = not (lhs < rhs), lhs == rhs, lhs ~= lhs or rhs ~= rhs, lhs < rhs");
                    line(depth, "else");
                    line(depth + 1, std::format("carry, overflow, negative, zero = {}, {}, {}, {}",
                        bool(op.otherwise & 2), bool(op.otherwise & 1), bool(op.otherwise & 8), bool(op.otherwise & 4)));
                    line(depth, "end");
                },
                [&](const VectorLaneMove& op) {
                    const auto dst = xmm(op.dst);
                    const auto src = xmm(op.src);
                    if (op.element >= 4) {
                        const auto words = op.element / 4;
                        for (unsigned i = 0; i < words; ++i)
                            line(depth, std::format("{} = {}", dst[op.dstLane * words + i], src[op.srcLane * words + i]));
                        return;
                    }
                    const auto bits = op.element * 8;
                    const auto from = op.srcLane * bits;
                    const auto to = op.dstLane * bits;
                    line(depth, std::format("{0} = bit32.replace({0}, bit32.extract({1}, {2}, {3}), {4}, {3})", dst[to / 32],
                        src[from / 32], from % 32, bits, to % 32));
                },
                [&](const VectorLaneLoad& op) {
                    const auto dst = xmm(op.dst);
                    const auto value = read(op.address, op.element, constants);
                    line(depth, "do");
                    if (op.element == 8)
                        line(depth + 1, "local lo, hi = " + value);
                    else
                        line(depth + 1, "local lo, hi = " + value + ", 0");
                    if (op.replicate) {
                        Lanes result{"0", "0", "0", "0"};
                        for (unsigned lane = 0; lane < op.size / 4; ++lane) {
                            result[lane] = op.element == 8 ? (lane % 2 ? "hi" : "lo") : op.element == 4 ? "lo" :
                                op.element == 2 ? "lo * 65537" : "lo * 16843009";
                        }
                        line(depth + 1, joinLanes(dst) + " = " + joinLanes(result));
                    } else if (op.element >= 4) {
                        const auto words = op.element / 4;
                        line(depth + 1, dst[op.lane * words] + " = lo");
                        if (words == 2)
                            line(depth + 1, dst[op.lane * 2 + 1] + " = hi");
                    } else {
                        const auto bits = op.element * 8;
                        const auto at = op.lane * bits;
                        line(depth + 1, std::format("{0} = bit32.replace({0}, lo, {1}, {2})", dst[at / 32], at % 32, bits));
                    }
                    line(depth, "end");
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
        if (!program.instructionLimit)
            return;
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
                effects(depth + 1, pc, block, loopConstants);
                const auto expression = condition(branch->condition);
                line(depth + 1, std::format("if {} then break end", taken ? "not (" + expression + ")" : expression));
                if (count)
                    tick(depth + 1, count);
                for (const auto address : loop)
                    effects(depth + 1, address, graph.at(address), loopConstants);
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
            effects(depth + 1, pc, block, loop);
            line(depth, "end");
            active.erase(pc);
            return;
        }
        effects(depth, pc, block, constants);
        if (target) {
            const auto* imported = arm ? findImport(Immediate{std::uint64_t(*target)}, constants, true) : nullptr;
            if (imported && tailImport(depth, *imported))
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
            if ((convention != CallingConvention::Microsoft || (imported && runtimeLibrary(imported->library))) &&
                (name == "_setjmp" || name == "setjmp" || name == "_setjmpex" || name == "__sigsetjmp" || name == "sigsetjmp")) {
                emitSetjmp(depth, call->resume);
            } else if (callResume = call->resume; imported && emitImport(depth, *imported)) {
                callResume.reset();
                region(call->resume, depth, {});
            } else if (const auto callee = resolveTarget(call->target, constants)) {
                addFunction(*callee);
                callPrologue(depth, call->resume);
                callRoutine(depth, routine(*callee), call->resume);
                region(call->resume, depth, {});
            } else if (callResume = call->resume; emitImport(depth, call->target, constants)) {
                callResume.reset();
                region(call->resume, depth, {});
            } else if (const auto* direct = findImport(call->target, constants)) {
                trap(depth, std::format("unsupported guest import {} called at {:#x}", importName(*direct), pc));
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
            else if (tailImport(depth, jump->target, constants))
                returnFromFunction(depth, arm ? Return{Register{30}} : Return{StackTop{}});
            else if (const auto* direct = findImport(jump->target, constants))
                trap(depth, std::format("unsupported guest import {} called at {:#x}", importName(*direct), pc));
            else if (!addressTaken.empty() && (std::holds_alternative<Register>(jump->target) ||
                (std::holds_alternative<Memory>(jump->target) && !findImport(jump->target, constants, true)))) {
                includeFunctionPointers();
                needsMemory = true;
                line(depth, std::format("local target = address({})", value(jump->target, 8, constants)));
                if (!data.landingPads.empty() && convention != CallingConvention::Microsoft) {
                    // libgcc's unwinder resumes a landing pad with an indirect jump from the frame's stack.
                    usesLandingPads = true;
                    line(depth, std::format("if landingPads[target] then unwindStack = {} return target end",
                        reg(arm ? 31 : 4).lo));
                }
                line(depth, "local callee = functionPointers[target]");
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

    // Calls a routine for a guest call that resumes at `resume`. Unwinding past this frame returns the
    // target address from the enclosing routine.
    void callRoutine(unsigned depth, std::string_view callee, Address resume) {
        // The frame's stack pointer once the call returns identifies it to unwinders.
        const auto frameStack = arm ? reg(31).lo : reg(4).lo + " + 8";
        line(depth, std::format("do local unwound = runGuestRoutine({}, {}, {}) if unwound then return unwound end end",
            callee, resume, frameStack));
    }

    // Runs a guest callback from emulated library code. Inside a routine body, unwinding past the callback
    // continues outward; inside a Luau closure it cannot, so it fails.
    void runCallback(unsigned depth, std::string_view callback, bool propagate = false) {
        if (arm)
            line(depth, "local linkLo, linkHi = " + reg(30).pair());
        callPrologue(depth, 4294967295);
        if (propagate)
            line(depth, std::format("do local unwound = runGuestRoutine({}, 4294967295) if unwound then return unwound end end",
                callback));
        else
            line(depth, std::format("checkUnwound(runGuestRoutine({}, 4294967295))", callback));
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
        callRoutine(depth + 1, "callee", resume);
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
        line(depth + 1, "local escaped: number? = nil");
        line(depth + 1, std::format("protectJump(jumpFrames, address({}), function(jumpValue: number): ()",
            environment.pair()));
        assign(depth + 2, 0, 8, "jumpValue, 0");
        line(depth + 2, "local function resumeRoutine(expectedReturn: number): any");
        region(resume, depth + 3, {});
        line(depth + 2, "end");
        line(depth + 2, "escaped = runGuestRoutine(resumeRoutine, expectedReturn)");
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
        line(depth + 1, "return escaped");
        line(depth, "end");
    }

    void returnFromFunction(unsigned depth, const Return& ret) {
        // A return elsewhere, such as an unwinder's return to a landing pad, resumes the frame that owns the
        // stack pointer.
        const auto unwind = [&](const std::string& lo, const std::string& hi) {
            line(depth, std::format("if {} ~= expectedReturn or {} ~= 0 then", lo, hi));
            line(depth + 1, std::format("if {} ~= 0 then error(\"guest returned to an address outside guest memory\", 0) end", hi));
            line(depth + 1, std::format("unwindStack = {}", reg(arm ? 31 : 4).lo));
            line(depth + 1, "return " + lo);
            line(depth, "end");
        };
        if (arm) {
            const auto value = reg(std::get<Register>(ret.target).index);
            unwind(value.lo, value.hi);
        } else if (features.stack) {
            stackPop(depth);
            if (ret.stackAdjust) {
                const auto sp = reg(4);
                line(depth, std::format("{} = offset({}, {})", sp.pair(), sp.pair(), ret.stackAdjust));
            }
            unwind("savedLo", "savedHi");
        }
        line(depth, "return nil");
    }

    // Placeholder addresses for imports loaded into registers. They lie above all guest memory, and calls
    // through them reach generated routines that perform the import.
    static constexpr std::uint64_t ImportToken = 0xf0000000ull;
    std::map<Address, const GuestImport*> importTokens;

    const GuestImport* importSlot(const Value& source, const Constants& constants) const {
        const auto* memory = std::get_if<Memory>(&source);
        const auto address = memory ? knownAddress(memory->address, constants) : std::nullopt;
        const auto* import = address ? data.unresolved(*address, 8) : nullptr;
        if (!import || !import->callable || import->start != *address || import->size != 8)
            return nullptr;
        return import;
    }

    const GuestImport* findImport(const Value& target, const Constants& constants, bool throughThunk = false) const {
        if (const auto* source = std::get_if<Register>(&target)) {
            if (const auto value = constants[source->index]; value && *value >= ImportToken &&
                *value < ImportToken + MaxExecutableSize) {
                const auto slot = *value - ImportToken;
                const auto* import = data.unresolved(slot, 8);
                if (import && import->start == slot && import->callable)
                    return import;
            }
        }
        if (arm) {
            if (!throughThunk)
                return nullptr;
            const auto address = resolveTarget(target, constants);
            if (!address || !graph.contains(*address))
                return nullptr;
            const auto& block = graph.at(*address);
            if (block.effects.size() != 2 && block.effects.size() != 3)
                return nullptr;
            if (block.effects.size() == 3) {
                const auto* add = std::get_if<Binary>(&block.effects[2]);
                if (!add || add->op != BinaryOp::Add || add->flags || add->count || !std::holds_alternative<Immediate>(add->rhs))
                    return nullptr;
            }
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

    // A jump to an import is a tail call: on x86-64 the return address is already on the stack, so stack
    // arguments start one word higher than at a call.
    bool tailImport(unsigned depth, const GuestImport& import) {
        tailCall = true;
        const bool emitted = emitImport(depth, import);
        tailCall = false;
        return emitted;
    }

    bool tailImport(unsigned depth, const Value& target, const Constants& constants) {
        const auto* import = findImport(target, constants);
        return import && tailImport(depth, *import);
    }

    // The guest stack pointer as an address where the import's stack arguments begin.
    std::string argumentStack() {
        const auto sp = std::format("address({})", reg(arm ? 31 : 4).pair());
        return tailCall && !arm ? sp + " + 8" : sp;
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
            line(depth, std::format("process.fiberSlots[process.fiberNext] = {{lo = 0, hi = 0, callbackLo = {}, callbackHi = {}}}",
                index.lo, index.hi));
            assign(depth, 0, 4, "process.fiberNext");
            line(depth, "process.fiberNext += 1");
            return;
        }
        line(depth, "do");
        line(depth + 1, "local slot = process.fiberSlots[" + index.lo + "]");
        line(depth + 1, "if not slot then");
        line(depth + 2, "process.lastError = 87");
        assign(depth + 2, 0, 4, "0");
        line(depth + 1, "else");
        if (name == "FlsGetValue") {
            line(depth + 2, "if slot.lo == 0 and slot.hi == 0 then process.lastError = 0 end");
            assign(depth + 2, 0, 8, "slot.lo, slot.hi");
        } else if (name == "FlsSetValue") {
            line(depth + 2, "slot.lo, slot.hi = " + value.pair());
            assign(depth + 2, 0, 4, "1");
        } else {
            line(depth + 2, "process.fiberSlots[" + index.lo + "] = nil");
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

    // ntdll exception dispatch and unwinding over the image's .pdata table. Handlers run as guest code through
    // sehCall, and RtlUnwindEx resumes its target frame by unwinding to it.
    bool emitExceptionImport(unsigned depth, std::string_view name) {
        static constexpr std::array<std::string_view, 7> names{"RaiseException", "RtlUnwindEx", "RtlUnwind",
            "RtlCaptureContext", "RtlLookupFunctionEntry", "RtlVirtualUnwind", "RtlPcToFileHeader"};
        if (arm || std::ranges::find(names, name) == names.end())
            return false;
        usesSeh = true;
        needsMemory = true;
        needsHeap = true;
        includeFunctionPointers();
        for (unsigned index = 0; index < 16; ++index)
            reg(index);
        const auto args = argumentRegisters(arm, convention);
        const auto arg = [&](unsigned index) { return reg(args[index]); };
        // The caller's context once the import returns: a call resumes after it, and a tail call or a call
        // through a pointer left the return address on the stack.
        const auto sp = reg(4).lo;
        const auto rip = callResume && !tailCall ? std::to_string(*callResume) : std::format("(read(8, {}))", sp);
        const auto rsp = callResume && !tailCall ? sp : sp + " + 8";
        const auto stack = argumentStack();
        if (name == "RtlPcToFileHeader") {
            line(depth, "do");
            line(depth + 1, std::format("local pc = address({})", arg(0).pair()));
            line(depth + 1, "local base = if pc >= seh.base and pc < seh.stop then seh.base else 0");
            line(depth + 1, std::format("write(8, address({}), base, 0)", arg(1).pair()));
            assign(depth + 1, 0, 8, "base, 0");
            line(depth, "end");
        } else if (name == "RtlLookupFunctionEntry") {
            line(depth, "do");
            line(depth + 1, std::format("local entry = sehLookup(address({}))", arg(0).pair()));
            line(depth + 1, std::format("write(8, address({}), if entry ~= 0 then seh.base else 0, 0)", arg(1).pair()));
            assign(depth + 1, 0, 8, "entry, 0");
            line(depth, "end");
        } else if (name == "RtlVirtualUnwind") {
            line(depth, "do");
            line(depth + 1, std::format("local handler, data, establisher = sehVirtualUnwind({}, address({}), address({}), "
                "address(stackArgument({}, 4)))", arg(0).lo, arg(2).pair(), arg(3).pair(), stack));
            line(depth + 1, std::format("write(8, address(stackArgument({}, 5)), data, 0)", stack));
            line(depth + 1, std::format("write(8, address(stackArgument({}, 6)), establisher, 0)", stack));
            assign(depth + 1, 0, 8, "handler, 0");
            line(depth, "end");
        } else if (name == "RtlCaptureContext") {
            line(depth, std::format("sehCapture(address({}), {}, {})", arg(0).pair(), rip, rsp));
        } else if (name == "RaiseException") {
            line(depth, "do");
            line(depth + 1, "local record = sehNew(152)");
            line(depth + 1, std::format("write(4, record, {}, 0)", arg(0).lo));
            line(depth + 1, std::format("write(4, record + 4, bit32.band({}, 1), 0)", arg(1).lo));
            line(depth + 1, std::format("write(8, record + 16, {}, 0)", rip));
            line(depth + 1, std::format("local count = math.min({}, 15)", arg(2).lo));
            line(depth + 1, "write(4, record + 24, count, 0)");
            line(depth + 1, std::format("local parameters = address({})", arg(3).pair()));
            line(depth + 1, "for i = 0, count - 1 do write(8, record + 32 + i * 8, read(8, parameters + i * 8)) end");
            line(depth + 1, "local context = sehNew(SehContextSize)");
            line(depth + 1, std::format("sehCapture(context, {}, {})", rip, rsp));
            line(depth + 1, "local escaped = sehRaise(record, context, sehCall)");
            line(depth + 1, "if escaped ~= nil then return escaped end");
            line(depth, "end");
        } else {
            // RtlUnwindEx(frame, ip, record, value, context, history) and RtlUnwind(frame, ip, record, value).
            line(depth, "do");
            if (name == "RtlUnwindEx")
                line(depth + 1, std::format("local final = address(stackArgument({}, 4))", stack));
            else
                line(depth + 1, "local final = 0");
            line(depth + 1, "if final == 0 then final = sehNew(SehContextSize) end");
            // The start is copied first: the caller may pass the context being dispatched as `final`.
            line(depth + 1, "local start, cursor = sehUnwindStart()");
            line(depth + 1, std::format("sehCapture(final, {}, {})", rip, rsp));
            line(depth + 1, std::format("local resume, escaped = sehUnwind(address({}), address({}), address({}), {}, "
                "sehCall, final, start, cursor)", arg(0).pair(), arg(1).pair(), arg(2).pair(), arg(3).lo));
            line(depth + 1, "if escaped ~= nil then return escaped end");
            line(depth + 1, "sehRestore(final)");
            line(depth + 1, "unwindStack = " + sp);
            line(depth + 1, "return resume");
            line(depth, "end");
        }
        return true;
    }

    // Per-entry helpers for exception imports: they read and write the guest registers.
    std::string exceptionHelpers() {
        std::string source = "    local function sehCapture(context: number, rip: number, rsp: number)\n"
            "        fillMemory(context, 0, 0, SehContextSize, 0)\n"
            "        write(4, context + 0x30, 0x10000b, 0)\n"
            "        write(4, context + 0x34, 0x1f80, 0)\n"
            "        write(2, context + 0x38, 0x33, 0)\n"
            "        write(2, context + 0x42, 0x2b, 0)\n"
            "        write(4, context + 0x118, 0x1f80, 0)\n";
        std::string restore = "    local function sehRestore(context: number)\n";
        for (const auto index : registers) {
            if (index >= 16)
                continue;
            const auto at = 0x78 + index * 8;
            source += std::format("        write(8, context + {}, {})\n", at, reg(index).pair());
            restore += std::format("        {} = read(8, context + {})\n", reg(index).pair(), at);
        }
        source += "        write(8, context + 0x98, rsp, 0)\n        write(8, context + 0xf8, rip, 0)\n";
        for (const auto index : xmmRegisters) {
            if (index >= 16 || index >= LocalVectorRegisters)
                continue;
            const auto lanes = xmm(VectorRegister{index});
            for (unsigned lane = 0; lane < 4; ++lane) {
                const auto at = 0x1a0 + index * 16 + lane * 4;
                source += std::format("        write(4, context + {}, {}, 0)\n", at, lanes[lane]);
                restore += std::format("        {} = (read(4, context + {}))\n", lanes[lane], at);
            }
        }
        source += "    end\n";
        restore += "    end\n";
        const auto sp = reg(4);
        source += restore;
        // Runs a handler or callback with four arguments; returns RAX, or the address an unwind escaped with.
        source += "    local function sehCall(target: number, a: number, b: number, c: number, d: number, marker: number): (number, any)\n"
            "        local callee = functionPointers[target]\n"
            "        if not callee then error(string.format(\"unknown guest exception handler 0x%x\", target), 0) end\n";
        source += std::format("        {} = a, 0\n        {} = b, 0\n        {} = c, 0\n        {} = d, 0\n",
            reg(1).pair(), reg(2).pair(), reg(8).pair(), reg(9).pair());
        source += std::format("        {0} -= 40\n        write(8, {0}, marker, 0)\n", sp.lo);
        source += "        local escaped = runGuestRoutine(callee, marker)\n"
            "        if escaped ~= nil then return 0, escaped end\n";
        source += std::format("        {} += 32\n        return {}\n    end\n", sp.lo, reg(0).lo);
        return source;
    }

    bool emitWindowsImport(unsigned depth, const GuestImport& import) {
        auto library = std::string(import.library);
        for (auto& ch : library)
            if (ch >= 'A' && ch <= 'Z')
                ch += 'a' - 'A';
        if (library != "kernel32.dll" && library != "kernelbase.dll" && !library.starts_with("api-ms-win-core-"))
            return false;

        const auto name = import.name;
        if (emitExceptionImport(depth, name))
            return true;
        struct Entry { std::string_view name; std::string_view target; };
        static constexpr std::array entries{
            Entry{"GetStdHandle", "GetStdHandle"}, Entry{"GetFileType", "GetFileType"}, Entry{"WriteFile", "WriteFile"},
            Entry{"ReadFile", "ReadFile"}, Entry{"WriteConsoleW", "WriteConsoleW"}, Entry{"CreateFileW", "CreateFileW"},
            Entry{"CloseHandle", "CloseHandle"}, Entry{"GetFileSizeEx", "GetFileSizeEx"},
            Entry{"SetFilePointerEx", "SetFilePointerEx"}, Entry{"SetEndOfFile", "SetEndOfFile"},
            Entry{"FlushFileBuffers", "yes"}, Entry{"GetConsoleMode", "no"}, Entry{"GetConsoleOutputCP", "GetACP"},
            Entry{"ReadConsoleW", "no"}, Entry{"GetCommandLineW", "GetCommandLineW"},
            Entry{"GetCommandLineA", "GetCommandLineA"}, Entry{"GetModuleFileNameW", "GetModuleFileNameW"},
            Entry{"GetModuleFileNameA", "GetModuleFileNameA"}, Entry{"GetProcAddress", "no"},
            Entry{"FreeLibrary", "yes"},
            Entry{"GetEnvironmentStringsW", "GetEnvironmentStringsW"}, Entry{"FreeEnvironmentStringsW", "yes"},
            Entry{"SetEnvironmentVariableW", "yes"}, Entry{"GetStartupInfoW", "GetStartupInfoW"},
            Entry{"GetCPInfo", "GetCPInfo"}, Entry{"GetACP", "GetACP"}, Entry{"GetOEMCP", "GetOEMCP"},
            Entry{"IsValidCodePage", "yes"}, Entry{"MultiByteToWideChar", "MultiByteToWideChar"},
            Entry{"WideCharToMultiByte", "WideCharToMultiByte"}, Entry{"LCMapStringW", "LCMapStringW"},
            Entry{"LCMapStringEx", "LCMapStringEx"}, Entry{"GetStringTypeW", "GetStringTypeW"},
            Entry{"CompareStringW", "CompareStringW"}, Entry{"GetLocaleInfoW", "GetLocaleInfoW"},
            Entry{"GetUserDefaultLCID", "GetUserDefaultLCID"}, Entry{"IsValidLocale", "yes"},
            Entry{"EnumSystemLocalesW", "yes"}, Entry{"GetDateFormatW", "no"}, Entry{"GetTimeFormatW", "no"},
            Entry{"GetTimeZoneInformation", "GetTimeZoneInformation"},
            Entry{"QueryPerformanceCounter", "QueryPerformanceCounter"},
            Entry{"QueryPerformanceFrequency", "QueryPerformanceFrequency"},
            Entry{"GetSystemTimeAsFileTime", "GetSystemTimeAsFileTime"},
            Entry{"GetCurrentProcessId", "GetCurrentProcessId"}, Entry{"GetCurrentThreadId", "GetCurrentThreadId"},
            Entry{"GetCurrentProcess", "GetCurrentProcess"}, Entry{"ExitProcess", "ExitProcess"},
            Entry{"TerminateProcess", "TerminateProcess"}, Entry{"IsProcessorFeaturePresent", "IsProcessorFeaturePresent"},
            Entry{"IsDebuggerPresent", "no"}, Entry{"InitializeSListHead", "InitializeSListHead"},
            Entry{"UnhandledExceptionFilter", "yes"}, Entry{"TlsAlloc", "TlsAlloc"}, Entry{"TlsGetValue", "TlsGetValue"},
            Entry{"TlsSetValue", "TlsSetValue"}, Entry{"TlsFree", "TlsFree"},
            Entry{"FindFirstFileExW", "FindFirstFileExW"}, Entry{"FindNextFileW", "no"}, Entry{"FindClose", "yes"},
            Entry{"SetStdHandle", "yes"}, Entry{"Sleep", "no"}, Entry{"IsDBCSLeadByteEx", "no"},
            Entry{"VirtualQuery", "VirtualQuery"}, Entry{"GetStartupInfoA", "GetStartupInfoW"},
        };
        if (const auto entry = std::ranges::find(entries, name, &Entry::name); entry != entries.end()) {
            needsProcess = true;
            needsMemory = true;
            const auto args = argumentRegisters(arm, convention);
            assign(depth, 0, 8, std::format("win32.{}({}, {}, {}, {}, {})", entry->target, reg(args[0]).pair(),
                reg(args[1]).pair(), reg(args[2]).pair(), reg(args[3]).pair(), argumentStack()));
            return true;
        }
        if (name == "GetModuleHandleW" || name == "GetModuleHandleA" || name == "GetModuleHandleExW" ||
            name == "GetModuleHandleExA") {
            // The executable is the only module: a null name or an address inside it names the image.
            needsMemory = true;
            const auto args = argumentRegisters(arm, convention);
            const auto base = std::to_string(program.imageBase);
            if (name.starts_with("GetModuleHandleEx")) {
                // GET_MODULE_HANDLE_EX_FLAG_FROM_ADDRESS treats the name as an address.
                line(depth, "do");
                line(depth + 1, std::format("local named = address({})", reg(args[1]).pair()));
                line(depth + 1, std::format("local found = named == 0 or (bit32.btest({}, 4) and named >= {} and named < {})",
                    reg(args[0]).lo, base, data.image.size()));
                line(depth + 1, std::format("write(8, address({}), if found then {} else 0, 0)", reg(args[2]).pair(), base));
                assign(depth + 1, 0, 4, "if found then 1 else 0");
                line(depth, "end");
            } else {
                assign(depth, 0, 8, std::format("if address({}) == 0 then {} else 0, 0", reg(args[0]).pair(), base));
            }
            return true;
        }
        if (name == "EncodePointer" || name == "DecodePointer") {
            const auto pointer = reg(argumentRegisters(arm, convention)[0]);
            assign(depth, 0, 8, std::format("bit32.bxor({}, 0xa5a55a5a), bit32.bxor({}, 0x5a5aa5a5)",
                pointer.lo, pointer.hi));
            return true;
        }
        if (name == "LoadLibraryExW") {
            // PE imports are resolved at translation time. This guest has no optional dynamic DLLs.
            usesLastError = true;
            line(depth, "process.lastError = 126");
            assign(depth, 0, 8, "0, 0");
            return true;
        }
        if (name == "VirtualProtect") {
            needsMemory = true;
            usesLastError = true;
            const auto args = argumentRegisters(arm, convention);
            assign(depth, 0, 4, std::format("protectMemory({}, {}, {}, {})",
                reg(args[0]).pair(), reg(args[1]).pair(), reg(args[2]).lo, reg(args[3]).pair()));
            line(depth, "if " + reg(0).lo + " == 0 then process.lastError = 87 end");
            return true;
        }
        if (name == "FlsAlloc" || name == "FlsGetValue" || name == "FlsSetValue" || name == "FlsFree") {
            emitFiberImport(depth, name);
            return true;
        }
        if (name == "GetLastError" || name == "SetLastError") {
            usesLastError = true;
            if (name == "GetLastError")
                assign(depth, 0, 4, "process.lastError");
            else
                line(depth, "process.lastError = " + reg(argumentRegisters(arm, convention)[0]).lo);
            return true;
        }
        if (name == "SetUnhandledExceptionFilter") {
            usesExceptionFilter = true;
            const auto handler = reg(argumentRegisters(arm, convention)[0]);
            const auto result = reg(0);
            line(depth, std::format("{}, process.exceptionFilterLo, process.exceptionFilterHi = process.exceptionFilterLo, process.exceptionFilterHi, {}",
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

    static bool runtimeLibrary(std::string_view library) {
        std::string lower(library);
        for (auto& ch : lower)
            if (ch >= 'A' && ch <= 'Z')
                ch += 'a' - 'A';
        return lower.starts_with("msvcrt") || lower.starts_with("ucrtbase") || lower.starts_with("api-ms-win-crt-") ||
            lower.starts_with("vcruntime") || lower.starts_with("msvcr");
    }

    bool emitImport(unsigned depth, const GuestImport& import) {
        if (convention == CallingConvention::Microsoft && !runtimeLibrary(import.library))
            return emitWindowsImport(depth, import);
        const auto name = importName(import);
        const auto arguments = argumentRegisters(arm, convention);
        if (emitMathImport(depth, name) || emitRuntimeImport(depth, name))
            return true;
        if (!arm && !import.leadingUnderscore && name == "__tls_get_addr") {
            std::string valid;
            for (const auto& region : data.regions) {
                if (!region.threadLocal)
                    continue;
                const auto size = region.end - region.start;
                if (!data.materialized(region.start))
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
            line(depth + 1, "table.insert(process.exitCallbacks, function()");
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

    // Floating-point arguments use the vector argument registers; on Windows they share positions with
    // integer arguments, so an integer after one double arrives in the second integer register.
    bool emitMathImport(unsigned depth, std::string_view name) {
        static const std::map<std::string_view, std::string_view> unary{
            {"sqrt", "math.sqrt(x)"}, {"floor", "math.floor(x)"}, {"ceil", "math.ceil(x)"},
            {"trunc", "roundTruncate(x)"}, {"round", "roundAway(x)"}, {"fabs", "math.abs(x)"},
            {"exp", "math.exp(x)"}, {"exp2", "2 ^ x"}, {"expm1", "math.exp(x) - 1"}, {"log", "math.log(x)"},
            {"log2", "math.log(x, 2)"}, {"log10", "math.log10(x)"}, {"log1p", "math.log(1 + x)"},
            {"sin", "math.sin(x)"}, {"cos", "math.cos(x)"}, {"tan", "math.tan(x)"}, {"asin", "math.asin(x)"},
            {"acos", "math.acos(x)"}, {"atan", "math.atan(x)"}, {"sinh", "math.sinh(x)"}, {"cosh", "math.cosh(x)"},
            {"tanh", "math.tanh(x)"}, {"cbrt", "(if x < 0 then -((-x) ^ (1 / 3)) else x ^ (1 / 3))"},
            {"nearbyint", "roundEven(x)"}, {"rint", "roundEven(x)"},
        };
        static const std::map<std::string_view, std::string_view> binary{
            {"pow", "x ^ y"}, {"atan2", "math.atan2(x, y)"}, {"fmod", "math.fmod(x, y)"},
            {"hypot", "math.sqrt(x * x + y * y)"}, {"fmin", "scalarMinMax(0, x, y)"}, {"fmax", "scalarMinMax(1, x, y)"},
            {"fdim", "(if x > y then x - y else 0)"},
            {"copysign", "(if (y < 0 or 1 / y < 0) then -math.abs(x) else math.abs(x))"},
        };
        auto base = name;
        unsigned size = 8;
        const auto find = [&](const auto& table) {
            if (table.contains(base))
                return true;
            if (base.ends_with('f') && table.contains(base.substr(0, base.size() - 1))) {
                base = base.substr(0, base.size() - 1);
                size = 4;
                return true;
            }
            return false;
        };
        const auto arguments = argumentRegisters(arm, convention);
        const bool microsoft = convention == CallingConvention::Microsoft;
        const auto x = floatOperand(VectorRegister{0}, 4, {});
        const auto decode = [&](unsigned index) {
            const auto lanes = xmm(VectorRegister{index});
            return std::format("decodeFloat({}, {}, {})", size, lanes[0], size == 8 ? lanes[1] : "0");
        };
        const auto result = [&](const std::string& expression) {
            needsFloating = true;
            needsVector = true;
            const auto lanes = xmm(VectorRegister{0});
            const auto fields = size == 8 ? lanes[0] + ", " + lanes[1] : lanes[0];
            line(depth, "do");
            line(depth + 1, "local x = " + decode(0));
            line(depth + 1, "local y = " + decode(1));
            line(depth + 1, std::format("{} = encodeFloat({}, {})", fields, size, expression));
            for (unsigned lane = size == 8 ? 2 : 1; lane < 4; ++lane)
                line(depth + 1, lanes[lane] + " = 0");
            line(depth, "end");
            return true;
        };
        (void)x;
        if (find(unary))
            return result(std::string(unary.at(base)));
        if (find(binary))
            return result(std::string(binary.at(base)));
        base = name;
        size = 8;
        const auto integer = arguments[microsoft ? 1 : 0];
        if (base == "ldexp" || base == "scalbn" || base == "ldexpf" || base == "scalbnf") {
            if (base.ends_with('f'))
                size = 4;
            const auto n = reg(integer).lo;
            return result(std::format("math.ldexp(x, if {0} >= 2147483648 then {0} - 4294967296 else {0})", n));
        }
        if (base == "frexp" || base == "frexpf" || base == "modf" || base == "modff") {
            if (base.ends_with('f'))
                size = 4;
            needsMemory = true;
            const auto pointer = reg(integer).pair();
            if (base.starts_with("frexp")) {
                line(depth, "do");
                line(depth + 1, std::format("local mantissa, exponent = math.frexp({})", decode(0)));
                line(depth + 1, std::format("write(4, address({}), exponent % 4294967296, 0)", pointer));
                line(depth, "end");
                return result("math.frexp(x)");
            }
            line(depth, "do");
            line(depth + 1, std::format("local whole = math.modf({})", decode(0)));
            if (size == 8)
                line(depth + 1, std::format("write(8, address({}), encodeFloat(8, whole))", pointer));
            else
                line(depth + 1, std::format("write(4, address({}), encodeFloat(4, whole))", pointer));
            line(depth, "end");
            return result("select(2, math.modf(x))");
        }
        if (base == "lround" || base == "llround" || base == "lrint" || base == "llrint" ||
            base == "lroundf" || base == "llroundf" || base == "lrintf" || base == "llrintf") {
            if (base.ends_with('f'))
                size = 4;
            needsFloating = true;
            needsVector = true;
            // Windows `long` is 32 bits wide.
            const unsigned width = microsoft && !base.starts_with("ll") ? 4 : 8;
            const auto rounding = base.find("rint") != std::string_view::npos ? "roundEven" : "roundAway";
            assign(depth, 0, 8, std::format("truncateFloat({}, {}, true, {}({}))", width, arm, rounding, decode(0)));
            return true;
        }
        return false;
    }

    // ABI of variadic arguments for the runtime's argument readers.
    unsigned variadicKind() const {
        if (convention == CallingConvention::Microsoft)
            return 3;
        if (arm)
            return program.darwin ? 2 : 1;
        return 0;
    }

    // A Luau expression building an argument reader for the variadic arguments after `named` named ones.
    std::string variadicArguments(unsigned named) {
        const auto arguments = argumentRegisters(arm, convention);
        std::string ints, floats;
        for (const auto index : arguments)
            ints += (ints.empty() ? "" : ", ") + reg(index).pair();
        for (unsigned index = 0; index < 8; ++index) {
            const auto lanes = xmm(VectorRegister{index});
            floats += (floats.empty() ? "" : ", ") + lanes[0] + ", " + lanes[1];
        }
        return std::format("registerArguments({}, {}, {{{}}}, {}, {{{}}}, 0)", variadicKind(), argumentStack(), ints,
            named, floats);
    }

    bool emitFormatImport(unsigned depth, std::string_view name) {
        // Output kinds: standard output, a FILE stream, a descriptor, a buffer, a bounded buffer, a new string.
        enum Kind { Out, Stream, Descriptor, Buffer, Bounded, Allocated };
        struct Form { std::string_view name; Kind kind; unsigned format; unsigned size; bool list; };
        static constexpr std::array forms{
            Form{"printf", Out, 0, 0, false}, Form{"vprintf", Out, 0, 0, true},
            Form{"fprintf", Stream, 1, 0, false}, Form{"vfprintf", Stream, 1, 0, true},
            Form{"dprintf", Descriptor, 1, 0, false}, Form{"vdprintf", Descriptor, 1, 0, true},
            Form{"sprintf", Buffer, 1, 0, false}, Form{"vsprintf", Buffer, 1, 0, true},
            Form{"snprintf", Bounded, 2, 1, false}, Form{"vsnprintf", Bounded, 2, 1, true},
            Form{"asprintf", Allocated, 1, 0, false}, Form{"vasprintf", Allocated, 1, 0, true},
            Form{"__printf_chk", Out, 1, 0, false}, Form{"__vprintf_chk", Out, 1, 0, true},
            Form{"__fprintf_chk", Stream, 2, 0, false}, Form{"__vfprintf_chk", Stream, 2, 0, true},
            Form{"__sprintf_chk", Buffer, 3, 0, false}, Form{"__vsprintf_chk", Buffer, 3, 0, true},
            Form{"__snprintf_chk", Bounded, 4, 1, false}, Form{"__vsnprintf_chk", Bounded, 4, 1, true},
            Form{"__asprintf_chk", Allocated, 2, 0, false}, Form{"__vasprintf_chk", Allocated, 2, 0, true},
            Form{"snprintf_l", Bounded, 3, 1, false}, Form{"vsnprintf_l", Bounded, 3, 1, true},
            Form{"asprintf_l", Allocated, 2, 0, false}, Form{"vasprintf_l", Allocated, 2, 0, true},
            Form{"sprintf_l", Buffer, 2, 0, false}, Form{"printf_l", Out, 1, 0, false},
        };
        const auto form = std::ranges::find(forms, name, &Form::name);
        if (form == forms.end())
            return false;
        needsProcess = true;
        needsMemory = true;
        const auto arguments = argumentRegisters(arm, convention);
        const auto arg = [&](unsigned index) { return reg(arguments[index]); };
        const bool windows = convention == CallingConvention::Microsoft;
        line(depth, "do");
        const auto reader = form->list ? std::format("listArguments({}, {})", variadicKind(), arg(form->format + 1).pair())
                                       : variadicArguments(form->format + 1);
        line(depth + 1, std::format("local text = formatGuest(guestString(address({})), {}, {})", arg(form->format).pair(),
            reader, windows));
        switch (form->kind) {
            case Out: line(depth + 1, "hostWrite(1, text)"); break;
            case Stream: line(depth + 1, std::format("hostWrite(streamDescriptor({}), text)", arg(0).pair())); break;
            case Descriptor: line(depth + 1, std::format("hostWrite(signed32({}), text)", arg(0).lo)); break;
            case Buffer:
                line(depth + 1, std::format("writeString(address({}), text)", arg(0).pair()));
                line(depth + 1, std::format("write(1, address({}) + #text, 0, 0)", arg(0).pair()));
                break;
            case Bounded:
                line(depth + 1, std::format("local limit = address({})", arg(form->size).pair()));
                line(depth + 1, "if limit > 0 then");
                line(depth + 2, "local kept = string.sub(text, 1, limit - 1)");
                line(depth + 2, std::format("writeString(address({}), kept)", arg(0).pair()));
                line(depth + 2, std::format("write(1, address({}) + #kept, 0, 0)", arg(0).pair()));
                line(depth + 1, "end");
                break;
            case Allocated:
                line(depth + 1, std::format("write(8, address({}), newGuestString(text), 0)", arg(0).pair()));
                break;
        }
        assign(depth + 1, 0, 4, "#text");
        line(depth, "end");
        return true;
    }

    // Calls a guest function pointer with integer arguments and leaves its result in the return register.
    void callGuest(unsigned depth, const std::string& target, std::span<const std::string> values,
        std::string_view missing, bool propagate = true) {
        includeFunctionPointers();
        needsMemory = true;
        const auto arguments = argumentRegisters(arm, convention);
        line(depth, std::format("local callee = functionPointers[address({})]", target));
        line(depth, std::format("if not callee then error({}, 0) end", quoted(missing)));
        for (std::size_t i = 0; i < values.size(); ++i)
            assign(depth, arguments[i], 8, values[i]);
        if (convention == CallingConvention::Microsoft)
            line(depth, reg(4).lo + " -= 32");
        runCallback(depth, "callee", propagate);
        if (convention == CallingConvention::Microsoft)
            line(depth, reg(4).lo + " += 32");
    }

    bool emitProcessImport(unsigned depth, std::string_view name) {
        const auto arguments = argumentRegisters(arm, convention);
        const auto arg = [&](unsigned index) { return reg(arguments[index]); };
        if (name == "__libc_start_main") {
            needsProcess = true;
            line(depth, "do");
            line(depth + 1, std::format("local count, vector = {}, {}", arg(1).lo, arg(2).lo));
            const std::array values{std::string("count, 0"), std::string("vector, 0"),
                std::string("vector + (count + 1) * 8, 0")};
            callGuest(depth + 1, arg(0).pair(), values, "unknown guest main function");
            line(depth + 1, std::format("exitProcess({}, true)", reg(0).lo));
            line(depth, "end");
            return true;
        }
        if (name == "exit" || name == "_exit" || name == "_Exit" || name == "quick_exit") {
            needsProcess = true;
            line(depth, std::format("exitProcess({}, {})", arg(0).lo, name == "exit"));
            return true;
        }
        if (name == "atexit") {
            usesExitCallbacks = true;
            includeFunctionPointers();
            needsMemory = true;
            line(depth, "do");
            line(depth + 1, std::format("local callback = functionPointers[address({})]", arg(0).pair()));
            line(depth + 1, "if not callback then error(\"unknown guest exit callback\", 0) end");
            line(depth + 1, "table.insert(process.exitCallbacks, function()");
            runCallback(depth + 2, "callback");
            line(depth + 1, "end)");
            assign(depth + 1, 0, 4, "0");
            line(depth, "end");
            return true;
        }
        if (name == "__cxa_finalize")
            return true;
        if (convention == CallingConvention::Microsoft && emitRuntimeStartup(depth, name))
            return true;
        if (name == "qsort" || name == "bsearch") {
            includeFunctionPointers();
            needsMemory = true;
            const bool search = name == "bsearch";
            // qsort(base, count, size, compare); bsearch(key, base, count, size, compare).
            const auto base = arg(search ? 1 : 0), count = arg(search ? 2 : 1), size = arg(search ? 3 : 2);
            const auto compare = arg(search ? 4 : 3);
            line(depth, "do");
            line(depth + 1, std::format("local first, count, size = address({}), address({}), address({})", base.pair(),
                count.pair(), size.pair()));
            line(depth + 1, std::format("local key = address({})", arg(0).pair()));
            line(depth + 1, std::format("local comparator = functionPointers[address({})]", compare.pair()));
            line(depth + 1, "if not comparator then error(\"unknown guest comparison function\", 0) end");
            line(depth + 1, "local function order(left: number, right: number): number");
            assign(depth + 2, arguments[0], 8, "left, 0");
            assign(depth + 2, arguments[1], 8, "right, 0");
            if (convention == CallingConvention::Microsoft)
                line(depth + 2, reg(4).lo + " -= 32");
            runCallback(depth + 2, "comparator");
            if (convention == CallingConvention::Microsoft)
                line(depth + 2, reg(4).lo + " += 32");
            line(depth + 2, std::format("return signed32({})", reg(0).lo));
            line(depth + 1, "end");
            needsProcess = true;
            if (search) {
                line(depth + 1, "local low, high, found = 0, count - 1, 0");
                line(depth + 1, "while low <= high do");
                line(depth + 2, "local middle = (low + high) // 2");
                line(depth + 2, "local sign = order(key, first + middle * size)");
                line(depth + 2, "if sign == 0 then found = first + middle * size; break end");
                line(depth + 2, "if sign < 0 then high = middle - 1 else low = middle + 1 end");
                line(depth + 1, "end");
                assign(depth + 1, 0, 8, "found, 0");
            } else {
                // A stable merge sort keeps comparator calls well defined for inconsistent orderings.
                line(depth + 1, "local items = {}");
                line(depth + 1, "for i = 0, count - 1 do items[i + 1] = readString(first + i * size, size) end");
                line(depth + 1, "local scratch = resize(0, 0, math.max(2 * size, 1), 0)");
                line(depth + 1, "local function less(a: string, b: string): boolean");
                line(depth + 2, "writeString(scratch, a)");
                line(depth + 2, "writeString(scratch + size, b)");
                line(depth + 2, "return order(scratch, scratch + size) < 0");
                line(depth + 1, "end");
                line(depth + 1, "local function sort(list: {string}): {string}");
                line(depth + 2, "if #list <= 1 then return list end");
                line(depth + 2, "local middle = #list // 2");
                line(depth + 2, "local left, right = sort(table.move(list, 1, middle, 1, {})), sort(table.move(list, middle + 1, #list, 1, {}))");
                line(depth + 2, "local merged, i, j = {}, 1, 1");
                line(depth + 2, "while i <= #left and j <= #right do");
                line(depth + 3, "if less(right[j], left[i]) then table.insert(merged, right[j]); j += 1 else table.insert(merged, left[i]); i += 1 end");
                line(depth + 2, "end");
                line(depth + 2, "for k = i, #left do table.insert(merged, left[k]) end");
                line(depth + 2, "for k = j, #right do table.insert(merged, right[k]) end");
                line(depth + 2, "return merged");
                line(depth + 1, "end");
                line(depth + 1, "for i, item in sort(items) do writeString(first + (i - 1) * size, item) end");
                line(depth + 1, "resize(scratch, 0, 0, 0)");
            }
            line(depth, "end");
            return true;
        }
        return false;
    }

    // The DLL C runtime's process startup, as the MinGW CRT uses it.
    bool emitRuntimeStartup(unsigned depth, std::string_view name) {
        const auto arguments = argumentRegisters(arm, convention);
        const auto arg = [&](unsigned index) { return reg(arguments[index]); };
        if (name == "__getmainargs" || name == "__wgetmainargs") {
            if (name == "__wgetmainargs")
                return false;
            needsProcess = true;
            line(depth, "do");
            line(depth + 1, "local count, vector, environment = processArguments()");
            line(depth + 1, std::format("write(4, address({}), count, 0)", arg(0).pair()));
            line(depth + 1, std::format("write(8, address({}), vector, 0)", arg(1).pair()));
            line(depth + 1, std::format("write(8, address({}), environment, 0)", arg(2).pair()));
            assign(depth + 1, 0, 4, "0");
            line(depth, "end");
            return true;
        }
        if (name == "_initterm" || name == "_initterm_e") {
            includeFunctionPointers();
            needsMemory = true;
            line(depth, "do");
            line(depth + 1, std::format("local first, last = address({}), address({})", arg(0).pair(), arg(1).pair()));
            line(depth + 1, "local status = 0");
            line(depth + 1, "for at = first, last - 8, 8 do");
            line(depth + 2, "local targetLo, targetHi = read(8, at)");
            line(depth + 2, "if targetLo ~= 0 or targetHi ~= 0 then");
            callGuest(depth + 3, "targetLo, targetHi", {}, "unknown guest initializer");
            if (name == "_initterm_e")
                line(depth + 3, std::format("if {} ~= 0 then status = {}; break end", reg(0).lo, reg(0).lo));
            line(depth + 2, "end");
            line(depth + 1, "end");
            assign(depth + 1, 0, 4, "status");
            line(depth, "end");
            return true;
        }
        if (name == "_onexit" || name == "_crt_atexit" || name == "_register_onexit_function") {
            usesExitCallbacks = true;
            includeFunctionPointers();
            needsMemory = true;
            const auto function = name == "_register_onexit_function" ? arg(1) : arg(0);
            line(depth, "do");
            line(depth + 1, std::format("local callbackLo, callbackHi = {}", function.pair()));
            line(depth + 1, "local callback = functionPointers[address(callbackLo, callbackHi)]");
            line(depth + 1, "if not callback then error(\"unknown guest exit callback\", 0) end");
            line(depth + 1, "table.insert(process.exitCallbacks, function()");
            line(depth + 2, reg(4).lo + " -= 32");
            runCallback(depth + 2, "callback");
            line(depth + 2, reg(4).lo + " += 32");
            line(depth + 1, "end)");
            assign(depth + 1, 0, 8, name == "_onexit" ? "callbackLo, callbackHi" : "0, 0");
            line(depth, "end");
            return true;
        }
        if (name == "_cexit" || name == "_c_exit") {
            if (name == "_cexit") {
                line(depth, "while #process.exitCallbacks > 0 do");
                line(depth + 1, "local callback = table.remove(process.exitCallbacks)");
                line(depth + 1, "if callback then callback() end");
                line(depth, "end");
            }
            return true;
        }
        if (name == "_amsg_exit") {
            trap(depth, "guest C runtime reported a fatal error");
            return true;
        }
        if (name == "__iob_func" || name == "__acrt_iob_func") {
            if (!program.streams[0])
                return false;
            const auto index = name == "__acrt_iob_func" ? std::format(" + {} * 48", arg(0).lo) : std::string();
            assign(depth, 0, 8, std::format("{}{}, 0", program.streams[0], index));
            return true;
        }
        if (name == "___lc_codepage_func") {
            assign(depth, 0, 4, "0");
            return true;
        }
        if (name == "___mb_cur_max_func") {
            assign(depth, 0, 4, "1");
            return true;
        }
        if (name == "_lock" || name == "_unlock" || name == "__set_app_type" || name == "__setusermatherr" ||
            name == "_set_app_type" || name == "_configthreadlocale" || name == "_set_invalid_parameter_handler") {
            assign(depth, 0, 8, "0, 0");
            return true;
        }
        return false;
    }

    bool emitLibraryImport(unsigned depth, std::string_view name) {
        // Functions with integer arguments implemented by the runtime's libc table.
        struct Entry { std::string_view name; std::string_view target; unsigned arguments; };
        static constexpr std::array entries{
            Entry{"write", "write", 3}, Entry{"read", "read", 3}, Entry{"open", "open", 2}, Entry{"open64", "open", 2},
            Entry{"openat", "openat", 3}, Entry{"close", "close", 1}, Entry{"lseek", "lseek", 3},
            Entry{"lseek64", "lseek", 3}, Entry{"fstat", "fstat", 2}, Entry{"fstat64", "fstat", 2},
            Entry{"stat", "stat", 2}, Entry{"stat64", "stat", 2}, Entry{"lstat", "stat", 2}, Entry{"isatty", "isatty", 1},
            Entry{"fopen", "fopen", 2}, Entry{"fopen64", "fopen", 2}, Entry{"fdopen", "fdopen", 2},
            Entry{"fclose", "fclose", 1}, Entry{"fileno", "fileno", 1}, Entry{"fwrite", "fwrite", 4},
            Entry{"fwrite_unlocked", "fwrite", 4}, Entry{"fread", "fread", 4}, Entry{"fread_unlocked", "fread", 4},
            Entry{"fputc", "fputc", 2}, Entry{"putc", "fputc", 2}, Entry{"_IO_putc", "fputc", 2},
            Entry{"fputc_unlocked", "fputc", 2}, Entry{"putc_unlocked", "fputc", 2}, Entry{"fputs", "fputs", 2},
            Entry{"fputs_unlocked", "fputs", 2}, Entry{"puts", "puts", 1}, Entry{"putchar", "putchar", 1},
            Entry{"putchar_unlocked", "putchar", 1}, Entry{"fgetc", "fgetc", 1}, Entry{"getc", "fgetc", 1},
            Entry{"_IO_getc", "fgetc", 1}, Entry{"getc_unlocked", "fgetc", 1}, Entry{"fgetc_unlocked", "fgetc", 1},
            Entry{"getchar", "getchar", 0}, Entry{"ungetc", "ungetc", 2}, Entry{"fgets", "fgets", 3},
            Entry{"fflush", "fflush", 1}, Entry{"fflush_unlocked", "fflush", 1}, Entry{"setvbuf", "setvbuf", 4},
            Entry{"setbuf", "setvbuf", 2}, Entry{"fseek", "fseek", 3}, Entry{"fseeko", "fseek", 3},
            Entry{"fseeko64", "fseek", 3}, Entry{"ftell", "ftell", 1}, Entry{"ftello", "ftell", 1},
            Entry{"ftello64", "ftell", 1}, Entry{"rewind", "rewind", 1}, Entry{"feof", "feof", 1},
            Entry{"ferror", "ferror", 1}, Entry{"clearerr", "clearerr", 1}, Entry{"__uflow", "__uflow", 1},
            Entry{"__overflow", "__overflow", 2}, Entry{"__srget", "__srget", 1}, Entry{"__swbuf", "__swbuf", 2},
            Entry{"getenv", "getenv", 1}, Entry{"secure_getenv", "getenv", 1}, Entry{"strtol", "strtol", 3},
            Entry{"strtoll", "strtol", 3}, Entry{"__isoc23_strtol", "strtol", 3}, Entry{"__isoc23_strtoll", "strtol", 3},
            Entry{"strtoimax", "strtol", 3}, Entry{"strtoul", "strtoul", 3}, Entry{"strtoull", "strtoul", 3},
            Entry{"__isoc23_strtoul", "strtoul", 3}, Entry{"__isoc23_strtoull", "strtoul", 3},
            Entry{"strtoumax", "strtoul", 3}, Entry{"atoi", "atoi", 1}, Entry{"atol", "atol", 1},
            Entry{"atoll", "atol", 1}, Entry{"time", "time", 1}, Entry{"clock", "clock", 0},
            Entry{"clock_gettime", "clock_gettime", 2}, Entry{"gettimeofday", "gettimeofday", 2},
            Entry{"setlocale", "setlocale", 2}, Entry{"getpid", "getpid", 0}, Entry{"sysconf", "sysconf", 1},
            Entry{"signal", "signal", 2}, Entry{"sigaction", "sigaction", 3},
            Entry{"pthread_self", "pthread_self", 0}, Entry{"pthread_mach_thread_np", "pthread_mach_thread_np", 1},
            Entry{"pthread_equal", "pthread_equal", 2}, Entry{"pthread_key_create", "pthread_key_create", 2},
            Entry{"pthread_key_delete", "success", 1}, Entry{"pthread_getspecific", "pthread_getspecific", 1},
            Entry{"pthread_setspecific", "pthread_setspecific", 2}, Entry{"pthread_mutex_init", "success", 2},
            Entry{"pthread_mutex_destroy", "success", 1}, Entry{"pthread_mutexattr_init", "success", 1},
            Entry{"pthread_mutexattr_settype", "success", 2}, Entry{"pthread_mutexattr_destroy", "success", 1},
            Entry{"pthread_cond_init", "success", 2}, Entry{"pthread_cond_destroy", "success", 1},
            Entry{"pthread_cond_wait", "pthread_cond_wait", 2}, Entry{"pthread_rwlock_init", "success", 2},
            Entry{"pthread_rwlock_destroy", "success", 1}, Entry{"pthread_rwlock_rdlock", "success", 1},
            Entry{"pthread_rwlock_wrlock", "success", 1}, Entry{"pthread_rwlock_unlock", "success", 1},
            Entry{"sched_yield", "success", 0},
            Entry{"__maskrune", "__maskrune", 2}, Entry{"__maskrune_l", "__maskrune", 2},
            Entry{"__toupper", "__toupper", 1}, Entry{"__tolower", "__tolower", 1},
            Entry{"__toupper_l", "__toupper", 1}, Entry{"__tolower_l", "__tolower", 1},
            Entry{"___toupper_l", "__toupper", 1}, Entry{"___tolower_l", "__tolower", 1},
            Entry{"___mb_cur_max_l", "__mb_cur_max_l", 0},
            Entry{"toupper_l", "__toupper", 1}, Entry{"tolower_l", "__tolower", 1},
            Entry{"__mb_cur_max_l", "__mb_cur_max_l", 0}, Entry{"wctob", "wctob", 1}, Entry{"wctob_l", "wctob", 1},
            Entry{"btowc_l", "btowc", 1}, Entry{"mbtowc", "mbtowc", 3}, Entry{"mbtowc_l", "mbtowc", 3},
            Entry{"mbrtowc", "mbrtowc", 3}, Entry{"mbrtowc_l", "mbrtowc", 3}, Entry{"mbrlen", "mbrlen", 2},
            Entry{"mbrlen_l", "mbrlen", 2}, Entry{"wcrtomb", "wcrtomb", 2}, Entry{"wcrtomb_l", "wcrtomb", 2},
            Entry{"mbsrtowcs", "mbsrtowcs", 3}, Entry{"mbsrtowcs_l", "mbsrtowcs", 3},
            Entry{"mbsnrtowcs", "mbsnrtowcs", 4}, Entry{"mbsnrtowcs_l", "mbsnrtowcs", 4},
            Entry{"wcsnrtombs", "wcsnrtombs", 4}, Entry{"wcsnrtombs_l", "wcsnrtombs", 4},
            Entry{"wcslen", "wcslen", 1}, Entry{"localeconv", "localeconv", 0}, Entry{"localeconv_l", "localeconv", 0},
            Entry{"strspn", "strspn", 2}, Entry{"strcspn", "strcspn", 2}, Entry{"strpbrk", "strpbrk", 2},
            Entry{"strncpy", "strncpy", 3}, Entry{"strncat", "strncat", 3}, Entry{"strdup", "strdup", 1},
            Entry{"strerror", "strerror", 1}, Entry{"strerror_r", "strerror_r", 3}, Entry{"__xpg_strerror_r", "strerror_r", 3},
            Entry{"aligned_alloc", "aligned_alloc", 2}, Entry{"posix_memalign", "posix_memalign", 3},
            Entry{"mach_absolute_time", "mach_absolute_time", 0}, Entry{"mach_timebase_info", "mach_timebase_info", 1},
            Entry{"dlopen", "failure", 0}, Entry{"dlsym", "failure", 0}, Entry{"dladdr", "failure", 0},
            Entry{"_dyld_register_func_for_remove_image", "success", 0},
            Entry{"_dyld_find_unwind_sections", "dyld_find_unwind_sections", 2},
            Entry{"_dl_find_object", "dl_find_object", 2}, Entry{"__getauxval", "failure", 1},
            Entry{"getauxval", "failure", 1}, Entry{"gettext", "gettext", 1}, Entry{"dgettext", "dgettext", 2},
            Entry{"dcgettext", "dgettext", 3},
            Entry{"isspace", "isspace", 1}, Entry{"strcoll_l", "strcoll", 2}, Entry{"strcoll", "strcoll", 2},
        };
        const auto arguments = argumentRegisters(arm, convention);
        if (name == "strtod" || name == "strtof" || name == "atof" || name == "__isoc23_strtod" ||
            name == "__isoc23_strtof" || name == "strtold") {
            needsProcess = true;
            needsFloating = true;
            const auto end = name == "atof" ? std::string("0, 0") : reg(arguments[1]).pair();
            const unsigned size = name.ends_with('f') && name != "atof" ? 4 : 8;
            const auto lanes = xmm(VectorRegister{0});
            line(depth, std::format("{}, {} = encodeFloat({}, libc.strtod({}, {}))", lanes[0], lanes[1], size,
                reg(arguments[0]).pair(), end));
            line(depth, std::format("{}, {} = 0, 0", lanes[2], lanes[3]));
            return true;
        }
        const auto entry = std::ranges::find(entries, name, &Entry::name);
        if (entry == entries.end())
            return false;
        needsProcess = true;
        needsMemory = true;
        std::string values;
        for (unsigned i = 0; i < entry->arguments; ++i)
            values += (i ? ", " : "") + reg(arguments[i]).pair();
        assign(depth, 0, 8, std::format("libc.{}({})", entry->target, values));
        return true;
    }

    // C runtime helpers shared by every platform.
    bool emitRuntimeImport(unsigned depth, std::string_view name) {
        if (emitFormatImport(depth, name) || emitProcessImport(depth, name) || emitLibraryImport(depth, name))
            return true;
        const auto arguments = argumentRegisters(arm, convention);
        const auto arg = [&](unsigned index) { return reg(arguments[index]); };
        if (name == "__stack_chk_fail" || name == "__stack_chk_fail_local") {
            trap(depth, "guest stack protector detected corruption");
            return true;
        }
        if (name == "abort") {
            trap(depth, "guest called abort");
            return true;
        }
        if (name == "__memcpy_chk" || name == "__memmove_chk") {
            needsMemory = true;
            line(depth, std::format("if {} > {} or ({} == {} and {} > {}) then error(\"guest buffer overflow detected\", 0) end",
                arg(2).hi, arg(3).hi, arg(2).hi, arg(3).hi, arg(2).lo, arg(3).lo));
            assign(depth, 0, 8, std::format("copyMemory({}, {}, {})", arg(0).pair(), arg(1).pair(), arg(2).pair()));
            return true;
        }
        if (name == "__memset_chk") {
            needsMemory = true;
            line(depth, std::format("if {} > {} or ({} == {} and {} > {}) then error(\"guest buffer overflow detected\", 0) end",
                arg(2).hi, arg(3).hi, arg(2).hi, arg(3).hi, arg(2).lo, arg(3).lo));
            assign(depth, 0, 8, std::format("fillMemory({}, {}, {})", arg(0).pair(), arg(1).lo, arg(2).pair()));
            return true;
        }
        if (name == "calloc") {
            needsMemory = true;
            needsHeap = true;
            line(depth, "do");
            line(depth + 1, std::format("local count, size = address({}), address({})", arg(0).pair(), arg(1).pair()));
            line(depth + 1, "local pointer = if count * size > 0 then resize(0, 0, count * size, 0) else resize(0, 0, 1, 0)");
            line(depth + 1, "if pointer ~= 0 then fillMemory(pointer, 0, 0, count * size, 0) end");
            assign(depth + 1, 0, 8, "pointer, 0");
            line(depth, "end");
            return true;
        }
        if (name == "_errno" || name == "__errno_location" || name == "__error" || name == "__errno") {
            needsMemory = true;
            needsHeap = true;
            assign(depth, 0, 8, "errnoAddress(), 0");
            return true;
        }
        if (name == "__udivti3" || name == "__umodti3" || name == "__divti3" || name == "__modti3") {
            needsDivision = true;
            const bool sign = name == "__divti3" || name == "__modti3";
            const bool remainder = name == "__umodti3" || name == "__modti3";
            const auto result = arm ? std::pair{reg(0), reg(1)} : std::pair{reg(0), reg(2)};
            line(depth, std::format("{}, {} = divide128({}, {}, {}, {}, {}, {})", result.first.pair(), result.second.pair(),
                sign, remainder, arg(0).pair(), arg(1).pair(), arg(2).pair(), arg(3).pair()));
            return true;
        }
        if (name == "strchr" || name == "strrchr") {
            needsMemory = true;
            line(depth, "do");
            line(depth + 1, "local at = address(" + arg(0).pair() + ")");
            line(depth + 1, "local needle = bit32.band(" + arg(1).lo + ", 255)");
            line(depth + 1, "local found = 0");
            line(depth + 1, "while true do");
            line(depth + 2, "local byte = read(1, at)");
            line(depth + 2, std::format("if byte == needle then found = at{} end", name == "strchr" ? "; break" : ""));
            line(depth + 2, "if byte == 0 then break end");
            line(depth + 2, "at += 1");
            line(depth + 1, "end");
            assign(depth + 1, 0, 8, "found, 0");
            line(depth, "end");
            return true;
        }
        if (name == "strncmp") {
            needsMemory = true;
            line(depth, "do");
            line(depth + 1, std::format("local a, b, count = address({}), address({}), address({})", arg(0).pair(),
                arg(1).pair(), arg(2).pair()));
            line(depth + 1, "local result = 0");
            line(depth + 1, "for i = 0, count - 1 do");
            line(depth + 2, "local left, right = read(1, a + i), read(1, b + i)");
            line(depth + 2, "if left ~= right then result = (left - right) % 4294967296; break end");
            line(depth + 2, "if left == 0 then break end");
            line(depth + 1, "end");
            assign(depth + 1, 0, 8, "result, 0");
            line(depth, "end");
            return true;
        }
        if (name == "strcpy" || name == "stpcpy" || name == "strcat") {
            needsMemory = true;
            line(depth, "do");
            line(depth + 1, std::format("local to, from = address({}), address({})", arg(0).pair(), arg(1).pair()));
            line(depth + 1, "local start = to");
            if (name == "strcat")
                line(depth + 1, "to += stringLength(to, 0)");
            line(depth + 1, "local length = stringLength(from, 0)");
            line(depth + 1, "copyMemory(to, 0, from, 0, length + 1, 0)");
            assign(depth + 1, 0, 8, name == "stpcpy" ? "to + length, 0" : "start, 0");
            line(depth, "end");
            return true;
        }
        if (name == "_tlv_bootstrap" || name == "tlv_bootstrap") {
            // The loader stores each thread-local template's address in the descriptor's key word.
            needsMemory = true;
            const auto descriptor = arg(0);
            line(depth, "do");
            line(depth + 1, std::format("local descriptor = address({})", descriptor.pair()));
            line(depth + 1, "local base = address(read(8, descriptor + 8))");
            assign(depth + 1, 0, 8, "base + address(read(8, descriptor + 16)), 0");
            line(depth, "end");
            return true;
        }
        if (program.darwin && (name == "newlocale" || name == "uselocale" || name == "duplocale" || name == "freelocale" ||
            name == "querylocale")) {
            needsProcess = true;
            if (name == "newlocale" || name == "duplocale")
                assign(depth, 0, 8, "libc.newlocale()");
            else if (name == "uselocale")
                assign(depth, 0, 8, "libc.uselocale()");
            else if (name == "querylocale")
                assign(depth, 0, 8, "cachedString(\"C\"), 0");
            return true;
        }
        if (name == "toupper" || name == "tolower") {
            const auto value = arg(0).lo;
            const auto [low, high, delta] = name == "toupper" ? std::tuple{97, 122, -32} : std::tuple{65, 90, 32};
            assign(depth, 0, 4, std::format("if {0} >= {1} and {0} <= {2} then {0} + {3} else {0}", value, low, high, delta));
            return true;
        }
        return false;
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
    std::span<const std::uint8_t> image, std::span<const ir::CodeRange> code, CallingConvention convention,
    const ProgramOptions& program) {
    const bool arm = architecture == Architecture::Arm64;
    const auto loops = recoverLoops(graph);
    Data data{image, regions, imports, code, objects, {}};
    data.unwindObjects = program.unwindObjects;
    for (const auto& pad : program.landingPads)
        if (references.functions.contains(Address(pad.target)) && graph.contains(Address(pad.target)))
            data.landingPads.insert(pad.target);
    // Mapped images embed all of their data: references through computed pointers are common.
    if (!regions.empty())
        data.materializeAll();
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
    bool vector = false;
    bool process = false;
    bool x87 = false;
    bool seh = false;
    bool landingPads = false;
    std::map<Address, std::string> functions;
    const auto lower = [&](Address entry) {
        if (functions.contains(entry))
            return;
        if (auto direct = initializers.empty() && program.startup == Startup::Library ?
            lowerDirect(graph, entry, arm, convention) : std::nullopt) {
            functions.emplace(entry, std::move(*direct));
        } else {
            structured = true;
            StructuredFunction emitter(graph, references.functions, loops, data, entry, arm, convention, initializers,
                program);
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
            vector |= emitter.usesVector();
            process |= emitter.usesProcess();
            x87 |= emitter.usesX87();
            seh |= emitter.usesSehRuntime();
            landingPads |= emitter.usesLandingPadTable();
            functions.emplace(entry, std::move(body));
        }
    };
    if (exports.empty())
        lower(0);
    for (const auto& entry : exports)
        lower(entry.offset);

    if (seh)
        process = true;
    if (process)
        memory = heap = floating = true;
    if (x87)
        memory = floating = vector = true;
    const RuntimeFeatures runtime{flags, shifts, division, multiply, jumpFrames, memory, stackGuard, heap, floating, prime,
        structured, decimal, vector, process, x87, seh, landingPads};
    return printModule(functions, exports, runtime, data, program);
}
}
