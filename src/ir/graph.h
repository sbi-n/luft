#pragma once

#include "recompiler.h"

#include <array>
#include <map>
#include <optional>
#include <set>
#include <variant>
#include <vector>

namespace ir {
using Address = std::int64_t;
inline constexpr unsigned Zero = 32;
// Registers past Zero are translator temporaries for instructions that need several IR effects.
inline constexpr unsigned Temp = 33;
inline constexpr unsigned RegisterCount = 40;
// Vector register index reserved for translator temporaries.
inline constexpr unsigned VectorTemp = 32;

struct Register { unsigned index; };
struct Immediate { std::uint64_t value; };
enum class IndexWidth { Full, Unsigned32, Signed32 };
struct EffectiveAddress {
    unsigned base;
    Address displacement;
    unsigned index = Zero;
    unsigned scale = 1;
    IndexWidth indexWidth = IndexWidth::Full;
    bool operator==(const EffectiveAddress&) const = default;
};
struct Memory { EffectiveAddress address; };
struct StackTop {};
struct StackGuard {};
// A GS-relative absolute load on Windows, such as the thread environment block's TLS array at 0x58.
struct ThreadLocalStorage { Address offset = 0x58; };
using Value = std::variant<Register, Immediate, EffectiveAddress, Memory, StackTop, StackGuard, ThreadLocalStorage>;

enum class BinaryOp { Add, Sub, And, Or, Xor };
enum class ShiftOp { Left, LogicalRight, ArithmeticRight, RotateRight, RotateLeft };
struct Nop {};
struct Move { unsigned size; unsigned dst; Value src; };
struct ByteMove { Value dst; unsigned dstField; Value src; unsigned srcField; };
struct Exchange { unsigned size; Value dst; Register src; bool add = false; };
struct AtomicAdd { unsigned size; EffectiveAddress address; Register src; unsigned dst; };
struct Extend { unsigned size; unsigned dst; Value src; unsigned bits; unsigned field; bool sign; };
struct ConditionalMove { unsigned size; unsigned dst; Value src; unsigned condition; };
enum class SelectElse { Copy, Increment, Invert, Negate };
struct Select { unsigned size; unsigned dst; Register yes; Register no; unsigned condition; SelectElse otherwise; };
struct ConditionalCompare {
    unsigned size;
    Register lhs;
    Value rhs;
    unsigned condition;
    unsigned otherwise;
    bool subtract;
};
struct Divide { unsigned size; Value divisor; bool sign = false; };
struct DivideWord { unsigned size; unsigned dst; Register lhs; Register rhs; bool sign; };
enum class MultiplyOperands { Full, Signed32, Unsigned32, SignedHigh, UnsignedHigh, SignedWide, UnsignedWide };
struct Multiply {
    unsigned size;
    unsigned dst;
    Value lhs;
    Value rhs;
    bool flags = true;
    unsigned accumulator = Zero;
    bool subtract = false;
    MultiplyOperands operands = MultiplyOperands::Full;
};
struct SetCondition { Value dst; unsigned field; unsigned condition; };
struct Binary {
    BinaryOp op;
    unsigned size;
    unsigned dst;
    unsigned lhs;
    Value rhs;
    bool flags;
    ShiftOp shift = ShiftOp::Left;
    unsigned count = 0;
    bool invert = false;
    unsigned extendBits = 0;
    bool signExtend = false;
    bool withCarry = false;
};
struct MemoryBinary {
    BinaryOp op;
    unsigned size;
    Value dst;
    Value rhs;
    bool writeBack;
    bool keepCarry = false;
    bool flags = true;
    bool withCarry = false;
};
struct Store { unsigned size; EffectiveAddress address; Value src; };
struct PairTransfer {
    unsigned size;
    unsigned first;
    unsigned second;
    EffectiveAddress address;
    Address writeback;
    bool load;
    bool vector = false;
    bool sign = false;
};
struct Push { Value src; };
struct KeepBits { unsigned size; unsigned dst; unsigned shift; unsigned value; };
struct ByteBinary {
    BinaryOp op; Value lhs; unsigned lhsField; Value rhs; unsigned rhsField;
    bool writeBack = false;
    bool keepCarry = false;
    bool reverse = false;
    bool flags = true;
};
struct ByteShift { ShiftOp op; Value dst; unsigned field; std::optional<unsigned> count; };
struct Shift { ShiftOp op; unsigned size; Register dst; unsigned count; };
struct ShiftRegister { ShiftOp op; unsigned size; unsigned dst; Register src; Register count; bool flags = false; };
struct Extract { unsigned size; unsigned dst; Register high; Register low; unsigned count; };
struct Bitfield {
    unsigned size; unsigned dst; Register src; unsigned start; unsigned width; unsigned position; bool sign;
    bool insert = false;
};
enum class BitAction { Test, Set, Reset, Toggle };
struct BitTest { unsigned size; Value target; Value index; BitAction action; };
// leadingCount: ARM64 CLZ without flags. counts: x86 LZCNT/TZCNT, whose result is the operand width for zero.
struct BitScan {
    unsigned size; unsigned dst; Value src; bool reverse; bool leadingCount = false; bool counts = false;
    bool population = false;
};
struct ByteSwap { unsigned size; unsigned dst; Register src; bool reverseBits = false; };
struct StringDirection { bool backward; };
struct RepeatStore { unsigned size; };
// An x87 instruction (opcodes D8-DF) interpreted by the runtime's FPU emulation.
struct X87 { unsigned opcode; unsigned modrm; std::optional<EffectiveAddress> memory; };
// SHLD/SHRD by CL: shift the destination and fill the vacated bits from the source register.
struct DoubleShift { unsigned size; unsigned dst; Register src; bool left; };
// MOVS copies [RSI] to [RDI]; with a REP prefix it repeats RCX times.
struct StringMove { unsigned size; bool repeat; };
// CMPXCHG compares the accumulator with memory and stores the source when they match.
struct CompareExchange { unsigned size; EffectiveAddress address; Register src; };
struct CpuId {};
struct VectorRegister { unsigned index; };
struct VectorMemory { EffectiveAddress address; bool aligned; };
using VectorOperand = std::variant<VectorRegister, VectorMemory>;
enum class VectorOp {
    Xor, And, AndNot, Or, UnpackLowDwords, UnpackLowQwords, AddDwords, SubDwords,
    DotUnsignedBytes, AccumulatePairs, CompareZeroDwords, CompareZeroQwords, AddQwords, SubQwords, SumQwords,
    CompareUnsignedWords, CompareUnsignedDwords
};
struct VectorBinary {
    VectorOp op; VectorRegister dst; VectorOperand src; std::optional<VectorRegister> lhs = {}; unsigned size = 16;
};
struct VectorMove { VectorOperand dst; VectorOperand src; unsigned size = 16; bool keepUpper = false; };
struct InterleavedLoad4 { VectorRegister first; EffectiveAddress address; unsigned elementSize; };
struct VectorSplat { VectorRegister dst; Register src; unsigned elementSize; unsigned size; };
struct VectorWiden { VectorRegister dst; VectorRegister src; unsigned bits; unsigned shift; bool upper; };
struct VectorHalfMove { VectorOperand dst; VectorOperand src; bool dstHigh; bool srcHigh; };
struct VectorShiftBytes { VectorRegister dst; unsigned count; bool left; };
struct VectorIntToDouble { VectorRegister dst; VectorOperand src; };
struct VectorSignMask { unsigned dst; VectorRegister src; unsigned size; };
struct VectorShuffle { VectorRegister dst; VectorOperand src; unsigned mask; std::optional<bool> highWords = {}; };
struct VectorTransfer { Register gp; VectorRegister xmm; bool toXmm; unsigned size = 8; std::optional<unsigned> lane = {}; };
struct VectorImmediate { VectorRegister dst; std::array<std::uint32_t, 4> lanes; };
struct VectorByteOperation { VectorRegister dst; VectorRegister src; unsigned size; bool reduce; };
enum class FloatOp { Add, Sub, Mul, Div, Min, Max, Sqrt, Convert, Ceil, Floor, Abs };
struct FloatBinary { FloatOp op; unsigned size; unsigned sourceSize; VectorRegister dst; VectorOperand src; std::optional<VectorRegister> lhs = {}; };
struct FloatCompare { unsigned size; VectorRegister lhs; std::optional<VectorOperand> rhs; };
struct FloatMask { unsigned size; VectorRegister dst; VectorOperand src; unsigned predicate; };
struct IntegerToFloat { unsigned size; VectorRegister dst; unsigned integerSize; Value src; bool sign = true; unsigned fractionBits = 0; };
enum class Rounding { Truncate, Up, Down, NearestEven, Away };
struct FloatToInteger {
    unsigned size;
    unsigned dst;
    unsigned floatSize;
    VectorOperand src;
    bool sign = true;
    Rounding rounding = Rounding::Truncate;
    unsigned fractionBits = 0;
};
struct FloatingControl { EffectiveAddress address; unsigned size; bool load; };

// Element-wise vector operations. Lanes are `element` bytes wide; `size` is 8 or 16 bytes, and an
// 8-byte result clears the upper half. A missing lhs means the destination is also the first operand.
enum class LaneOp {
    Add, Sub, Mul, Equal, GreaterSigned, GreaterEqualSigned, Higher, HigherSame,
    MinSigned, MaxSigned, MinUnsigned, MaxUnsigned, AddSaturateUnsigned, AddSaturateSigned,
    SubSaturateUnsigned, SubSaturateSigned, AverageUnsigned, MulHighUnsigned, MulHighSigned, AbsoluteDifference,
    MulWideUnsigned, // PMULUDQ: the low 32 bits of each 64-bit lane widen to a 64-bit product.
    // PACKSS/PACKUS narrow both operands with saturation: the first fills the low half, the second the high.
    PackSigned, PackUnsigned,
    ShuffleBytes, // PSHUFB: each control byte selects a byte of the first operand or zero.
};
struct VectorLanes {
    LaneOp op; unsigned element; VectorRegister dst; VectorOperand rhs; std::optional<VectorRegister> lhs = {};
    unsigned size = 16;
};
enum class FloatLaneOp {
    Add, Sub, Mul, Div, Min, Max, Sqrt, Equal, Less, LessEqual, Unordered, NotEqual, NotLess, NotLessEqual,
    Ordered, Greater, GreaterEqual, Negate, Absolute, MinNumber, MaxNumber, ArmMin, ArmMax,
};
struct VectorFloatLanes {
    FloatLaneOp op; unsigned element; VectorRegister dst; VectorOperand rhs; std::optional<VectorRegister> lhs = {};
    unsigned size = 16;
    std::optional<unsigned> rhsLane = {}; // Multiply by one broadcast element, as in FMUL Vd.2S, Vn.2S, Vm.S[i].
};
// Shifts each lane by an immediate count, or by the low 64 bits of a vector operand for SSE register forms.
struct VectorShiftLanes {
    ShiftOp op; unsigned element; VectorRegister dst; VectorRegister src; unsigned count;
    std::optional<VectorOperand> countOperand = {}; unsigned size = 16;
};
// Builds the destination byte by byte: indexes 0-15 select from the first source, 16-31 from the
// second, and 255 produces zero. Indexes 32-47 keep the destination's previous bytes.
struct VectorPermute {
    VectorRegister dst; VectorOperand first; VectorOperand second; std::array<std::uint8_t, 16> bytes;
};
enum class LaneConversion {
    FloatToDouble, DoubleToFloat, DoubleToInt32Truncate, Int32ToFloat, FloatToInt32Truncate,
    SignedToFloat, UnsignedToFloat, FloatToSigned, FloatToUnsigned, WidenSigned, WidenUnsigned, Narrow,
    Int32ToDouble,
};
// `upper` selects the source's upper half for widening forms and the destination's upper half for
// narrowing forms (the "2" ARM64 variants). `element` is the source element size in bytes.
struct VectorConvert {
    LaneConversion kind; VectorRegister dst; VectorOperand src; unsigned element; bool upper = false; unsigned shift = 0;
    unsigned size = 16;
};
enum class ReduceOp { Add, AddLong, MaxUnsigned, MinUnsigned, MaxSigned, MinSigned, SignMask, AddPair };
// Reduces the lanes of a vector into lane 0 of `dst`, or into a general register for SignMask.
struct VectorReduce { ReduceOp op; unsigned element; VectorRegister dst; VectorRegister src; unsigned size = 16; unsigned gp = Zero; };
// Selects bits from `yes` where `mask` is set and from `no` elsewhere.
struct VectorBlend { VectorRegister dst; VectorOperand yes; VectorOperand no; VectorRegister mask; bool laneSign = false; unsigned element = 8; };
// Scalar floating-point operations that ARM64 and SSE4.1 provide beyond FloatBinary.
enum class ScalarFloatOp { Negate, RoundNearestEven, RoundAway, Floor, Ceil, Truncate, NegateMultiply, MinNumber, MaxNumber, ArmMin, ArmMax };
struct ScalarFloat { ScalarFloatOp op; unsigned size; VectorRegister dst; VectorOperand src; std::optional<VectorRegister> lhs = {}; bool clearUpper = true; };
// FMADD and its variants: dst = (negateProduct ? -1 : 1) * a * b + (negateAddend ? -1 : 1) * c.
struct FusedMultiply { unsigned size; VectorRegister dst; VectorRegister a; VectorRegister b; VectorRegister c; bool negateProduct; bool negateAddend; bool clearUpper = true; };
struct FloatSelect { unsigned size; VectorRegister dst; VectorRegister yes; VectorRegister no; unsigned condition; };
struct FloatConditionalCompare { unsigned size; VectorRegister lhs; std::optional<VectorRegister> rhs; unsigned condition; unsigned otherwise; };
// Moves one lane between vector registers, or between a vector lane and memory.
struct VectorLaneMove { unsigned element; VectorRegister dst; unsigned dstLane; VectorRegister src; unsigned srcLane; };
struct VectorLaneLoad { unsigned element; VectorRegister dst; unsigned lane; EffectiveAddress address; bool replicate = false; unsigned size = 16; };
using Effect = std::variant<Nop, Move, ByteMove, Exchange, AtomicAdd, Extend, ConditionalMove, Select, ConditionalCompare,
    Divide, DivideWord, Multiply, SetCondition,
    Binary, MemoryBinary, Store, PairTransfer, Push, KeepBits, ByteBinary, ByteShift, Shift, ShiftRegister,
    Bitfield, BitTest, BitScan, ByteSwap,
    StringDirection, RepeatStore, StringMove, CompareExchange, CpuId, Extract, DoubleShift, X87,
    VectorBinary, VectorMove, InterleavedLoad4, VectorSplat, VectorWiden,
    VectorHalfMove, VectorShiftBytes, VectorIntToDouble, VectorSignMask,
    VectorShuffle, VectorTransfer,
    VectorImmediate, VectorByteOperation,
    FloatBinary, FloatCompare,
    FloatMask, IntegerToFloat, FloatToInteger, FloatingControl,
    VectorLanes, VectorFloatLanes, VectorShiftLanes, VectorPermute, VectorConvert, VectorReduce, VectorBlend,
    ScalarFloat, FusedMultiply, FloatSelect, FloatConditionalCompare, VectorLaneMove, VectorLaneLoad>;


struct FlagsCondition { unsigned code; };
struct ZeroCondition { unsigned reg; unsigned size; bool inverted; };
struct TestBitCondition { unsigned reg; unsigned bit; bool inverted; };
using Condition = std::variant<FlagsCondition, ZeroCondition, TestBitCondition>;

struct Jump { Value target; std::vector<Address> destinations = {}; };
struct Branch { Condition condition; Address taken; Address other; };
struct Call { Value target; Address resume; };
struct Return { Value target; unsigned stackAdjust = 0; };
struct Trap { std::string message; };
using Terminator = std::variant<Jump, Branch, Call, Return, Trap>;

struct Block {
    std::vector<Effect> effects;
    Terminator end;
    bool hasTerminator = true;
};
using Graph = std::map<Address, Block>;
struct CodeRange { std::size_t first; std::size_t last; };
struct References {
    std::set<Address> functions;
    std::set<Address> data;
    std::vector<GuestObject> tables;
};

std::size_t executableEnd(std::size_t pc, std::size_t imageSize, std::span<const GuestRegion> regions);
Graph lift(Architecture architecture, std::span<const std::uint8_t> image,
    std::span<const GuestExport> exports, std::span<const GuestRegion> regions,
    std::vector<CodeRange>* code = nullptr, References* references = nullptr,
    std::span<const GuestBinding> bindings = {}, CallingConvention convention = CallingConvention::Native,
    std::optional<std::size_t> tlsVector = {}, std::size_t threadBlock = 0);
}
