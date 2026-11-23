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
struct ThreadLocalStorage {};
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
struct Divide { unsigned size; Value divisor; };
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
struct Push { Register src; };
struct KeepBits { unsigned size; unsigned dst; unsigned shift; unsigned value; };
struct ByteBinary {
    BinaryOp op; Value lhs; unsigned lhsField; Value rhs; unsigned rhsField;
    bool writeBack = false;
    bool keepCarry = false;
    bool reverse = false;
};
struct ByteShift { ShiftOp op; Value dst; unsigned field; std::optional<unsigned> count; };
struct Shift { ShiftOp op; unsigned size; Register dst; unsigned count; };
struct ShiftRegister { ShiftOp op; unsigned size; unsigned dst; Register src; Register count; bool flags = false; };
struct Bitfield {
    unsigned size; unsigned dst; Register src; unsigned start; unsigned width; unsigned position; bool sign;
    bool insert = false;
};
enum class BitAction { Test, Set, Reset, Toggle };
struct BitTest { unsigned size; Value target; Value index; BitAction action; };
struct BitScan { unsigned size; unsigned dst; Value src; bool reverse; bool leadingCount = false; };
struct ByteSwap { unsigned size; unsigned dst; Register src; bool reverseBits = false; };
struct StringDirection { bool backward; };
struct RepeatStore { unsigned size; };
struct CpuId {};
struct VectorRegister { unsigned index; };
struct VectorMemory { EffectiveAddress address; bool aligned; };
using VectorOperand = std::variant<VectorRegister, VectorMemory>;
enum class VectorOp { Xor, And, AndNot, Or, UnpackLowDwords, UnpackLowQwords, AddDwords, SubDwords };
struct VectorBinary { VectorOp op; VectorRegister dst; VectorOperand src; std::optional<VectorRegister> lhs = {}; };
struct VectorMove { VectorOperand dst; VectorOperand src; unsigned size = 16; bool keepUpper = false; };
struct VectorHalfMove { VectorOperand dst; VectorOperand src; bool dstHigh; bool srcHigh; };
struct VectorShiftBytes { VectorRegister dst; unsigned count; bool left; };
struct VectorIntToDouble { VectorRegister dst; VectorOperand src; };
struct VectorSignMask { unsigned dst; VectorRegister src; unsigned size; };
struct VectorShuffleDwords { VectorRegister dst; VectorOperand src; unsigned mask; };
struct VectorTransfer { Register gp; VectorRegister xmm; bool toXmm; unsigned size = 8; };
struct VectorImmediate { VectorRegister dst; std::array<std::uint32_t, 4> lanes; };
struct VectorByteOperation { VectorRegister dst; VectorRegister src; unsigned size; bool reduce; };
enum class FloatOp { Add, Sub, Mul, Div, Min, Max, Sqrt, Convert, Ceil, Floor, Abs };
struct FloatBinary { FloatOp op; unsigned size; unsigned sourceSize; VectorRegister dst; VectorOperand src; };
struct FloatCompare { unsigned size; VectorRegister lhs; std::optional<VectorOperand> rhs; };
struct FloatMask { unsigned size; VectorRegister dst; VectorOperand src; unsigned predicate; };
struct IntegerToFloat { unsigned size; VectorRegister dst; unsigned integerSize; Value src; bool sign = true; };
enum class Rounding { Truncate, Up, Down };
struct FloatToInteger {
    unsigned size;
    unsigned dst;
    unsigned floatSize;
    VectorOperand src;
    bool sign = true;
    Rounding rounding = Rounding::Truncate;
};
struct FloatingControl { EffectiveAddress address; unsigned size; bool load; };
using Effect = std::variant<Nop, Move, ByteMove, Exchange, AtomicAdd, Extend, ConditionalMove, Select, ConditionalCompare,
    Divide, DivideWord, Multiply, SetCondition,
    Binary, MemoryBinary, Store, PairTransfer, Push, KeepBits, ByteBinary, ByteShift, Shift, ShiftRegister,
    Bitfield, BitTest, BitScan, ByteSwap,
    StringDirection, RepeatStore, CpuId,
    VectorBinary, VectorMove, VectorHalfMove, VectorShiftBytes, VectorIntToDouble, VectorSignMask,
    VectorShuffleDwords, VectorTransfer,
    VectorImmediate, VectorByteOperation,
    FloatBinary, FloatCompare,
    FloatMask, IntegerToFloat, FloatToInteger, FloatingControl>;

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
    std::optional<std::size_t> tlsVector = {});
}
