#include "decode.h"

#include <array>
#include <format>
#include <utility>

namespace ir::decode {
namespace {
std::pair<Register, unsigned> byteRegister(unsigned index, bool rexPresent) {
    if (!rexPresent && index >= 4)
        return {Register{index - 4}, 8};
    return {Register{index}, 0};
}

constexpr auto x64Operations = std::to_array<std::optional<BinaryOp>>({
    BinaryOp::Add, BinaryOp::Or, {}, {}, BinaryOp::And, BinaryOp::Sub, BinaryOp::Xor, BinaryOp::Sub
});

EffectiveAddress x64Address(Reader& reader, unsigned mode, unsigned rm, unsigned rex,
    unsigned trailingBytes = 0) {
    unsigned base = rm + (rex & 1) * 8;
    unsigned index = Zero;
    unsigned scale = 1;
    if (rm == 4) {
        const auto sib = reader.read(1);
        if ((sib & 0x38) != 0x20 || (rex & 2))
            index = unsigned((sib >> 3) & 7) + (rex & 2) * 4;
        scale = 1u << (sib >> 6);
        rm = sib & 7;
        base = mode == 0 && rm == 5 ? Zero : rm + (rex & 1) * 8;
    } else if (mode == 0 && rm == 5) {
        const auto displacement = signExtend(reader.read(4), 32);
        return {Zero, reader.pc + displacement + trailingBytes};
    }

    Address displacement = 0;
    if (mode == 1)
        displacement = signExtend(reader.read(1), 8);
    else if (mode == 2 || base == Zero)
        displacement = signExtend(reader.read(4), 32);
    if (reader.segmented)
        displacement += reader.threadPointer;
    return {base, displacement, index, scale};
}

void skipMultiByteNop(Reader& reader, unsigned rex) {
    const auto modrm = reader.read(1);
    if ((modrm & 0x38) != 0)
        unsupported();
    if (modrm >> 6 != 3)
        x64Address(reader, unsigned(modrm >> 6), unsigned(modrm & 7), rex);
}

bool decodePrefixedNop(Reader& reader, unsigned prefix) {
    if (prefix != 0x66 && prefix != 0x2e)
        return false;
    auto lookahead = reader;
    auto opcode = lookahead.read(1);
    unsigned prefixes = 1;
    while (opcode == 0x66 || opcode == 0x2e) {
        if (++prefixes > 12)
            unsupported();
        opcode = lookahead.read(1);
    }
    if (opcode != 0x0f || lookahead.read(1) != 0x1f)
        return false;
    skipMultiByteNop(lookahead, 0);
    if (lookahead.pc - reader.pc + 1 > 15)
        unsupported();
    reader = lookahead;
    return true;
}

Instruction decodeExtend(Reader& reader, unsigned rex, bool rexPresent, unsigned destinationSize,
    unsigned sourceBits, bool sign) {
    const auto modrm = reader.read(1);
    const unsigned mode = modrm >> 6;
    const unsigned rm = modrm & 7;
    const unsigned dst = unsigned((modrm >> 3) & 7) + (rex & 4) * 2;
    if (mode != 3)
        return {Extend{destinationSize, dst, Memory{x64Address(reader, mode, rm, rex)}, sourceBits, 0, sign}};
    const bool highByte = sourceBits == 8 && !rexPresent && rm >= 4;
    return {Extend{destinationSize, dst, Register{highByte ? rm - 4 : rm + (rex & 1) * 8},
        sourceBits, highByte ? 8u : 0u, sign}};
}

Instruction decodeStackGuard(Reader& reader) {
    const auto rex = reader.read(1);
    if ((rex & 0xfa) != 0x48)
        unsupported();
    const auto opcode = reader.read(1);
    const auto modrm = reader.read(1);
    if ((modrm & 0xc7) != 4 || (reader.read(1) & 0x3f) != 0x25 || reader.read(4) != 0x28)
        unsupported();

    // Linux x86-64 places the stack guard at FS:[0x28].
    const unsigned reg = unsigned((modrm >> 3) & 7) + unsigned(rex & 4) * 2;
    if (opcode == 0x8b)
        return {Move{8, reg, StackGuard{}}};
    if ((opcode & 0xc7) == 3 && x64Operations[opcode >> 3]) {
        const auto op = opcode >> 3;
        return {Binary{*x64Operations[op], 8, op == 7 ? Zero : reg, reg, StackGuard{}, true}};
    }
    unsupported();
}


std::array<std::uint8_t, 16> interleave(unsigned element, bool high) {
    std::array<std::uint8_t, 16> bytes{};
    const unsigned base = high ? 8 : 0;
    for (unsigned i = 0; i < 8 / element; ++i)
        for (unsigned b = 0; b < element; ++b) {
            bytes[2 * i * element + b] = std::uint8_t(base + i * element + b);
            bytes[(2 * i + 1) * element + b] = std::uint8_t(16 + base + i * element + b);
        }
    return bytes;
}

Instruction decodeXmmEscape(Reader& reader, unsigned prefix, unsigned escape, unsigned rex) {
    const auto opcode = reader.read(1);
    const auto modrm = reader.read(1);
    const unsigned mode = modrm >> 6;
    const unsigned rm = modrm & 7;
    const VectorRegister reg{unsigned((modrm >> 3) & 7) + (rex & 4) * 2};
    const unsigned rmReg = rm + (rex & 1) * 8;
    const auto operandAt = [&](unsigned trailing) -> VectorOperand {
        if (mode == 3)
            return VectorRegister{rmReg};
        return VectorMemory{x64Address(reader, mode, rm, rex, trailing), false};
    };
    if (prefix != 0x66)
        unsupported();
    if (escape == 0x3a && (opcode == 0x0a || opcode == 0x0b)) {
        const auto operand = operandAt(1);
        const auto control = unsigned(reader.read(1));
        constexpr std::array modes{ScalarFloatOp::RoundNearestEven, ScalarFloatOp::Floor, ScalarFloatOp::Ceil,
            ScalarFloatOp::Truncate};
        const auto op = control & 4 ? ScalarFloatOp::RoundNearestEven : modes[control & 3];
        return {ScalarFloat{op, opcode == 0x0b ? 8u : 4u, reg, operand, std::nullopt, false}};
    }
    if (escape == 0x3a && (opcode == 0x0c || opcode == 0x0d)) {
        // BLENDPS/BLENDPD take each lane from the source when its immediate bit is set.
        const auto operand = operandAt(1);
        const auto control = unsigned(reader.read(1));
        const unsigned element = opcode == 0x0d ? 8 : 4;
        std::array<std::uint8_t, 16> bytes{};
        for (unsigned lane = 0; lane < 16 / element; ++lane)
            for (unsigned b = 0; b < element; ++b)
                bytes[lane * element + b] = std::uint8_t((control >> lane & 1 ? 16 : 0) + lane * element + b);
        return {VectorPermute{reg, reg, operand, bytes}};
    }
    if (escape == 0x3a && opcode == 0x0f) {
        // PALIGNR concatenates destination:source and shifts the pair right by whole bytes.
        const auto operand = operandAt(1);
        const auto count = unsigned(reader.read(1));
        std::array<std::uint8_t, 16> bytes{};
        for (unsigned i = 0; i < 16; ++i) {
            const auto index = i + count;
            bytes[i] = index < 16 ? std::uint8_t(16 + index) : index < 32 ? std::uint8_t(index - 16) : 255;
        }
        return {VectorPermute{reg, reg, operand, bytes}};
    }
    if (escape == 0x38 && opcode == 0x00)
        return {VectorLanes{LaneOp::ShuffleBytes, 1, reg, operandAt(0)}};
    if (escape == 0x38 && opcode == 0x2b)
        return {VectorLanes{LaneOp::PackUnsigned, 4, reg, operandAt(0)}};
    if (escape == 0x38 && opcode == 0x29)
        return {VectorLanes{LaneOp::Equal, 8, reg, operandAt(0)}};
    if (escape == 0x38 && opcode == 0x37)
        return {VectorLanes{LaneOp::GreaterSigned, 8, reg, operandAt(0)}};
    if (escape == 0x38 && (opcode == 0x14 || opcode == 0x15))
        return {VectorBlend{reg, operandAt(0), reg, VectorRegister{0}, true, opcode == 0x15 ? 8u : 4u}};
    unsupported();
}

Instruction decodeXmm(Reader& reader, unsigned prefix, unsigned opcode, unsigned rex) {
    const auto modrm = reader.read(1);
    const unsigned mode = modrm >> 6;
    const unsigned rm = modrm & 7;
    const VectorRegister reg{unsigned((modrm >> 3) & 7) + (rex & 4) * 2};
    const unsigned rmReg = rm + (rex & 1) * 8;
    const auto operandAt = [&](bool aligned, unsigned trailing = 0) -> VectorOperand {
        if (mode == 3)
            return VectorRegister{rmReg};
        return VectorMemory{x64Address(reader, mode, rm, rex, trailing), aligned};
    };
    if (prefix == 0x66 && (opcode == 0x71 || opcode == 0x72 || opcode == 0x73) && mode == 3) {
        const auto group = (modrm >> 3) & 7;
        if (opcode == 0x73 && (group == 3 || group == 7))
            return {VectorShiftBytes{VectorRegister{rmReg}, unsigned(reader.read(1)), group == 7}};
        if (group != 2 && group != 4 && group != 6)
            unsupported();
        const auto op = group == 2 ? ShiftOp::LogicalRight : group == 4 ? ShiftOp::ArithmeticRight : ShiftOp::Left;
        const unsigned element = opcode == 0x71 ? 2 : opcode == 0x72 ? 4 : 8;
        if (op == ShiftOp::ArithmeticRight && element == 8)
            unsupported();
        return {VectorShiftLanes{op, element, VectorRegister{rmReg}, VectorRegister{rmReg}, unsigned(reader.read(1))}};
    }
    if ((prefix == 0 || prefix == 0x66) && (opcode == 0x14 || opcode == 0x15)) {
        const unsigned element = prefix ? 8 : 4;
        return {VectorPermute{reg, reg, operandAt(true), interleave(element, opcode == 0x15)}};
    }
    if (prefix == 0x66 && ((opcode >= 0x60 && opcode <= 0x62) || (opcode >= 0x68 && opcode <= 0x6a) ||
        opcode == 0x6c || opcode == 0x6d)) {
        const unsigned element = opcode == 0x6c || opcode == 0x6d ? 8 : 1u << (opcode & 3);
        const bool high = opcode == 0x6d || (opcode >= 0x68 && opcode <= 0x6a);
        return {VectorPermute{reg, reg, operandAt(true), interleave(element, high)}};
    }
    if ((prefix == 0 || prefix == 0x66) && opcode == 0xc6) {
        const auto operand = operandAt(true, 1);
        const auto control = unsigned(reader.read(1));
        std::array<std::uint8_t, 16> bytes{};
        const auto pick = [&](unsigned slot, unsigned source, unsigned lane, unsigned element) {
            for (unsigned b = 0; b < element; ++b)
                bytes[slot * element + b] = std::uint8_t(source * 16 + lane * element + b);
        };
        if (prefix) {
            pick(0, 0, control & 1, 8);
            pick(1, 1, (control >> 1) & 1, 8);
        } else {
            pick(0, 0, control & 3, 4);
            pick(1, 0, (control >> 2) & 3, 4);
            pick(2, 1, (control >> 4) & 3, 4);
            pick(3, 1, (control >> 6) & 3, 4);
        }
        return {VectorPermute{reg, reg, operand, bytes}};
    }
    if ((prefix == 0x66 || prefix == 0xf2) && (opcode == 0x7c || opcode == 0x7d)) {
        // HADD/HSUB combine adjacent lanes: the destination's pairs fill the low half, the source's the high.
        const unsigned element = prefix == 0x66 ? 8 : 4;
        const auto operand = operandAt(true);
        std::array<std::uint8_t, 16> evens{}, odds{};
        for (unsigned lane = 0; lane < 16 / element; ++lane) {
            const auto source = lane < 8 / element ? 0u : 16u;
            const auto pair = (lane % (8 / element)) * 2;
            for (unsigned b = 0; b < element; ++b) {
                evens[lane * element + b] = std::uint8_t(source + pair * element + b);
                odds[lane * element + b] = std::uint8_t(source + (pair + 1) * element + b);
            }
        }
        const VectorRegister temp{VectorTemp};
        Instruction instruction{VectorPermute{temp, reg, operand, evens}};
        instruction.after.push_back(VectorPermute{reg, reg, operand, odds});
        instruction.after.push_back(VectorFloatLanes{opcode == 0x7c ? FloatLaneOp::Add : FloatLaneOp::Sub, element, reg,
            reg, temp});
        return instruction;
    }
    if (prefix == 0x66 && opcode == 0xd7 && mode == 3)
        return {VectorReduce{ReduceOp::SignMask, 1, reg, VectorRegister{rmReg}, 16, reg.index}};
    if (prefix == 0x66) {
        struct LaneForm { unsigned opcode; LaneOp op; unsigned element; };
        static constexpr std::array forms{
            LaneForm{0x74, LaneOp::Equal, 1}, LaneForm{0x75, LaneOp::Equal, 2}, LaneForm{0x76, LaneOp::Equal, 4},
            LaneForm{0x64, LaneOp::GreaterSigned, 1}, LaneForm{0x65, LaneOp::GreaterSigned, 2},
            LaneForm{0x66, LaneOp::GreaterSigned, 4}, LaneForm{0xfc, LaneOp::Add, 1}, LaneForm{0xfd, LaneOp::Add, 2},
            LaneForm{0xd4, LaneOp::Add, 8}, LaneForm{0xf8, LaneOp::Sub, 1}, LaneForm{0xf9, LaneOp::Sub, 2},
            LaneForm{0xfb, LaneOp::Sub, 8}, LaneForm{0xd5, LaneOp::Mul, 2}, LaneForm{0xf4, LaneOp::MulWideUnsigned, 8},
            LaneForm{0xe5, LaneOp::MulHighSigned, 2}, LaneForm{0xe4, LaneOp::MulHighUnsigned, 2},
            LaneForm{0xda, LaneOp::MinUnsigned, 1}, LaneForm{0xde, LaneOp::MaxUnsigned, 1},
            LaneForm{0xea, LaneOp::MinSigned, 2}, LaneForm{0xee, LaneOp::MaxSigned, 2},
            LaneForm{0xe0, LaneOp::AverageUnsigned, 1}, LaneForm{0xe3, LaneOp::AverageUnsigned, 2},
            LaneForm{0xd8, LaneOp::SubSaturateUnsigned, 1}, LaneForm{0xd9, LaneOp::SubSaturateUnsigned, 2},
            LaneForm{0xdc, LaneOp::AddSaturateUnsigned, 1}, LaneForm{0xdd, LaneOp::AddSaturateUnsigned, 2},
            LaneForm{0xe8, LaneOp::SubSaturateSigned, 1}, LaneForm{0xe9, LaneOp::SubSaturateSigned, 2},
            LaneForm{0xec, LaneOp::AddSaturateSigned, 1}, LaneForm{0xed, LaneOp::AddSaturateSigned, 2},
            LaneForm{0x63, LaneOp::PackSigned, 2}, LaneForm{0x6b, LaneOp::PackSigned, 4},
            LaneForm{0x67, LaneOp::PackUnsigned, 2},
        };
        for (const auto& form : forms)
            if (form.opcode == opcode)
                return {VectorLanes{form.op, form.element, reg, operandAt(true)}};
        struct ShiftForm { unsigned opcode; ShiftOp op; unsigned element; };
        static constexpr std::array shifts{
            ShiftForm{0xd1, ShiftOp::LogicalRight, 2}, ShiftForm{0xd2, ShiftOp::LogicalRight, 4},
            ShiftForm{0xd3, ShiftOp::LogicalRight, 8}, ShiftForm{0xe1, ShiftOp::ArithmeticRight, 2},
            ShiftForm{0xe2, ShiftOp::ArithmeticRight, 4}, ShiftForm{0xf1, ShiftOp::Left, 2},
            ShiftForm{0xf2, ShiftOp::Left, 4}, ShiftForm{0xf3, ShiftOp::Left, 8},
        };
        for (const auto& form : shifts)
            if (form.opcode == opcode)
                return {VectorShiftLanes{form.op, form.element, reg, reg, 0, operandAt(true)}};
    }
    if ((prefix == 0 || prefix == 0x66) && (opcode == 0x51 || opcode == 0x58 || opcode == 0x59 ||
        (opcode >= 0x5c && opcode <= 0x5f))) {
        const auto op = opcode == 0x51 ? FloatLaneOp::Sqrt : opcode == 0x58 ? FloatLaneOp::Add :
            opcode == 0x59 ? FloatLaneOp::Mul : opcode == 0x5c ? FloatLaneOp::Sub : opcode == 0x5d ? FloatLaneOp::Min :
            opcode == 0x5e ? FloatLaneOp::Div : FloatLaneOp::Max;
        return {VectorFloatLanes{op, prefix ? 8u : 4u, reg, operandAt(true)}};
    }
    if ((prefix == 0 || prefix == 0x66) && opcode == 0xc2) {
        const auto operand = operandAt(true, 1);
        constexpr std::array predicates{FloatLaneOp::Equal, FloatLaneOp::Less, FloatLaneOp::LessEqual,
            FloatLaneOp::Unordered, FloatLaneOp::NotEqual, FloatLaneOp::NotLess, FloatLaneOp::NotLessEqual,
            FloatLaneOp::Ordered};
        return {VectorFloatLanes{predicates[reader.read(1) & 7], prefix ? 8u : 4u, reg, operand}};
    }
    if (opcode == 0x5a && (prefix == 0 || prefix == 0x66))
        return {VectorConvert{prefix ? LaneConversion::DoubleToFloat : LaneConversion::FloatToDouble, reg,
            operandAt(false), prefix ? 8u : 4u}};
    if (opcode == 0x5b && (prefix == 0 || prefix == 0xf3))
        return {VectorConvert{prefix ? LaneConversion::FloatToInt32Truncate : LaneConversion::Int32ToFloat, reg,
            operandAt(true), 4}};
    if (opcode == 0xe6 && prefix == 0x66)
        return {VectorConvert{LaneConversion::DoubleToInt32Truncate, reg, operandAt(true), 8}};
    if (prefix == 0x66 && (opcode == 0x10 || opcode == 0x11)) {
        const auto operand = operandAt(false);
        if (opcode == 0x11)
            return {VectorMove{operand, reg}};
        return {VectorMove{reg, operand}};
    }
    if (prefix == 0xf3 && opcode == 0xe6)
        return {VectorIntToDouble{reg, operandAt(false)}};
    if ((prefix == 0x66 || prefix == 0xf2 || prefix == 0xf3) && opcode == 0x70) {
        const auto operand = operandAt(false, 1);
        return {VectorShuffle{reg, operand, unsigned(reader.read(1)),
            prefix == 0x66 ? std::nullopt : std::optional(prefix == 0xf3)}};
    }
    if ((prefix == 0 || prefix == 0x66) && opcode == 0x50 && mode == 3)
        return {VectorSignMask{reg.index, VectorRegister{rmReg}, prefix ? 8u : 4u}};
    if ((prefix == 0 || prefix == 0x66) &&
        (opcode == 0x12 || opcode == 0x13 || opcode == 0x16 || opcode == 0x17)) {
        const bool high = opcode >= 0x16;
        const bool store = opcode & 1;
        if (mode == 3 && (prefix || store))
            unsupported();
        const auto other = operandAt(false);
        if (store)
            return {VectorHalfMove{other, reg, false, high}};
        return {VectorHalfMove{reg, other, high, mode == 3 && !high}};
    }
    if ((prefix == 0 || prefix == 0x66) && (opcode == 0x2e || opcode == 0x2f))
        return {FloatCompare{prefix ? 8u : 4u, reg, operandAt(false)}};
    if ((prefix == 0xf2 || prefix == 0xf3)) {
        const unsigned width = prefix == 0xf2 ? 8 : 4;
        const unsigned integerSize = rex & 8 ? 8 : 4;
        if (opcode == 0xc2) {
            const auto from = operandAt(false, 1);
            return {FloatMask{width, reg, from, unsigned(reader.read(1) & 7)}};
        }
        if (opcode == 0x2a) {
            const Value from = mode == 3 ? Value(Register{rmReg}) : Value(Memory{x64Address(reader, mode, rm, rex)});
            return {IntegerToFloat{width, reg, integerSize, from}};
        }
        if (opcode == 0x2c)
            return {FloatToInteger{integerSize, reg.index, width, operandAt(false)}};
        if (opcode == 0x5a)
            return {FloatBinary{FloatOp::Convert, 12 - width, width, reg, operandAt(false)}};
        if (opcode == 0x51)
            return {FloatBinary{FloatOp::Sqrt, width, width, reg, operandAt(false)}};
        if (opcode == 0x58 || opcode == 0x59 || (opcode >= 0x5c && opcode <= 0x5f)) {
            const auto arithmetic = opcode == 0x58 ? FloatOp::Add : opcode == 0x59 ? FloatOp::Mul :
                opcode == 0x5c ? FloatOp::Sub : opcode == 0x5d ? FloatOp::Min :
                opcode == 0x5e ? FloatOp::Div : FloatOp::Max;
            return {FloatBinary{arithmetic, width, width, reg, operandAt(false)}};
        }
    }
    if ((prefix == 0xf2 || prefix == 0xf3) && (opcode == 0x10 || opcode == 0x11)) {
        const VectorOperand operand = mode == 3 ? VectorOperand(VectorRegister{rmReg})
            : VectorOperand(VectorMemory{x64Address(reader, mode, rm, rex), false});
        const unsigned width = prefix == 0xf2 ? 8 : 4;
        if (opcode == 0x11)
            return {VectorMove{operand, reg, width, mode == 3}};
        return {VectorMove{reg, operand, width, mode == 3}};
    }
    if (prefix == 0x66 && (opcode == 0x6e || opcode == 0x7e)) {
        const unsigned width = rex & 8 ? 8 : 4;
        if (mode == 3)
            return {VectorTransfer{Register{rmReg}, reg, opcode == 0x6e, width}};
        const auto memory = operandAt(false);
        if (opcode == 0x7e)
            return {VectorMove{memory, reg, width}};
        return {VectorMove{reg, memory, width}};
    }
    if (prefix == 0x66 && opcode == 0xc5 && mode == 3)
        return {VectorTransfer{Register{reg.index}, VectorRegister{rmReg}, false, 2, unsigned(reader.read(1) & 7)}};

    if ((prefix == 0xf3 && opcode == 0x7e) || (prefix == 0x66 && opcode == 0xd6)) {
        const VectorOperand operand = mode == 3 ? VectorOperand(VectorRegister{rmReg})
            : VectorOperand(VectorMemory{x64Address(reader, mode, rm, rex), false});
        if (opcode == 0xd6)
            return {VectorMove{operand, reg, 8}};
        return {VectorMove{reg, operand, 8}};
    }

    const bool alignedMoves = ((prefix == 0 || prefix == 0x66) && (opcode == 0x28 || opcode == 0x29)) ||
        (prefix == 0x66 && (opcode == 0x6f || opcode == 0x7f));
    const bool unalignedMoves = (prefix == 0 && (opcode == 0x10 || opcode == 0x11)) ||
        (prefix == 0xf3 && (opcode == 0x6f || opcode == 0x7f));
    const bool logical = (prefix == 0 || prefix == 0x66) && (opcode >= 0x54 && opcode <= 0x57);
    const bool binary = logical || (prefix == 0x66 && (opcode == 0xdb || opcode == 0xdf || opcode == 0xeb ||
        opcode == 0xef || opcode == 0x62 || opcode == 0x6c || opcode == 0xfe || opcode == 0xfa));
    if (!alignedMoves && !unalignedMoves && !binary)
        unsupported();
    const VectorOperand operand = mode == 3 ? VectorOperand(VectorRegister{rmReg})
        : VectorOperand(VectorMemory{x64Address(reader, mode, rm, rex), !unalignedMoves});
    if (binary) {
        const auto kind = opcode == 0xfe ? VectorOp::AddDwords : opcode == 0xfa ? VectorOp::SubDwords :
            opcode == 0x62 ? VectorOp::UnpackLowDwords :
            opcode == 0x6c ? VectorOp::UnpackLowQwords : opcode == 0x54 || opcode == 0xdb ? VectorOp::And :
            opcode == 0x55 || opcode == 0xdf ? VectorOp::AndNot :
            opcode == 0x56 || opcode == 0xeb ? VectorOp::Or : VectorOp::Xor;
        return {VectorBinary{kind, reg, operand}};
    }
    if (opcode == 0x29 || opcode == 0x11 || opcode == 0x7f)
        return {VectorMove{operand, reg}};
    return {VectorMove{reg, operand}};
}

Instruction decodeX64Prefix(Reader& reader, unsigned prefix) {
    auto opcode = reader.read(1);
    while (prefix == 0x66 && opcode == 0x66)
        opcode = reader.read(1);
    unsigned rex = 0;
    const bool rexPresent = opcode >= 0x40 && opcode <= 0x4f;
    if (rexPresent) {
        rex = opcode & 15;
        opcode = reader.read(1);
    }
    if (prefix == 0xf3 && (opcode == 0xaa || opcode == 0xab))
        return {RepeatStore{opcode == 0xaa ? 1u : (rex & 8) ? 8u : 4u}};
    if (prefix == 0xf3 && opcode == 0xc3)
        return {.end = Return{StackTop{}}};
    if (prefix == 0xf3 && (opcode == 0xa4 || opcode == 0xa5))
        return {StringMove{opcode == 0xa4 ? 1u : (rex & 8) ? 8u : 4u, true}};
    if (prefix == 0x66 && opcode == 0x90 && !(rex & 1))
        return {};
    if (prefix == 0x66 && (rex & 8) && opcode == 0xe8) {
        const auto displacement = signExtend(reader.read(4), 32);
        return {.end = Call{immediate(reader.pc + displacement), reader.pc}};
    }
    if (prefix == 0x66 && (rex & 8) && opcode == 0x8d) {
        const auto modrm = reader.read(1);
        const unsigned mode = modrm >> 6;
        const unsigned rm = modrm & 7;
        if (mode == 3)
            unsupported();
        const auto at = x64Address(reader, mode, rm, rex);
        Instruction instruction{Move{8, unsigned((modrm >> 3) & 7) + (rex & 4) * 2, at}};
        if (mode == 0 && rm == 5 && reader.mapped)
            instruction.addressTaken = at.displacement;
        return instruction;
    }
    if (opcode == 0x0f) {
        const auto extension = reader.read(1);
        if (extension == 0x1e) {
            // The hint-NOP group: ENDBR32/64, and RDSSPD/Q, which leave their register unchanged while
            // control-flow enforcement is off, so guests skip their shadow-stack paths.
            const auto modrm = reader.read(1);
            if ((modrm >> 6) != 3)
                x64Address(reader, modrm >> 6, modrm & 7, rex);
            return {};
        }
        if (prefix == 0xf3 && (extension == 0xb8 || extension == 0xbc || extension == 0xbd)) {
            const auto modrm = reader.read(1);
            const unsigned mode = modrm >> 6;
            const unsigned rm = modrm & 7;
            const unsigned dst = unsigned((modrm >> 3) & 7) + (rex & 4) * 2;
            const Value operand = mode == 3 ? Value(Register{rm + (rex & 1) * 8})
                : Value(Memory{x64Address(reader, mode, rm, rex)});
            return {BitScan{rex & 8 ? 8u : 4u, dst, operand, extension == 0xbd, false, extension != 0xb8,
                extension == 0xb8}};
        }
        if (prefix == 0x66 && !(rex & 8) && (extension == 0xb6 || extension == 0xbe)) {
            // MOVZX and MOVSX into a 16-bit register: extend into a temporary and merge its low word.
            auto instruction = decodeExtend(reader, rex, rexPresent, 4, 8, extension == 0xbe);
            auto& extend = std::get<Extend>(instruction.effect);
            const auto target = extend.dst;
            extend.dst = Temp;
            instruction.after.push_back(Move{2, target, Register{Temp}});
            return instruction;
        }
        if (prefix == 0x66 && extension == 0x1f) {
            skipMultiByteNop(reader, rex);
            return {};
        }
        if (extension == 0x38 || extension == 0x3a)
            return decodeXmmEscape(reader, prefix, extension, rex);
        return decodeXmm(reader, prefix, extension, rex);
    }
    if (prefix == 0x66 && !(rex & 8) && (opcode == 0x89 || opcode == 0x8b)) {
        const auto modrm = reader.read(1);
        const unsigned mode = modrm >> 6;
        const unsigned rm = modrm & 7;
        const unsigned reg = unsigned((modrm >> 3) & 7) + (rex & 4) * 2;
        const unsigned rmReg = rm + (rex & 1) * 8;
        if (mode == 3)
            return opcode == 0x89 ? Instruction{Move{2, rmReg, Register{reg}}}
                                  : Instruction{Move{2, reg, Register{rmReg}}};
        const auto addr = x64Address(reader, mode, rm, rex);
        if (opcode == 0x89)
            return {Store{2, addr, Register{reg}}};
        return {Move{2, reg, Memory{addr}}};
    }
    if (prefix == 0x66 && !(rex & 8) && opcode >= 0xb8 && opcode <= 0xbf)
        return {Move{2, unsigned(opcode & 7) + (rex & 1) * 8, Immediate{reader.read(2)}}};
    if (prefix == 0x66 && !(rex & 8) && (opcode & 0xc7) == 5 && x64Operations[opcode >> 3]) {
        const auto op = opcode >> 3;
        return {MemoryBinary{*x64Operations[op], 2, Register{0}, Immediate{reader.read(2)}, op != 7}};
    }
    if (prefix == 0x66 && !(rex & 8) && opcode == 0xc7) {
        const auto modrm = reader.read(1);
        const unsigned mode = modrm >> 6;
        const unsigned rm = modrm & 7;
        if (modrm & 0x38)
            unsupported();
        if (mode == 3)
            return {Move{2, rm + (rex & 1) * 8, Immediate{reader.read(2)}}};
        const auto address = x64Address(reader, mode, rm, rex, 2);
        return {Store{2, address, Immediate{reader.read(2)}}};
    }
    if ((prefix == 0x66 && opcode == 0xf3) || (prefix == 0xf3 && opcode == 0x66)) {
        if (reader.read(1) == 0xab)
            return {RepeatStore{2}};
        unsupported();
    }
    if (prefix == 0x66 && !(rex & 8) && (opcode == 0xc1 || opcode == 0xd1 || opcode == 0xd3)) {
        const auto modrm = reader.read(1);
        const unsigned group = (modrm >> 3) & 7;
        const unsigned target = unsigned(modrm & 7) + (rex & 1) * 8;
        if (modrm >> 6 != 3 || group == 2 || group == 3 || group == 6)
            unsupported();
        const auto op = group == 0 ? ShiftOp::RotateLeft : group == 1 ? ShiftOp::RotateRight :
            group == 4 ? ShiftOp::Left : group == 5 ? ShiftOp::LogicalRight : ShiftOp::ArithmeticRight;
        // Widen the word into a temporary, shift it as 32 bits, and merge the low half back.
        Instruction instruction{Extend{4, Temp, Register{target}, 16, 0, op == ShiftOp::ArithmeticRight}};
        if (op == ShiftOp::RotateLeft || op == ShiftOp::RotateRight)
            instruction.after.push_back(Binary{BinaryOp::Or, 4, Temp, Temp, Register{Temp}, false, ShiftOp::Left, 16});
        if (opcode == 0xd3) {
            instruction.after.push_back(ShiftRegister{op, 4, Temp, Register{Temp}, Register{1}});
        } else {
            const auto count = opcode == 0xd1 ? 1u : unsigned(reader.read(1)) & 31u;
            if (count == 0)
                return {};
            instruction.after.push_back(Shift{op, 4, Register{Temp}, (op == ShiftOp::RotateLeft ||
                op == ShiftOp::RotateRight) ? count % 16 : count});
        }
        instruction.after.push_back(Move{2, target, Register{Temp}});
        return instruction;
    }
    if (prefix == 0x66 && !(rex & 8) && opcode == 0xf7) {
        auto lookahead = reader;
        const auto group = (lookahead.read(1) >> 3) & 7;
        if (group == 2 || group == 3) {
            const auto modrm = reader.read(1);
            const unsigned mode = modrm >> 6;
            const unsigned rm = modrm & 7;
            const Value target = mode == 3 ? Value(Register{rm + (rex & 1) * 8}) :
                Value(Memory{x64Address(reader, mode, rm, rex)});
            if (group == 2)
                return {MemoryBinary{BinaryOp::Xor, 2, target, Immediate{0xffff}, true, false, false}};
            Instruction instruction{Move{8, Temp, Immediate{0}}};
            instruction.after.push_back(MemoryBinary{BinaryOp::Sub, 2, Register{Temp}, target, true});
            if (const auto* reg = std::get_if<Register>(&target))
                instruction.after.push_back(Move{2, reg->index, Register{Temp}});
            else
                instruction.after.push_back(Store{2, std::get<Memory>(target).address, Register{Temp}});
            return instruction;
        }
    }
    if (prefix == 0x66 && !(rex & 8) && opcode == 0xff) {
        const auto modrm = reader.read(1);
        const unsigned mode = modrm >> 6;
        const unsigned rm = modrm & 7;
        const unsigned group = (modrm >> 3) & 7;
        if (group > 1)
            unsupported();
        const Value target = mode == 3 ? Value(Register{rm + (rex & 1) * 8}) :
            Value(Memory{x64Address(reader, mode, rm, rex)});
        return {MemoryBinary{group ? BinaryOp::Sub : BinaryOp::Add, 2, target, Immediate{1}, true, true}};
    }
    const bool registerAlu = (opcode & 0xc5) == 1 && x64Operations[opcode >> 3].has_value();
    const bool carryAlu = (opcode & 0xf5) == 0x11;
    if (prefix == 0x66 && !(rex & 8) &&
        (opcode == 0x81 || opcode == 0x83 || opcode == 0x85 || opcode == 0xf7 || registerAlu || carryAlu)) {
        const auto modrm = reader.read(1);
        const unsigned mode = modrm >> 6;
        const unsigned rm = modrm & 7;
        const unsigned group = (modrm >> 3) & 7;
        const Register reg{group + (rex & 4) * 2};
        const bool immediateAlu = opcode == 0x81 || opcode == 0x83 || opcode == 0xf7;
        if (opcode == 0xf7 && group != 0)
            unsupported();
        const unsigned bytes = !immediateAlu ? 0 : opcode == 0x83 ? 1 : 2;
        const Value operand = mode == 3 ? Value(Register{rm + (rex & 1) * 8}) :
            Value(Memory{x64Address(reader, mode, rm, rex, bytes)});
        if (immediateAlu) {
            if (opcode == 0xf7)
                return {MemoryBinary{BinaryOp::And, 2, operand, Immediate{reader.read(2)}, false}};
            const auto source = immediate(signExtend(reader.read(bytes), bytes * 8));
            if (group == 2 || group == 3)
                return {MemoryBinary{group == 2 ? BinaryOp::Add : BinaryOp::Sub, 2, operand, source, true, false, true, true}};
            if (!x64Operations[group])
                unsupported();
            return {MemoryBinary{*x64Operations[group], 2, operand, source, group != 7}};
        }
        if (opcode == 0x85)
            return {MemoryBinary{BinaryOp::And, 2, operand, reg, false}};
        if (carryAlu) {
            const auto op = opcode & 8 ? BinaryOp::Sub : BinaryOp::Add;
            if (opcode & 2)
                return {MemoryBinary{op, 2, reg, operand, true, false, true, true}};
            return {MemoryBinary{op, 2, operand, reg, true, false, true, true}};
        }
        const auto op = opcode >> 3;
        if (opcode & 2)
            return {MemoryBinary{*x64Operations[op], 2, reg, operand, op != 7}};
        return {MemoryBinary{*x64Operations[op], 2, operand, reg, op != 7}};
    }
    unsupported();
}

}

Instruction decodeX64(Reader& reader) {
    auto opcode = reader.read(1);
    const bool locked = opcode == 0xf0;
    if (locked)
        opcode = reader.read(1);
    if (opcode == 0x64 && !locked) {
        const auto start = reader.pc;
        try {
            return decodeStackGuard(reader);
        } catch (const std::runtime_error&) {
        }
        // Other FS-relative accesses reach thread-local storage at the thread pointer.
        if (!reader.threadPointer || reader.segmented)
            unsupported();
        reader.pc = start;
        reader.segmented = true;
        auto instruction = decodeX64(reader);
        reader.segmented = false;
        return instruction;
    }
    if (opcode == 0x65 && !locked) {
        // Only absolute GS loads appear in compiled Windows code: mov reg, gs:[disp32].
        auto operation = reader.read(1);
        unsigned rex = 0;
        if (operation >= 0x40 && operation <= 0x4f) {
            rex = operation & 15;
            operation = reader.read(1);
        }
        const auto destination = reader.read(1);
        if (operation == 0x8b && (destination & 0xc7) == 4 && reader.read(1) == 0x25) {
            const auto reg = unsigned((destination >> 3) & 7) + unsigned(rex & 4) * 2;
            return {Move{rex & 8 ? 8u : 4u, reg, ThreadLocalStorage{signExtend(reader.read(4), 32)}}};
        }
        unsupported();
    }
    if (decodePrefixedNop(reader, opcode))
        return {};
    const bool notrack = opcode == 0x3e;
    if (notrack)
        opcode = reader.read(1);
    const bool address32 = opcode == 0x67;
    if (address32)
        opcode = reader.read(1);
    if (opcode == 0x66 || opcode == 0xf2 || opcode == 0xf3)
        return decodeX64Prefix(reader, opcode);
    unsigned rex = 0;
    const bool rexPresent = opcode >= 0x40 && opcode <= 0x4f;
    if (rexPresent) {
        rex = opcode & 15;
        opcode = reader.read(1);
    }
    const bool lockableRegister = (opcode & 0xc7) == 1 && x64Operations[opcode >> 3] && (opcode >> 3) != 7;
    const bool lockableImmediate = opcode == 0x81 || opcode == 0x83;
    if ((locked && opcode != 0x0f && opcode != 0xff && !lockableRegister && !lockableImmediate) ||
        (notrack && opcode != 0xff))
        unsupported();
    const unsigned size = rex & 8 ? 8 : 4;
    if (address32 && (locked || size != 4 || opcode != 0x8d))
        unsupported();
    if (opcode >= 0x90 && opcode <= 0x97) {
        const unsigned other = unsigned(opcode & 7) + (rex & 1) * 8;
        if (other == 0)
            return {};
        return {Exchange{size, Register{0}, Register{other}}};
    }
    if (opcode == 0x63 && size == 8)
        return decodeExtend(reader, rex, rexPresent, 8, 32, true);
    if (opcode >= 0xb8 && opcode <= 0xbf)
        return {Move{size, unsigned(opcode & 7) + (rex & 1) * 8, Immediate{reader.read(size)}}};
    if (opcode >= 0xb0 && opcode <= 0xb7) {
        const auto [dst, field] = byteRegister(unsigned(opcode & 7) + (rex & 1) * 8, rexPresent);
        return {ByteMove{dst, field, Immediate{reader.read(1)}, 0}};
    }
    if (opcode >= 0x50 && opcode <= 0x57)
        return {Push{Register{unsigned(opcode & 7) + (rex & 1) * 8}}};
    if (opcode == 0x6a)
        return {Push{immediate(signExtend(reader.read(1), 8))}};
    if (opcode == 0x68)
        return {Push{immediate(signExtend(reader.read(4), 32))}};
    if (opcode == 0xa4 || opcode == 0xa5)
        return {StringMove{opcode == 0xa4 ? 1u : size, false}};
    if (opcode == 0xcc || opcode == 0xf4)
        return {.end = Trap{std::format("guest trap instruction at guest offset {}", reader.pc - 1)}};
    if (opcode >= 0x58 && opcode <= 0x5f)
        return {Move{8, unsigned(opcode & 7) + (rex & 1) * 8, StackTop{}}};

    switch (opcode) {
        case 0xfc:
        case 0xfd:
            return {StringDirection{opcode == 0xfd}};
        case 0xa8:
            return {ByteBinary{BinaryOp::And, Register{0}, 0, Immediate{reader.read(1)}, 0}};
        case 0xa9:
            return {Binary{BinaryOp::And, size, Zero, 0, immediate(signExtend(reader.read(4), 32)), true}};
        case 0xc3:
            return {.end = Return{StackTop{}}};
        case 0xc2:
            return {.end = Return{StackTop{}, unsigned(reader.read(2))}};
        case 0x98:
            return {Extend{size, 0, Register{0}, size == 8 ? 32u : 16u, 0, true}};
        case 0x99:
            return {Bitfield{size, 2, Register{0}, size * 8 - 1, 1, 0, true}};
        case 0xc9:
            return {.effect = Move{8, 4, Register{5}}, .after = {Move{8, 5, StackTop{}}}};
        case 0xd8: case 0xd9: case 0xda: case 0xdb: case 0xdc: case 0xdd: case 0xde: case 0xdf: {
            const auto modrm = unsigned(reader.read(1));
            const auto mode = modrm >> 6;
            const auto group = (modrm >> 3) & 7;
            if (mode == 3)
                return {X87{unsigned(opcode), modrm, std::nullopt}};
            if (opcode == 0xd9 && (group == 5 || group == 7))
                return {FloatingControl{x64Address(reader, mode, modrm & 7, rex), 2, group == 5}};
            if ((opcode == 0xd9 && (group == 4 || group == 6)) || (opcode == 0xdd && (group == 4 || group == 6)))
                unsupported();
            return {X87{unsigned(opcode), modrm & 0x38, x64Address(reader, mode, modrm & 7, rex)}};
        }
        case 0x9b:
            return {};
        case 0xe8:
        case 0xe9:
        case 0xeb: {
            const unsigned bytes = opcode == 0xeb ? 1 : 4;
            const auto displacement = signExtend(reader.read(bytes), 8 * bytes);
            const auto target = immediate(reader.pc + displacement);
            if (opcode == 0xe8)
                return {.end = Call{target, reader.pc}};
            return {.end = Jump{target}};
        }
        case 0x0f: {
            const auto extension = reader.read(1);
            if (extension == 0xc1) {
                const auto modrm = reader.read(1);
                const unsigned mode = modrm >> 6;
                const unsigned rm = modrm & 7;
                const unsigned source = unsigned((modrm >> 3) & 7) + (rex & 4) * 2;
                if (locked && mode == 3)
                    unsupported();
                const Value target = mode == 3 ? Value(Register{rm + (rex & 1) * 8}) :
                    Value(Memory{x64Address(reader, mode, rm, rex)});
                return {Exchange{size, target, Register{source}, true}};
            }
            if (extension == 0xb1) {
                const auto modrm = reader.read(1);
                const unsigned mode = modrm >> 6;
                if (mode == 3)
                    unsupported();
                const unsigned source = unsigned((modrm >> 3) & 7) + (rex & 4) * 2;
                return {CompareExchange{size, x64Address(reader, mode, modrm & 7, rex), Register{source}}};
            }
            if (locked)
                unsupported();
            if (extension == 0x0b)
                return {.end = Trap{std::format("guest trap instruction at guest offset {}", reader.pc - 2)}};
            if (extension == 0xa5 || extension == 0xad) {
                const auto modrm = reader.read(1);
                if (modrm >> 6 != 3)
                    unsupported();
                const unsigned target = unsigned(modrm & 7) + (rex & 1) * 8;
                const unsigned source = unsigned((modrm >> 3) & 7) + (rex & 4) * 2;
                return {DoubleShift{size, target, Register{source}, extension == 0xa5}};
            }
            if (extension == 0xa4 || extension == 0xac) {
                const auto modrm = reader.read(1);
                if (modrm >> 6 != 3)
                    unsupported();
                const unsigned target = unsigned(modrm & 7) + (rex & 1) * 8;
                const unsigned source = unsigned((modrm >> 3) & 7) + (rex & 4) * 2;
                const auto count = unsigned(reader.read(1)) & (size == 8 ? 63u : 31u);
                if (count == 0)
                    return {};
                // SHLD shifts the destination left and fills from the source; SHRD is the mirror image.
                if (extension == 0xa4)
                    return {Extract{size, target, Register{target}, Register{source}, size * 8 - count}};
                return {Extract{size, target, Register{source}, Register{target}, count}};
            }
            if (extension >= 0xc8 && extension <= 0xcf) {
                const auto target = unsigned(extension & 7) + (rex & 1) * 8;
                return {ByteSwap{size, target, Register{target}}};
            }
            if (extension == 0xae) {
                const auto modrm = reader.read(1);
                const auto mode = unsigned(modrm >> 6);
                const auto group = (modrm >> 3) & 7;
                if (mode == 3 || (group != 2 && group != 3))
                    unsupported();
                return {FloatingControl{x64Address(reader, mode, modrm & 7, rex), 4, group == 2}};
            }
            if (extension == 0xa2)
                return {CpuId{}};
            if (extension == 0x1f) {
                skipMultiByteNop(reader, rex);
                return {};
            }
            if (extension == 0xb6 || extension == 0xb7 || extension == 0xbe || extension == 0xbf)
                return decodeExtend(reader, rex, rexPresent, size, extension & 1 ? 16 : 8,
                    extension == 0xbe || extension == 0xbf);
            if (extension == 0xbc || extension == 0xbd) {
                const auto modrm = reader.read(1);
                const unsigned mode = modrm >> 6;
                const unsigned rm = modrm & 7;
                const unsigned dst = unsigned((modrm >> 3) & 7) + (rex & 4) * 2;
                const Value operand = mode == 3 ? Value(Register{rm + (rex & 1) * 8})
                    : Value(Memory{x64Address(reader, mode, rm, rex)});
                return {BitScan{size, dst, operand, extension == 0xbd}};
            }
            if (extension >= 0x40 && extension <= 0x4f) {
                const auto modrm = reader.read(1);
                const unsigned mode = modrm >> 6;
                const unsigned rm = modrm & 7;
                const unsigned dst = unsigned((modrm >> 3) & 7) + (rex & 4) * 2;
                const Value src = mode == 3 ? Value(Register{rm + (rex & 1) * 8})
                                           : Value(Memory{x64Address(reader, mode, rm, rex)});
                return {ConditionalMove{size, dst, src, unsigned(extension & 15)}};
            }
            if (extension >= 0x90 && extension <= 0x9f) {
                const auto modrm = reader.read(1);
                const unsigned mode = modrm >> 6;
                const unsigned rm = modrm & 7;
                const bool highByte = mode == 3 && !rexPresent && rm >= 4;
                const Value dst = mode == 3 ?
                    Value(Register{highByte ? rm - 4 : rm + (rex & 1) * 8}) :
                    Value(Memory{x64Address(reader, mode, rm, rex)});
                return {SetCondition{dst, highByte ? 8u : 0u, unsigned(extension & 15)}};
            }
            if (extension == 0xaf) {
                const auto modrm = reader.read(1);
                const unsigned mode = modrm >> 6;
                const unsigned rm = modrm & 7;
                const unsigned dst = unsigned((modrm >> 3) & 7) + (rex & 4) * 2;
                const Value rhs = mode == 3 ? Value(Register{rm + (rex & 1) * 8})
                                           : Value(Memory{x64Address(reader, mode, rm, rex)});
                return {Multiply{size, dst, Register{dst}, rhs}};
            }
            if (extension == 0xa3 || extension == 0xab || extension == 0xb3 || extension == 0xbb || extension == 0xba) {
                const auto modrm = reader.read(1);
                const auto mode = unsigned(modrm >> 6);
                const auto rm = unsigned(modrm & 7);
                const auto group = unsigned((modrm >> 3) & 7);
                if (extension == 0xba) {
                    if (group < 4)
                        unsupported();
                    const Value dst = mode == 3 ? Value(Register{rm + (rex & 1) * 8})
                                               : Value(Memory{x64Address(reader, mode, rm, rex, 1)});
                    return {BitTest{size, dst, Immediate{reader.read(1)}, BitAction(group - 4)}};
                }
                if (mode != 3)
                    unsupported();
                const auto action = extension == 0xa3 ? BitAction::Test : extension == 0xab ? BitAction::Set :
                    extension == 0xb3 ? BitAction::Reset : BitAction::Toggle;
                return {BitTest{size, Register{rm + (rex & 1) * 8}, Register{group + (rex & 4) * 2}, action}};
            }
            if ((extension >= 0x10 && extension <= 0x17) || extension == 0x28 || extension == 0x29 ||
                extension == 0x2e || extension == 0x2f || extension == 0x50 || extension == 0x51 ||
                (extension >= 0x54 && extension <= 0x5f) || extension == 0xc2 || extension == 0xc6)
                return decodeXmm(reader, 0, extension, rex);
            if (extension < 0x80 || extension > 0x8f)
                unsupported();
            const auto displacement = signExtend(reader.read(4), 32);
            return {.end = Branch{FlagsCondition{unsigned(extension & 15)}, reader.pc + displacement, reader.pc}};
        }
    }
    if (opcode >= 0x70 && opcode <= 0x7f) {
        const auto displacement = signExtend(reader.read(1), 8);
        return {.end = Branch{FlagsCondition{unsigned(opcode & 15)}, reader.pc + displacement, reader.pc}};
    }

    if ((opcode & 0xc7) == 5 && x64Operations[opcode >> 3]) {
        const auto op = opcode >> 3;
        return {Binary{*x64Operations[op], size, op == 7 ? Zero : 0, 0, immediate(signExtend(reader.read(4), 32)), true}};
    }
    // ADC and SBB with the accumulator.
    if (opcode == 0x15 || opcode == 0x1d)
        return {Binary{opcode == 0x15 ? BinaryOp::Add : BinaryOp::Sub, size, 0, 0, immediate(signExtend(reader.read(4), 32)),
            true, ShiftOp::Left, 0, false, 0, false, true}};
    if ((opcode & 0xc7) == 4 && x64Operations[opcode >> 3]) {
        const auto op = opcode >> 3;
        return {ByteBinary{*x64Operations[op], Register{0}, 0, Immediate{reader.read(1)}, 0, op != 7}};
    }
    if (opcode == 0x14 || opcode == 0x1c) {
        ByteBinary binary{opcode == 0x14 ? BinaryOp::Add : BinaryOp::Sub, Register{0}, 0, Immediate{reader.read(1)}, 0, true};
        binary.withCarry = true;
        return {binary};
    }

    const bool registerAlu = (opcode & 0xc5) == 1 && x64Operations[opcode >> 3].has_value();
    // ADC and SBB on bytes: 0x10, 0x12, 0x18, 0x1a.
    const bool byteCarry = (opcode & 0xf5) == 0x10;
    const bool byteAlu = ((opcode & 0xc5) == 0 && x64Operations[opcode >> 3].has_value()) || byteCarry;
    const bool carryAlu = (opcode & 0xf5) == 0x11;
    if (!registerAlu && !byteAlu && !carryAlu && opcode != 0x69 && opcode != 0x6b && opcode != 0x80 && opcode != 0x81 && opcode != 0x83 &&
        opcode != 0x84 && opcode != 0x85 && opcode != 0x87 &&
        opcode != 0x88 && opcode != 0x89 && opcode != 0x8a &&
        opcode != 0x8b && opcode != 0x8d &&
        opcode != 0xc0 && opcode != 0xc1 && opcode != 0xc6 && opcode != 0xc7 &&
        opcode != 0xd0 && opcode != 0xd1 && opcode != 0xd2 && opcode != 0xd3 &&
        opcode != 0xf6 && opcode != 0xf7 && opcode != 0xfe && opcode != 0xff)
        unsupported();
    const auto modrm = reader.read(1);
    const unsigned mode = modrm >> 6;
    const unsigned rm = modrm & 7;
    const unsigned group = (modrm >> 3) & 7;
    const unsigned dst = rm + (rex & 1) * 8;
    const unsigned src = group + (rex & 4) * 2;
    if (locked && (mode == 3 || (opcode == 0xff && group > 1) ||
        (lockableImmediate && (!x64Operations[group] || group == 7))))
        unsupported();
    if (notrack && group != 2 && group != 4)
        unsupported();
    if (opcode == 0xc0 || opcode == 0xd0 || opcode == 0xd2 || opcode == 0xfe) {
        const auto [target, field] = byteRegister(dst, rexPresent);
        const Value operand = mode == 3 ? Value(target) :
            Value(Memory{x64Address(reader, mode, rm, rex, opcode == 0xc0 ? 1 : 0)});
        if (opcode == 0xfe) {
            if (group > 1)
                unsupported();
            return {ByteBinary{group ? BinaryOp::Sub : BinaryOp::Add, operand, field, Immediate{1}, 0, true, true}};
        }
        if (group != 4 && group != 5 && group != 7)
            unsupported();
        const auto op = group == 4 ? ShiftOp::Left : group == 5 ? ShiftOp::LogicalRight : ShiftOp::ArithmeticRight;
        std::optional<unsigned> count;
        if (opcode == 0xc0)
            count = reader.read(1) & 31;
        else if (opcode == 0xd0)
            count = 1;
        return {ByteShift{op, operand, field, count}};
    }
    if (opcode == 0xff && group <= 1) {
        const Value target = mode == 3 ? Value(Register{dst}) : Value(Memory{x64Address(reader, mode, rm, rex)});
        return {MemoryBinary{group == 0 ? BinaryOp::Add : BinaryOp::Sub, size, target, Immediate{1}, true, true}};
    }
    if (opcode == 0xd3 && mode == 3 && (group <= 1 || group == 4 || group == 5 || group == 7)) {
        const auto operation = group == 0 ? ShiftOp::RotateLeft : group == 1 ? ShiftOp::RotateRight :
            group == 4 ? ShiftOp::Left : group == 5 ? ShiftOp::LogicalRight : ShiftOp::ArithmeticRight;
        return {ShiftRegister{operation, size, dst, Register{dst}, Register{1}, true}};
    }

    if (byteAlu || opcode == 0x84 || opcode == 0x88 || opcode == 0x8a) {
        const auto [reg, regField] = byteRegister(src, rexPresent);
        const auto [rmByte, rmField] = byteRegister(dst, rexPresent);
        const Value operand = mode == 3 ? Value(rmByte) : Value(Memory{x64Address(reader, mode, rm, rex)});
        if (opcode == 0x84)
            return {ByteBinary{BinaryOp::And, operand, rmField, reg, regField}};
        if (byteAlu) {
            const auto operation = opcode >> 3;
            const auto op = byteCarry ? (operation == 2 ? BinaryOp::Add : BinaryOp::Sub) : *x64Operations[operation];
            ByteBinary binary = opcode & 2 ? ByteBinary{op, reg, regField, operand, rmField, operation != 7}
                                           : ByteBinary{op, operand, rmField, reg, regField, operation != 7};
            binary.withCarry = byteCarry;
            return {binary};
        }
        if (opcode == 0x88)
            return {ByteMove{operand, rmField, reg, regField}};
        return {ByteMove{reg, regField, operand, rmField}};
    }
    if (opcode == 0x87) {
        const Value target = mode == 3 ? Value(Register{dst}) : Value(Memory{x64Address(reader, mode, rm, rex)});
        return {Exchange{size, target, Register{src}}};
    }
    if (opcode == 0xf6 && group == 2) {
        const auto [target, field] = byteRegister(dst, rexPresent);
        const Value operand = mode == 3 ? Value(target) : Value(Memory{x64Address(reader, mode, rm, rex)});
        return {ByteBinary{BinaryOp::Xor, operand, field, Immediate{255}, 0, true, false, false, false}};
    }
    if (opcode == 0xf6 && group == 3) {
        const auto [target, field] = byteRegister(dst, rexPresent);
        const Value operand = mode == 3 ? Value(target) : Value(Memory{x64Address(reader, mode, rm, rex)});
        return {ByteBinary{BinaryOp::Sub, operand, field, Immediate{0}, 0, true, false, true}};
    }
    if (opcode == 0xf6 && (group == 4 || group == 5)) {
        const auto [target, field] = byteRegister(dst, rexPresent);
        const Value operand = mode == 3 ? Value(target) : Value(Memory{x64Address(reader, mode, rm, rex)});
        return {Multiply{1, 0, Register{0}, operand, true, Zero, false,
            group == 4 ? MultiplyOperands::UnsignedByte : MultiplyOperands::SignedByte, mode == 3 ? field : 0}};
    }
    if (opcode == 0xf6 && group == 0) {
        const auto [target, field] = byteRegister(dst, rexPresent);
        const Value operand = mode == 3 ? Value(target) : Value(Memory{x64Address(reader, mode, rm, rex, 1)});
        return {ByteBinary{BinaryOp::And, operand, field, Immediate{reader.read(1)}, 0}};
    }
    if (opcode == 0xc6 && mode == 3 && group == 0) {
        const auto [target, field] = byteRegister(dst, rexPresent);
        return {ByteMove{target, field, Immediate{reader.read(1)}, 0}};
    }
    if (opcode == 0x69 || opcode == 0x6b) {
        const unsigned bytes = opcode == 0x6b ? 1 : 4;
        const Value lhs = mode == 3 ? Value(Register{dst})
                                    : Value(Memory{x64Address(reader, mode, rm, rex, bytes)});
        return {Multiply{size, src, lhs, immediate(signExtend(reader.read(bytes), 8 * bytes))}};
    }
    if (opcode == 0xf7 && (group == 6 || group == 7)) {
        const Value divisor = mode == 3 ? Value(Register{dst})
                                        : Value(Memory{x64Address(reader, mode, rm, rex)});
        return {Divide{size, divisor, group == 7}};
    }
    if (opcode == 0xf7 && (group == 4 || group == 5)) {
        const Value operand = mode == 3 ? Value(Register{dst})
            : Value(Memory{x64Address(reader, mode, rm, rex)});
        return {Multiply{size, 0, Register{0}, operand, true, Zero, false,
            group == 4 ? MultiplyOperands::UnsignedWide : MultiplyOperands::SignedWide}};
    }
    if (opcode == 0xf7 && group == 2) {
        const Immediate mask{UINT64_MAX};
        if (mode == 3)
            return {Binary{BinaryOp::Xor, size, dst, dst, mask, false}};
        return {MemoryBinary{BinaryOp::Xor, size, Memory{x64Address(reader, mode, rm, rex)}, mask, true, false, false}};
    }
    if (opcode == 0xf7 && group == 3 && mode == 3)
        return {Binary{BinaryOp::Sub, size, dst, Zero, Register{dst}, true}};
    if (opcode == 0xff && (group == 2 || group == 4)) {
        const Value value = mode == 3 ? Value(Register{dst}) : Value(Memory{x64Address(reader, mode, rm, rex)});
        if (group == 2)
            return {.end = Call{value, reader.pc}};
        return {.end = Jump{value}};
    }
    if (opcode == 0xff && group == 6) {
        const Value value = mode == 3 ? Value(Register{dst}) : Value(Memory{x64Address(reader, mode, rm, rex)});
        return {Push{value}};
    }
    if (opcode == 0xf7 && group == 3 && mode != 3) {
        const auto at = x64Address(reader, mode, rm, rex);
        return {Move{size, Temp, Memory{at}}, {}, {}, 0,
            {Binary{BinaryOp::Sub, size, Temp, Zero, Register{Temp}, true}, Store{size, at, Register{Temp}}}};
    }
    if ((opcode == 0xc1 || opcode == 0xd1 || opcode == 0xd3) && mode != 3 &&
        (group <= 1 || group == 4 || group == 5 || group == 7)) {
        // Shift memory through a temporary: load, shift, and store back.
        const auto at = x64Address(reader, mode, rm, rex, opcode == 0xc1 ? 1 : 0);
        const auto op = group == 0 ? ShiftOp::RotateLeft : group == 1 ? ShiftOp::RotateRight :
            group == 4 ? ShiftOp::Left : group == 5 ? ShiftOp::LogicalRight : ShiftOp::ArithmeticRight;
        if (opcode == 0xd3)
            return {Move{size, Temp, Memory{at}}, {}, {}, 0,
                {ShiftRegister{op, size, Temp, Register{Temp}, Register{1}, true}, Store{size, at, Register{Temp}}}};
        const auto count = opcode == 0xd1 ? 1u : unsigned(reader.read(1)) & (size == 8 ? 63u : 31u);
        if (count == 0)
            return {};
        return {Move{size, Temp, Memory{at}}, {}, {}, 0,
            {Shift{op, size, Register{Temp}, count}, Store{size, at, Register{Temp}}}};
    }
    if (opcode == 0x80 && (x64Operations[group] || group == 2 || group == 3)) {
        const auto [target, field] = byteRegister(dst, rexPresent);
        const Value operand = mode == 3 ? Value(target) : Value(Memory{x64Address(reader, mode, rm, rex, 1)});
        const auto op = x64Operations[group] ? *x64Operations[group] : group == 2 ? BinaryOp::Add : BinaryOp::Sub;
        ByteBinary binary{op, operand, field, Immediate{reader.read(1)}, 0, group != 7};
        binary.withCarry = !x64Operations[group];
        return {binary};
    }
    if (opcode == 0x89 || opcode == 0x8b || opcode == 0x8d) {
        if (mode != 3) {
            const auto at = x64Address(reader, mode, rm, rex);
            if (opcode == 0x8d) {
                Instruction move{Move{size, src, at}};
                if (size == 8 && mode == 0 && rm == 5 && reader.mapped)
                    move.addressTaken = at.displacement;
                return move;
            }
            if (opcode == 0x89)
                return {Store{size, at, Register{src}}};
            return {Move{size, src, Memory{at}}};
        }
        if (opcode == 0x89)
            return {Move{size, dst, Register{src}}};
        if (opcode == 0x8b)
            return {Move{size, src, Register{dst}}};
    }
    if (mode != 3 && group == 0 && (opcode == 0xc6 || opcode == 0xc7)) {
        const unsigned bytes = opcode == 0xc6 ? 1 : 4;
        const auto addr = x64Address(reader, mode, rm, rex, bytes);
        const auto value = immediate(signExtend(reader.read(bytes), 8 * bytes));
        return {Store{opcode == 0xc6 ? 1 : size, addr, value}};
    }
    if (mode != 3 && (opcode == 0x81 || opcode == 0x83) && (x64Operations[group] || group == 2 || group == 3)) {
        const unsigned bytes = opcode == 0x83 ? 1 : 4;
        const auto addr = x64Address(reader, mode, rm, rex, bytes);
        const auto rhs = immediate(signExtend(reader.read(bytes), 8 * bytes));
        if (!x64Operations[group])
            return {MemoryBinary{group == 2 ? BinaryOp::Add : BinaryOp::Sub, size, Memory{addr}, rhs, true, false, true, true}};
        return {MemoryBinary{*x64Operations[group], size, Memory{addr}, rhs, group != 7}};
    }
    if (opcode == 0xf7 && group == 0) {
        const Value target = mode == 3 ? Value(Register{dst})
            : Value(Memory{x64Address(reader, mode, rm, rex, 4)});
        const auto rhs = immediate(signExtend(reader.read(4), 32));
        return {MemoryBinary{BinaryOp::And, size, target, rhs, false}};
    }
    if (mode != 3 && carryAlu) {
        // ADC and SBB with a memory operand.
        const Memory memory{x64Address(reader, mode, rm, rex)};
        const auto op = opcode & 8 ? BinaryOp::Sub : BinaryOp::Add;
        if (opcode & 2)
            return {MemoryBinary{op, size, Register{src}, memory, true, false, true, true}};
        return {MemoryBinary{op, size, memory, Register{src}, true, false, true, true}};
    }
    if (mode != 3 && (registerAlu || opcode == 0x85)) {
        const Memory memory{x64Address(reader, mode, rm, rex)};
        const auto op = opcode >> 3;
        if (opcode == 0x85)
            return {MemoryBinary{BinaryOp::And, size, memory, Register{src}, false}};
        if (opcode & 2)
            return {MemoryBinary{*x64Operations[op], size, Register{src}, memory, op != 7}};
        return {MemoryBinary{*x64Operations[op], size, memory, Register{src}, op != 7}};
    }
    if (mode != 3)
        unsupported();

    if ((opcode == 0xc1 || opcode == 0xd1) && (group <= 1 || group == 4 || group == 5 || group == 7)) {
        const auto count = opcode == 0xd1 ? 1u : unsigned(reader.read(1)) & (size == 8 ? 63u : 31u);
        if (count == 0)
            return {};
        const auto op = group == 0 ? ShiftOp::RotateLeft : group == 1 ? ShiftOp::RotateRight :
            group == 4 ? ShiftOp::Left : group == 5 ? ShiftOp::LogicalRight : ShiftOp::ArithmeticRight;
        return {Shift{op, size, Register{dst}, count}};
    }

    if (opcode == 0x81 || opcode == 0x83 || (opcode == 0xc7 && group == 0)) {
        const unsigned bytes = opcode == 0x83 ? 1 : 4;
        const auto value = immediate(signExtend(reader.read(bytes), 8 * bytes));
        if (opcode == 0xc7)
            return {Move{size, dst, value}};
        if (x64Operations[group])
            return {Binary{*x64Operations[group], size, group == 7 ? Zero : dst, dst, value, true}};
        if ((opcode == 0x81 || opcode == 0x83) && (group == 2 || group == 3))
            return {Binary{group == 2 ? BinaryOp::Add : BinaryOp::Sub, size, dst, dst, value, true,
                ShiftOp::Left, 0, false, 0, false, true}};
    }
    if (opcode == 0x85)
        return {Binary{BinaryOp::And, size, Zero, dst, Register{src}, true}};
    if (registerAlu) {
        const auto op = opcode >> 3;
        const bool reverse = opcode & 2;
        const auto lhs = reverse ? src : dst;
        return {Binary{*x64Operations[op], size, op == 7 ? Zero : lhs, lhs, Register{reverse ? dst : src}, true}};
    }
    if (carryAlu) {
        const bool reverse = opcode & 2;
        const auto lhs = reverse ? src : dst;
        return {Binary{opcode & 8 ? BinaryOp::Sub : BinaryOp::Add, size, lhs, lhs,
            Register{reverse ? dst : src}, true, ShiftOp::Left, 0, false, 0, false, true}};
    }
    unsupported();
}
}
