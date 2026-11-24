#include "decode.h"

#include <array>
#include <bit>
#include <format>
#include <utility>

namespace ir::decode {
namespace {
unsigned armReg(unsigned index) {
    return index == 31 ? Zero : index;
}

Instruction transfer(Effect effect, unsigned base, Address writeback) {
    Instruction instruction{std::move(effect)};
    if (writeback)
        instruction.after = {Binary{BinaryOp::Add, 8, base, base, immediate(writeback), false}};
    return instruction;
}
}

namespace {
std::uint64_t expandFloatImmediate(unsigned imm8, unsigned size) {
    const std::uint64_t sign = imm8 >> 7;
    const std::uint64_t b6 = (imm8 >> 6) & 1;
    const std::uint64_t exponent = (imm8 >> 4) & 3;
    const std::uint64_t fraction = imm8 & 15;
    if (size == 4)
        return sign << 31 | (b6 ^ 1) << 30 | (b6 ? 0x1full : 0) << 25 | exponent << 23 | fraction << 19;
    return sign << 63 | (b6 ^ 1) << 62 | (b6 ? 0xffull : 0) << 54 | exponent << 52 | fraction << 48;
}

std::array<std::uint32_t, 4> splitLanes(std::uint64_t value, bool both) {
    const auto lo = std::uint32_t(value), hi = std::uint32_t(value >> 32);
    return {lo, hi, both ? lo : 0, both ? hi : 0};
}

// AdvSIMD and floating-point encodings beyond the forms decodeArm matches directly.
std::optional<Instruction> decodeArmSimd(std::uint32_t word) {
    const unsigned rd = word & 31;
    const unsigned rn = (word >> 5) & 31;
    const unsigned rm = (word >> 16) & 31;
    const bool q = word & 0x40000000;
    const bool u = word & 0x20000000;
    const unsigned width = q ? 16 : 8;
    const VectorRegister vd{rd}, vn{rn}, vm{rm}, temp{VectorTemp};
    const unsigned type = (word >> 22) & 3;
    const unsigned scalar = type == 1 ? 8 : 4;
    const auto withTemp = [](Effect first, std::vector<Effect> rest) {
        Instruction instruction{std::move(first)};
        instruction.after = std::move(rest);
        return instruction;
    };

    if ((word & 0xff201fe0) == 0x1e201000) {
        if (type > 1)
            unsupported();
        const auto bits = expandFloatImmediate((word >> 13) & 0xff, scalar);
        return Instruction{VectorImmediate{vd, splitLanes(bits, false)}};
    }
    if ((word & 0xff207c00) == 0x1e204000 && type <= 1) {
        switch ((word >> 15) & 0x3f) {
            case 0: return Instruction{VectorMove{vd, vn, scalar}};
            case 2: return Instruction{ScalarFloat{ScalarFloatOp::Negate, scalar, vd, vn}};
            case 8: case 14: case 15: return Instruction{ScalarFloat{ScalarFloatOp::RoundNearestEven, scalar, vd, vn}};
            case 9: return Instruction{ScalarFloat{ScalarFloatOp::Ceil, scalar, vd, vn}};
            case 10: return Instruction{ScalarFloat{ScalarFloatOp::Floor, scalar, vd, vn}};
            case 11: return Instruction{ScalarFloat{ScalarFloatOp::Truncate, scalar, vd, vn}};
            case 12: return Instruction{ScalarFloat{ScalarFloatOp::RoundAway, scalar, vd, vn}};
            default: return std::nullopt;
        }
    }
    if ((word & 0xff200c00) == 0x1e200800 && type <= 1) {
        constexpr std::array ops{ScalarFloatOp::ArmMax, ScalarFloatOp::ArmMin, ScalarFloatOp::MaxNumber,
            ScalarFloatOp::MinNumber, ScalarFloatOp::NegateMultiply};
        const auto opcode = (word >> 12) & 15;
        if (opcode >= 4 && opcode <= 8)
            return Instruction{ScalarFloat{ops[opcode - 4], scalar, vd, vm, vn}};
        return std::nullopt;
    }
    if ((word & 0xff000000) == 0x1f000000) {
        if (type > 1)
            unsupported();
        const bool o1 = word & 0x00200000;
        const bool o0 = word & 0x8000;
        return Instruction{FusedMultiply{scalar, vd, vn, vm, VectorRegister{(word >> 10) & 31}, o0 != o1, o1}};
    }
    if ((word & 0xff200c00) == 0x1e200c00 && type <= 1)
        return Instruction{FloatSelect{scalar, vd, vn, vm, (word >> 12) & 15}};
    if ((word & 0xff200c00) == 0x1e200400 && type <= 1)
        return Instruction{FloatConditionalCompare{scalar, vn, vm, (word >> 12) & 15, word & 15}};

    const unsigned integerSize = word >> 31 ? 8 : 4;
    const auto convert = word & 0x7fbffc00;
    if (convert == 0x1e200000 || convert == 0x1e210000 || convert == 0x1e240000 || convert == 0x1e250000)
        return Instruction{FloatToInteger{integerSize, rd == 31 ? Zero : rd, scalar, vn, !(convert & 0x10000),
            convert & 0x40000 ? Rounding::Away : Rounding::NearestEven}};
    const auto fixed = word & 0x7f3f0000;
    if ((fixed == 0x1e020000 || fixed == 0x1e030000 || fixed == 0x1e180000 || fixed == 0x1e190000) && type <= 1) {
        const auto fraction = 64 - ((word >> 10) & 63);
        if (fraction > integerSize * 8)
            unsupported();
        if (fixed <= 0x1e030000)
            return Instruction{IntegerToFloat{scalar, vd, integerSize, Register{rn == 31 ? Zero : rn}, fixed == 0x1e020000,
                fraction}};
        return Instruction{FloatToInteger{integerSize, rd == 31 ? Zero : rd, scalar, vn, fixed == 0x1e180000,
            Rounding::Truncate, fraction}};
    }
    if ((word & 0xdfbffc00) == 0x5e21d800) {
        const unsigned size = word & 0x00400000 ? 8 : 4;
        return withTemp(VectorTransfer{Register{Temp}, vn, false, size},
            {IntegerToFloat{size, vd, size, Register{Temp}, !u}});
    }
    if ((word & 0xdfbffc00) == 0x5ea1b800) {
        const unsigned size = word & 0x00400000 ? 8 : 4;
        return withTemp(FloatToInteger{size, Temp, size, vn, !u}, {VectorTransfer{Register{Temp}, vd, true, size}});
    }
    if ((word & 0xfffefc00) == 0x9eae0000) {
        // FMOV between a general register and the upper half of a vector register.
        const bool toVector = word & 0x10000;
        return Instruction{VectorTransfer{Register{toVector ? (rn == 31 ? Zero : rn) : (rd == 31 ? Zero : rd)},
            toVector ? vd : vn, toVector, 8, 1}};
    }

    if ((word & 0x9ff80400) == 0x0f000400) {
        const bool op = u;
        const auto cmode = (word >> 12) & 15;
        const std::uint64_t imm8 = ((word >> 11) & 0xe0) | ((word >> 5) & 0x1f);
        std::uint64_t value = 0;
        enum { MoveImmediate, OrImmediate, ClearImmediate } kind = MoveImmediate;
        bool invert = false;
        if (cmode < 8) {
            value = (imm8 << (8 * (cmode >> 1))) * 0x0000000100000001ull;
            kind = cmode & 1 ? (op ? ClearImmediate : OrImmediate) : MoveImmediate;
            invert = op && !(cmode & 1);
        } else if (cmode < 12) {
            value = (imm8 << (8 * ((cmode >> 1) & 1))) * 0x0001000100010001ull;
            kind = cmode & 1 ? (op ? ClearImmediate : OrImmediate) : MoveImmediate;
            invert = op && !(cmode & 1);
        } else if (cmode < 14) {
            const auto word32 = cmode == 12 ? (imm8 << 8) | 0xff : (imm8 << 16) | 0xffff;
            value = word32 * 0x0000000100000001ull;
            invert = op;
        } else if (cmode == 14) {
            if (!op) {
                value = imm8 * 0x0101010101010101ull;
            } else {
                for (unsigned bit = 0; bit < 8; ++bit)
                    if (imm8 & (1u << bit))
                        value |= 0xffull << (bit * 8);
            }
        } else {
            if (op && !q)
                unsupported();
            value = op ? expandFloatImmediate(unsigned(imm8), 8) :
                expandFloatImmediate(unsigned(imm8), 4) * 0x0000000100000001ull;
        }
        if (invert)
            value = ~value;
        const auto lanes = splitLanes(value, q);
        if (kind == MoveImmediate)
            return Instruction{VectorImmediate{vd, lanes}};
        if (kind == OrImmediate)
            return withTemp(VectorImmediate{temp, lanes}, {VectorBinary{VectorOp::Or, vd, temp, vd, width}});
        return withTemp(VectorImmediate{temp, lanes}, {VectorBinary{VectorOp::AndNot, vd, vd, temp, width}});
    }

    const auto elementOf = [](unsigned imm5) -> std::pair<unsigned, unsigned> {
        const auto shift = unsigned(std::countr_zero(imm5));
        if (shift > 3)
            unsupported();
        return {1u << shift, imm5 >> (shift + 1)};
    };
    if ((word & 0xbfe0fc00) == 0x0e000400 || (word & 0xffe0fc00) == 0x5e000400) {
        const bool scalarForm = (word & 0xffe0fc00) == 0x5e000400;
        const auto [element, index] = elementOf((word >> 16) & 31);
        std::array<std::uint8_t, 16> bytes;
        bytes.fill(255);
        const unsigned length = scalarForm ? element : width;
        for (unsigned i = 0; i < length; ++i)
            bytes[i] = std::uint8_t(index * element + i % element);
        return Instruction{VectorPermute{vd, vn, vn, bytes}};
    }
    if ((word & 0xffe08400) == 0x6e000400) {
        const auto imm5 = (word >> 16) & 31;
        const auto [element, dstIndex] = elementOf(imm5);
        const auto srcIndex = ((word >> 11) & 15) >> std::countr_zero(imm5);
        return Instruction{VectorLaneMove{element, vd, dstIndex, vn, srcIndex}};
    }
    if ((word & 0xbfe0fc00) == 0x0e003c00 || (word & 0xbfe0fc00) == 0x0e002c00) {
        const auto [element, index] = elementOf((word >> 16) & 31);
        const auto target = rd == 31 ? Zero : rd;
        if ((word & 0xbfe0fc00) == 0x0e003c00)
            return Instruction{VectorTransfer{Register{target}, vn, false, element, index}};
        return withTemp(VectorTransfer{Register{Temp}, vn, false, element, index},
            {Extend{q ? 8u : 4u, target, Register{Temp}, element * 8, 0, true}});
    }
    if ((word & 0xffe0fc00) == 0x4e001c00) {
        const auto [element, index] = elementOf((word >> 16) & 31);
        return Instruction{VectorTransfer{Register{rn == 31 ? Zero : rn}, vd, true, element, index}};
    }
    if ((word & 0xbfe08400) == 0x2e000000) {
        const auto start = (word >> 11) & 15;
        std::array<std::uint8_t, 16> bytes;
        bytes.fill(255);
        for (unsigned i = 0; i < width; ++i) {
            const auto index = start + i;
            bytes[i] = std::uint8_t(index < width ? index : 16 + index - width);
        }
        return Instruction{VectorPermute{vd, vn, vm, bytes}};
    }
    if ((word & 0xbf208c00) == 0x0e000800) {
        const auto opcode = (word >> 12) & 7;
        const unsigned element = 1u << ((word >> 22) & 3);
        const unsigned count = width / element;
        std::array<std::uint8_t, 16> bytes;
        bytes.fill(255);
        for (unsigned i = 0; i < count; ++i) {
            unsigned source = 0, lane = 0;
            switch (opcode) {
                case 1: case 5: source = i < count / 2 ? 0 : 1; lane = 2 * (i % (count / 2)) + (opcode == 5); break;
                case 2: case 6: source = i % 2; lane = (i & ~1u) + (opcode == 6); break;
                case 3: case 7: source = i % 2; lane = i / 2 + (opcode == 7 ? count / 2 : 0); break;
                default: unsupported();
            }
            for (unsigned b = 0; b < element; ++b)
                bytes[i * element + b] = std::uint8_t(source * 16 + lane * element + b);
        }
        return Instruction{VectorPermute{vd, vn, vm, bytes}};
    }

    if ((word & 0x9f3e0c00) == 0x0e200800) {
        const auto opcode = (word >> 12) & 0x1f;
        const unsigned size = (word >> 22) & 3;
        const unsigned element = 1u << size;
        const unsigned floatElement = size & 1 ? 8 : 4;
        const bool high = size & 2;
        if (opcode <= 1) {
            const unsigned container = opcode == 1 ? 2 : u ? 4 : 8;
            if (element >= container)
                unsupported();
            std::array<std::uint8_t, 16> bytes;
            bytes.fill(255);
            for (unsigned at = 0; at < width; at += element) {
                const auto base = at - at % container;
                const auto mirrored = base + container - element - (at - base);
                for (unsigned b = 0; b < element; ++b)
                    bytes[at + b] = std::uint8_t(mirrored + b);
            }
            return Instruction{VectorPermute{vd, vn, vn, bytes}};
        }
        if (opcode == 0x0f && high)
            return Instruction{VectorFloatLanes{u ? FloatLaneOp::Negate : FloatLaneOp::Absolute, floatElement, vd, vn,
                std::nullopt, width}};
        if (opcode == 0x1f && high && u)
            return Instruction{VectorFloatLanes{FloatLaneOp::Sqrt, floatElement, vd, vn, std::nullopt, width}};
        if (opcode == 0x17 && !u && !high && (size & 1))
            return Instruction{VectorConvert{LaneConversion::FloatToDouble, vd, vn, 4, q}};
        if (opcode == 0x16 && !u && !high && (size & 1))
            return Instruction{VectorConvert{LaneConversion::DoubleToFloat, vd, vn, 8, q}};
        if (opcode == 0x1d && !high)
            return Instruction{VectorConvert{u ? LaneConversion::UnsignedToFloat : LaneConversion::SignedToFloat, vd, vn,
                floatElement, false, 0, width}};
        if (opcode == 0x1b && high)
            return Instruction{VectorConvert{u ? LaneConversion::FloatToUnsigned : LaneConversion::FloatToSigned, vd, vn,
                floatElement, false, 0, width}};
        if (opcode == 0x12 && !u && size < 3)
            return Instruction{VectorConvert{LaneConversion::Narrow, vd, vn, element * 2, q}};
        if (opcode == 0x05 && u && size == 0) {
            return withTemp(VectorImmediate{temp, {~0u, ~0u, ~0u, ~0u}},
                {VectorBinary{VectorOp::Xor, vd, temp, vn, width}});
        }
        const auto zeroCompare = [&](LaneOp op, bool zeroFirst) {
            const auto other = zeroFirst ? vn : temp;
            return withTemp(VectorImmediate{temp, {0, 0, 0, 0}},
                {VectorLanes{op, element, vd, other, zeroFirst ? temp : vn, width}});
        };
        if (opcode == 0x09 && !u) return zeroCompare(LaneOp::Equal, false);
        if (opcode == 0x08) return zeroCompare(u ? LaneOp::GreaterEqualSigned : LaneOp::GreaterSigned, false);
        if (opcode == 0x09 && u) return zeroCompare(LaneOp::GreaterEqualSigned, true);
        if (opcode == 0x0a && !u) return zeroCompare(LaneOp::GreaterSigned, true);
        if (opcode == 0x0b && u) return zeroCompare(LaneOp::Sub, true);
        return std::nullopt;
    }
    if ((word & 0x9f3e0c00) == 0x0e300800) {
        const auto opcode = (word >> 12) & 0x1f;
        const unsigned element = 1u << ((word >> 22) & 3);
        std::optional<ReduceOp> op;
        if (opcode == 0x1b && !u) op = ReduceOp::Add;
        else if (opcode == 0x03 && u) op = ReduceOp::AddLong;
        else if (opcode == 0x0a) op = u ? ReduceOp::MaxUnsigned : ReduceOp::MaxSigned;
        else if (opcode == 0x1a) op = u ? ReduceOp::MinUnsigned : ReduceOp::MinSigned;
        if (op)
            return Instruction{VectorReduce{*op, element, vd, vn, width}};
        return std::nullopt;
    }
    if ((word & 0x9f200400) == 0x0e200400) {
        const auto opcode = (word >> 11) & 0x1f;
        const unsigned size = (word >> 22) & 3;
        const unsigned element = 1u << size;
        if (opcode >= 0x18) {
            const bool a = size & 2;
            const unsigned floatElement = size & 1 ? 8 : 4;
            std::optional<FloatLaneOp> op;
            if (opcode == 0x1a && !u) op = a ? FloatLaneOp::Sub : FloatLaneOp::Add;
            else if (opcode == 0x1b && u && !a) op = FloatLaneOp::Mul;
            else if (opcode == 0x1f && u && !a) op = FloatLaneOp::Div;
            else if (opcode == 0x1e && !u) op = a ? FloatLaneOp::ArmMin : FloatLaneOp::ArmMax;
            else if (opcode == 0x18 && !u) op = a ? FloatLaneOp::MinNumber : FloatLaneOp::MaxNumber;
            else if (opcode == 0x1c && !u && !a) op = FloatLaneOp::Equal;
            else if (opcode == 0x1c && u) op = a ? FloatLaneOp::Greater : FloatLaneOp::GreaterEqual;
            if (op)
                return Instruction{VectorFloatLanes{*op, floatElement, vd, vm, vn, width}};
            if (opcode == 0x19 && !u)
                return withTemp(VectorFloatLanes{FloatLaneOp::Mul, floatElement, temp, vm, vn, width},
                    {VectorFloatLanes{a ? FloatLaneOp::Sub : FloatLaneOp::Add, floatElement, vd, temp, vd, width}});
            return std::nullopt;
        }
        if (opcode == 0x03) {
            if (!u && size == 1)
                return Instruction{VectorBinary{VectorOp::AndNot, vd, vn, vm, width}};
            if (u && size == 1)
                return Instruction{VectorBlend{vd, vn, vm, vd}};
            if (u && size == 2)
                return Instruction{VectorBlend{vd, vn, vd, vm}};
            if (u && size == 3)
                return Instruction{VectorBlend{vd, vd, vn, vm}};
            return std::nullopt;
        }
        std::optional<LaneOp> op;
        switch (opcode) {
            case 0x10: op = u ? LaneOp::Sub : LaneOp::Add; break;
            case 0x06: op = u ? LaneOp::Higher : LaneOp::GreaterSigned; break;
            case 0x07: op = u ? LaneOp::HigherSame : LaneOp::GreaterEqualSigned; break;
            case 0x11: if (u) op = LaneOp::Equal; break;
            case 0x0c: op = u ? LaneOp::MaxUnsigned : LaneOp::MaxSigned; break;
            case 0x0d: op = u ? LaneOp::MinUnsigned : LaneOp::MinSigned; break;
            case 0x0e: if (u) op = LaneOp::AbsoluteDifference; break;
            case 0x13: if (!u) op = LaneOp::Mul; break;
            case 0x01: op = u ? LaneOp::AddSaturateUnsigned : LaneOp::AddSaturateSigned; break;
            case 0x05: op = u ? LaneOp::SubSaturateUnsigned : LaneOp::SubSaturateSigned; break;
            case 0x02: if (u) op = LaneOp::AverageUnsigned; break;
            case 0x12:
                return withTemp(VectorLanes{LaneOp::Mul, element, temp, vm, vn, width},
                    {VectorLanes{u ? LaneOp::Sub : LaneOp::Add, element, vd, temp, vd, width}});
        }
        if (op)
            return Instruction{VectorLanes{*op, element, vd, vm, vn, width}};
        return std::nullopt;
    }
    if ((word & 0x9f800400) == 0x0f000400 && ((word >> 19) & 15) != 0) {
        const auto immh = (word >> 19) & 15;
        const auto immediate = (word >> 16) & 0x7f;
        const unsigned element = immh >= 8 ? 8 : immh >= 4 ? 4 : immh >= 2 ? 2 : 1;
        const unsigned bits = element * 8;
        const auto opcode = (word >> 11) & 0x1f;
        const auto right = 2 * bits - immediate;
        const auto left = immediate - bits;
        if (opcode == 0x00)
            return Instruction{VectorShiftLanes{u ? ShiftOp::LogicalRight : ShiftOp::ArithmeticRight, element, vd, vn,
                right, std::nullopt, width}};
        if (opcode == 0x02)
            return withTemp(VectorShiftLanes{u ? ShiftOp::LogicalRight : ShiftOp::ArithmeticRight, element, temp, vn,
                right, std::nullopt, width}, {VectorLanes{LaneOp::Add, element, vd, temp, vd, width}});
        if (opcode == 0x0a && !u)
            return Instruction{VectorShiftLanes{ShiftOp::Left, element, vd, vn, left, std::nullopt, width}};
        if (opcode == 0x14 && element < 8)
            return Instruction{VectorConvert{u ? LaneConversion::WidenUnsigned : LaneConversion::WidenSigned, vd, vn,
                element, q, left}};
        if (opcode == 0x10 && !u && element < 8)
            return withTemp(VectorShiftLanes{ShiftOp::LogicalRight, element * 2, temp, vn, right, std::nullopt, 16},
                {VectorConvert{LaneConversion::Narrow, vd, temp, element * 2, q}});
        return std::nullopt;
    }
    if ((word & 0xbf9f0000) == 0x0d000000 || (word & 0xbf800000) == 0x0d800000) {
        // LD1 (single structure) and LD1R, with optional post-index.
        const bool load = word & 0x00400000;
        const bool replicate = (word >> 13 & 7) == 6;
        if (!load || (word & 0x00200000))
            return std::nullopt;
        const auto opcode = (word >> 13) & 7;
        const auto size = (word >> 10) & 3;
        const bool s = word & 0x1000;
        unsigned element = 0, lane = 0;
        if (replicate) {
            element = 1u << size;
        } else if (opcode == 0) {
            element = 1; lane = (q << 3) | (s << 2) | size;
        } else if (opcode == 2) {
            element = 2; lane = (q << 2) | (s << 1) | (size >> 1);
        } else if (opcode == 4 && size == 0) {
            element = 4; lane = (q << 1) | s;
        } else if (opcode == 4 && size == 1 && !s) {
            element = 8; lane = q;
        } else {
            unsupported();
        }
        Instruction instruction{VectorLaneLoad{element, vd, lane, {rn, 0}, replicate, width}};
        if (word & 0x00800000) {
            if (rm == 31)
                instruction.after.push_back(Binary{BinaryOp::Add, 8, rn, rn, immediate(element), false});
            else
                instruction.after.push_back(Binary{BinaryOp::Add, 8, rn, rn, Register{rm}, false});
        }
        return instruction;
    }
    if ((word & 0xbfbf0000) == 0x0c000000 || (word & 0xbfa00000) == 0x0c800000) {
        // LD1/ST1 (multiple structures) with one to four consecutive registers.
        const bool load = word & 0x00400000;
        const auto opcode = (word >> 12) & 15;
        const unsigned count = opcode == 7 ? 1 : opcode == 10 ? 2 : opcode == 6 ? 3 : opcode == 2 ? 4 : 0;
        if (!count)
            return std::nullopt;
        Instruction instruction;
        for (unsigned i = 0; i < count; ++i) {
            const VectorRegister reg{(rd + i) % 32};
            const VectorMemory memory{{rn, Address(i * width)}, false};
            Effect effect = load ? Effect(VectorMove{reg, memory, width}) : Effect(VectorMove{memory, reg, width});
            if (i == 0)
                instruction.effect = effect;
            else
                instruction.after.push_back(effect);
        }
        if (word & 0x00800000) {
            if (rm == 31)
                instruction.after.push_back(Binary{BinaryOp::Add, 8, rn, rn, immediate(count * width), false});
            else
                instruction.after.push_back(Binary{BinaryOp::Add, 8, rn, rn, Register{rm}, false});
        }
        return instruction;
    }
    return std::nullopt;
}
}

Instruction decodeArm(Reader& reader) {
    const auto pc = reader.pc;
    if (pc % 4 != 0)
        throw std::runtime_error("unaligned ARM64 instruction");
    const auto word = std::uint32_t(reader.read(4));
    const unsigned size = word >> 31 ? 8 : 4;
    const unsigned rd = word & 31;
    const unsigned rn = (word >> 5) & 31;
    const unsigned rm = (word >> 16) & 31;
    const unsigned operation = (word >> 29) & 3;
    const bool setFlags = operation & 1;
    const auto arithmetic = operation & 2 ? BinaryOp::Sub : BinaryOp::Add;
    const auto next = reader.pc;

    if ((word & 0xfffff01f) == 0xd503201f || (word & 0xfffff09f) == 0xd503309f)
        return {}; // Hints (NOP, BTI, PAC) and barriers have no single-threaded effect.
    if ((word & 0xffe0001f) == 0xd4200000 || (word & 0xffe0001f) == 0xd4400000 || (word >> 16) == 0)
        return {.end = Trap{std::format("guest trap instruction at guest offset {}", pc)}};
    if ((word & 0xfffffc1f) == 0xd65f0000)
        return {.end = Return{Register{armReg(rn)}}};
    if ((word & 0xfffffc1f) == 0xd61f0000)
        return {.end = Jump{Register{armReg(rn)}}};
    if ((word & 0xfffffc1f) == 0xd63f0000)
        return {.end = Call{Register{armReg(rn)}, next}};
    if ((word & 0x7c000000) == 0x14000000) {
        const auto target = immediate(pc + 4 * signExtend(word & 0x03ffffff, 26));
        if (word >> 31)
            return {.end = Call{target, next}};
        return {.end = Jump{target}};
    }
    const auto branchTarget = pc + 4 * signExtend((word >> 5) & 0x7ffff, 19);
    if ((word & 0xff000010) == 0x54000000)
        return {.end = Branch{FlagsCondition{rd & 15}, branchTarget, next}};
    if ((word & 0x7e000000) == 0x34000000)
        return {.end = Branch{ZeroCondition{armReg(rd), size, bool(word & 0x01000000)}, branchTarget, next}};
    if ((word & 0x7e000000) == 0x36000000) {
        const auto bit = ((word >> 26) & 32) | ((word >> 19) & 31);
        const auto target = pc + 4 * signExtend((word >> 5) & 0x3fff, 14);
        return {.end = Branch{TestBitCondition{armReg(rd), bit, bool(word & 0x01000000)}, target, next}};
    }

    if ((word & 0x1f800000) == 0x12800000) {
        const unsigned shift = ((word >> 21) & 3) * 16;
        const auto value = (word >> 5) & 0xffff;
        if (operation == 1 || shift >= size * 8)
            unsupported();
        if (operation == 3)
            return {KeepBits{size, armReg(rd), shift, value}};
        const auto shifted = std::uint64_t(value) << shift;
        return {Move{size, armReg(rd), Immediate{operation == 0 ? ~shifted : shifted}}};
    }
    if ((word & 0x1f800000) == 0x13000000 && operation != 3) {
        const auto start = (word >> 16) & 63;
        const auto last = (word >> 10) & 63;
        const unsigned width = size * 8;
        if (start >= width || last >= width || bool(word & 0x00400000) != (size == 8))
            unsupported();
        const bool wrap = last < start;
        return {Bitfield{size, armReg(rd), Register{armReg(rn)}, wrap ? 0 : start,
            wrap ? last + 1 : last - start + 1, wrap ? width - start : 0, operation == 0, operation == 1}};
    }
    if ((word & 0x7fa00000) == 0x13800000) {
        const auto count = (word >> 10) & 63;
        if (count >= size * 8 || bool(word & 0x00400000) != (size == 8))
            unsupported();
        return {Extract{size, armReg(rd), Register{armReg(rn)}, Register{armReg(rm)}, count}};
    }
    if ((word & 0x3fe00800) == 0x1a800000) {
        const auto variant = ((word >> 29) & 2) | ((word >> 10) & 1);
        constexpr std::array actions{SelectElse::Copy, SelectElse::Increment, SelectElse::Invert, SelectElse::Negate};
        return {Select{size, armReg(rd), Register{armReg(rn)}, Register{armReg(rm)},
            (word >> 12) & 15, actions[variant]}};
    }
    if ((word & 0x1fe0fc00) == 0x1a000000)
        return {Binary{arithmetic, size, armReg(rd), armReg(rn), Register{armReg(rm)}, setFlags,
            ShiftOp::Left, 0, false, 0, false, true}};
    if ((word & 0x3fe00410) == 0x3a400000) {
        const Value rhs = word & 0x800 ? Value(Immediate{rm}) : Value(Register{armReg(rm)});
        return {ConditionalCompare{size, Register{armReg(rn)}, rhs, (word >> 12) & 15, word & 15,
            bool(word & 0x40000000)}};
    }
    if ((word & 0x1f800000) == 0x11000000) {
        const auto operand = ((word >> 10) & 0xfff) << (word & 0x00400000 ? 12 : 0);
        return {Binary{arithmetic, size, setFlags ? armReg(rd) : rd, rn, Immediate{operand}, setFlags}};
    }
    if ((word & 0x1f800000) == 0x12000000) {
        const auto imms = (word >> 10) & 63;
        const auto pattern = ((word >> 16) & 64) | ((~imms) & 63);
        if (pattern < 2)
            unsupported();
        const auto element = 1u << (std::bit_width(pattern) - 1);
        const auto width = (imms & (element - 1)) + 1;
        const auto rotation = (word >> 16) & (element - 1);
        if (element > size * 8 || width == element)
            unsupported();
        auto mask = (std::uint64_t(1) << width) - 1;
        const auto laneMask = element == 64 ? UINT64_MAX : (std::uint64_t(1) << element) - 1;
        if (rotation)
            mask = ((mask >> rotation) | (mask << (element - rotation))) & laneMask;
        std::uint64_t repeated = 0;
        for (unsigned bit = 0; bit < size * 8; bit += element)
            repeated |= mask << bit;
        constexpr std::array ops{BinaryOp::And, BinaryOp::Or, BinaryOp::Xor, BinaryOp::And};
        return {Binary{ops[operation], size, operation == 3 ? armReg(rd) : rd, armReg(rn),
            Immediate{repeated}, operation == 3}};
    }
    if ((word & 0x1fe00000) == 0x0b200000) {
        const auto option = (word >> 13) & 7;
        const auto count = (word >> 10) & 7;
        if (count > 4)
            unsupported();
        const unsigned width = 8u << (option & 3);
        return {Binary{arithmetic, size, setFlags ? armReg(rd) : rd, rn, Register{armReg(rm)}, setFlags,
            ShiftOp::Left, count, false, width > size * 8 ? size * 8 : width, bool(option & 4)}};
    }
    if ((word & 0x1f200000) == 0x0b000000) {
        const auto shift = ShiftOp((word >> 22) & 3);
        const auto count = (word >> 10) & 63;
        if (shift == ShiftOp::RotateRight || count >= size * 8)
            unsupported();
        return {Binary{arithmetic, size, armReg(rd), armReg(rn), Register{armReg(rm)}, setFlags, shift, count}};
    }
    if ((word & 0x1f000000) == 0x0a000000) {
        constexpr std::array ops{BinaryOp::And, BinaryOp::Or, BinaryOp::Xor, BinaryOp::And};
        const auto shift = ShiftOp((word >> 22) & 3);
        const auto count = (word >> 10) & 63;
        if (count >= size * 8)
            unsupported();
        return {Binary{ops[operation], size, armReg(rd), armReg(rn), Register{armReg(rm)},
            operation == 3, shift, count, bool(word & 0x00200000)}};
    }
    if ((word & 0x7fe00000) == 0x1b000000)
        return {Multiply{size, armReg(rd), Register{armReg(rn)}, Register{armReg(rm)}, false,
            armReg((word >> 10) & 31), bool(word & 0x8000)}};
    const auto longMultiply = word & 0xffe00000;
    if (longMultiply == 0x9b200000 || longMultiply == 0x9ba00000)
        return {Multiply{8, armReg(rd), Register{armReg(rn)}, Register{armReg(rm)}, false,
            armReg((word >> 10) & 31), bool(word & 0x8000),
            longMultiply == 0x9b200000 ? MultiplyOperands::Signed32 : MultiplyOperands::Unsigned32}};
    const auto highMultiply = word & 0xffe0fc00;
    if (highMultiply == 0x9b407c00 || highMultiply == 0x9bc07c00)
        return {Multiply{8, armReg(rd), Register{armReg(rn)}, Register{armReg(rm)}, false, Zero, false,
            highMultiply == 0x9b407c00 ? MultiplyOperands::SignedHigh : MultiplyOperands::UnsignedHigh}};
    if ((word & 0x7fe0f800) == 0x1ac00800)
        return {DivideWord{size, armReg(rd), Register{armReg(rn)}, Register{armReg(rm)}, bool(word & 0x400)}};
    if ((word & 0x7fe0f000) == 0x1ac02000)
        return {ShiftRegister{ShiftOp((word >> 10) & 3), size, armReg(rd), Register{armReg(rn)}, Register{armReg(rm)}}};
    if ((word & 0x7ffffc00) == 0x5ac01000)
        return {BitScan{size, armReg(rd), Register{armReg(rn)}, true, true}};
    if ((word & 0xfffffc00) == 0x5ac00800 || (word & 0xfffffc00) == 0xdac00c00)
        return {ByteSwap{size, armReg(rd), Register{armReg(rn)}}};
    if ((word & 0x7ffffc00) == 0x5ac00000)
        return {ByteSwap{size, armReg(rd), Register{armReg(rn)}, true}};
    if ((word & 0xbf20fc00) == 0xb8200000)
        return {AtomicAdd{size, {rn, 0}, Register{armReg(rm)}, armReg(rd)}};
    const auto ordered = word & 0x3ffffc00;
    const auto unscaledOrder = word & 0x3fe00c00;
    if (ordered == 0x38bfc000 || ordered == 0x08dffc00 || ordered == 0x089ffc00 ||
        unscaledOrder == 0x19400000 || unscaledOrder == 0x19000000) {
        const unsigned width = 1u << (word >> 30);
        const auto offset = unscaledOrder == 0x19400000 || unscaledOrder == 0x19000000 ?
            signExtend((word >> 12) & 0x1ff, 9) : 0;
        const EffectiveAddress address{rn, offset};
        if (ordered == 0x089ffc00 || unscaledOrder == 0x19000000)
            return {Store{width, address, Register{armReg(rd)}}};
        if (width < 4)
            return {Extend{4, armReg(rd), Memory{address}, width * 8, 0, false}};
        return {Move{width, armReg(rd), Memory{address}}};
    }
    const unsigned floatSize = word & 0x00400000 ? 8 : 4;
    const auto convert = word & 0x7fbffc00;
    if (convert == 0x1e220000 || convert == 0x1e230000)
        return {IntegerToFloat{floatSize, VectorRegister{rd}, size, Register{armReg(rn)}, convert == 0x1e220000}};
    if (convert == 0x1e380000 || convert == 0x1e390000)
        return {FloatToInteger{size, armReg(rd), floatSize, VectorRegister{rn}, convert == 0x1e380000}};
    if (convert == 0x1e280000 || convert == 0x1e290000 || convert == 0x1e300000 || convert == 0x1e310000)
        return {FloatToInteger{size, armReg(rd), floatSize, VectorRegister{rn},
            !(convert & 0x10000), convert & 0x100000 ? Rounding::Down : Rounding::Up}};
    if (convert == 0x1e260000 || convert == 0x1e270000) {
        if (size != floatSize)
            unsupported();
        const bool toFloat = convert == 0x1e270000;
        return {VectorTransfer{Register{armReg(toFloat ? rn : rd)}, VectorRegister{toFloat ? rd : rn}, toFloat, size}};
    }
    const auto floatBinary = word & 0xffa0fc00;
    if (floatBinary == 0x1e200800 || floatBinary == 0x1e201800 ||
        floatBinary == 0x1e202800 || floatBinary == 0x1e203800) {
        constexpr std::array operations{FloatOp::Mul, FloatOp::Div, FloatOp::Add, FloatOp::Sub};
        return {FloatBinary{operations[(word >> 12) & 3], floatSize, floatSize, VectorRegister{rd}, VectorRegister{rm},
            VectorRegister{rn}}};
    }
    if ((word & 0xffa0fc07) == 0x1e202000) {
        const auto rhs = word & 8 ? std::optional<VectorOperand>{} : VectorOperand(VectorRegister{rm});
        return {FloatCompare{floatSize, VectorRegister{rn}, rhs}};
    }
    const auto floatUnary = word & 0xffbffc00;
    if (floatUnary == 0x1e24c000 || floatUnary == 0x1e254000 || floatUnary == 0x1e21c000 || floatUnary == 0x1e20c000) {
        const auto op = floatUnary == 0x1e24c000 ? FloatOp::Ceil :
            floatUnary == 0x1e254000 ? FloatOp::Floor : floatUnary == 0x1e20c000 ? FloatOp::Abs : FloatOp::Sqrt;
        return {FloatBinary{op, floatSize, floatSize, VectorRegister{rd}, VectorRegister{rn}}};
    }
    if ((word & 0xfffffc00) == 0x1e624000 || (word & 0xfffffc00) == 0x1e22c000)
        return {FloatBinary{FloatOp::Convert, 12 - floatSize, floatSize, VectorRegister{rd}, VectorRegister{rn}}};
    if ((word & 0x9f000000) == 0x10000000) {
        const auto offset = signExtend(((word >> 5) & 0x7ffff) * 4 + ((word >> 29) & 3), 21);
        if (!reader.mapped)
            return {Move{8, armReg(rd), immediate(pc + offset)}};
        return {Move{8, armReg(rd), EffectiveAddress{Zero, pc + offset}}, {}, pc + offset};
    }
    if ((word & 0x9f000000) == 0x90000000) {
        const auto pages = signExtend(((word >> 5) & 0x7ffff) * 4 + ((word >> 29) & 3), 21);
        const auto page = (pc & ~Address(4095)) + pages * 4096;
        Instruction address{Move{8, armReg(rd), immediate(page)}};
        if (reader.mapped && rd != 31 && next + 4 <= Address(reader.image.size())) {
            auto lookahead = reader;
            const auto add = lookahead.read(4);
            if ((add & 0xffc00000) == 0x91000000 && ((add >> 5) & 31) == rd)
                address.addressTaken = page + ((add >> 10) & 0xfff);
        }
        return address;
    }
    if ((word & 0xfff8fc00) == 0x6f00e400) {
        const auto mask = ((word >> 11) & 0xe0) | ((word >> 5) & 0x1f);
        std::array<std::uint32_t, 4> lanes{};
        for (unsigned i = 0; i < 8; ++i)
            if (mask & (1u << i))
                lanes[i / 4] |= 0xffu << ((i % 4) * 8);
        lanes[2] = lanes[0];
        lanes[3] = lanes[1];
        return {VectorImmediate{VectorRegister{rd}, lanes}};
    }
    if ((word & 0xbff8fc00) == 0x0f00e400) {
        const auto byte = ((word >> 11) & 0xe0) | ((word >> 5) & 0x1f);
        const std::uint32_t lane = byte * 0x01010101u;
        const auto upper = word & 0x40000000 ? lane : 0;
        return {VectorImmediate{VectorRegister{rd}, {lane, lane, upper, upper}}};
    }
    const auto byteOp = word & 0xbffffc00;
    if (byteOp == 0x0e205800 || byteOp == 0x2e303800)
        return {VectorByteOperation{VectorRegister{rd}, VectorRegister{rn}, word & 0x40000000 ? 16u : 8u,
            byteOp == 0x2e303800}};
    const auto vectorLogic = word & 0xbfe0fc00;
    if (vectorLogic == 0x2e809400)
        return {VectorBinary{VectorOp::DotUnsignedBytes, VectorRegister{rd}, VectorRegister{rm},
            VectorRegister{rn}, word & 0x40000000 ? 16u : 8u}};
    if (vectorLogic == 0x2e603c00 || vectorLogic == 0x2ea03c00)
        return {VectorBinary{vectorLogic == 0x2e603c00 ? VectorOp::CompareUnsignedWords : VectorOp::CompareUnsignedDwords,
            VectorRegister{rd}, VectorRegister{rm}, VectorRegister{rn}, word & 0x40000000 ? 16u : 8u}};
    if ((word & 0xbf80fc00) == 0x2f00a400) {
        const auto amount = (word >> 16) & 127;
        const auto bits = std::bit_floor(amount);
        if (bits == 16 || bits == 32)
            return {VectorWiden{VectorRegister{rd}, VectorRegister{rn}, bits, amount - bits, bool(word & 0x40000000)}};
    }
    if (vectorLogic == 0x0e201c00 || vectorLogic == 0x0ea01c00 || vectorLogic == 0x2e201c00) {
        const auto op = vectorLogic == 0x0e201c00 ? VectorOp::And :
            vectorLogic == 0x0ea01c00 ? VectorOp::Or : VectorOp::Xor;
        const auto width = word & 0x40000000 ? 16u : 8u;
        if (vectorLogic == 0x0ea01c00 && rn == rm)
            return {VectorMove{VectorRegister{rd}, VectorRegister{rn}, width}};
        return {VectorBinary{op, VectorRegister{rd}, VectorRegister{rm}, VectorRegister{rn}, width}};
    }
    const auto vectorAdd = word & 0xffe0fc00;
    if (vectorAdd == 0x4ea08400 || vectorAdd == 0x6ea08400)
        return {VectorBinary{vectorAdd == 0x4ea08400 ? VectorOp::AddDwords : VectorOp::SubDwords,
            VectorRegister{rd}, VectorRegister{rm}, VectorRegister{rn}}};
    if (vectorAdd == 0x4ee08400 || vectorAdd == 0x6ee08400)
        return {VectorBinary{vectorAdd == 0x4ee08400 ? VectorOp::AddQwords : VectorOp::SubQwords,
            VectorRegister{rd}, VectorRegister{rm}, VectorRegister{rn}}};
    const auto vectorUnary = word & 0xfffffc00;
    if (vectorUnary == 0x6ea06800)
        return {VectorBinary{VectorOp::AccumulatePairs, VectorRegister{rd}, VectorRegister{rn}}};
    if (vectorUnary == 0x5ef1b800)
        return {VectorBinary{VectorOp::SumQwords, VectorRegister{rd}, VectorRegister{rn}}};
    if (vectorUnary == 0x4ea09800 || vectorUnary == 0x4ee09800)
        return {VectorBinary{vectorUnary == 0x4ea09800 ? VectorOp::CompareZeroDwords : VectorOp::CompareZeroQwords,
            VectorRegister{rd}, VectorRegister{rn}}};
    if ((word & 0xbfe0fc00) == 0x0e000c00) {
        const auto imm = (word >> 16) & 31;
        const auto element = std::countr_zero(imm);
        if (element < 4 && imm == (1u << element) && (element != 3 || (word & 0x40000000)))
            return {VectorSplat{VectorRegister{rd}, Register{armReg(rn)}, 1u << element, word & 0x40000000 ? 16u : 8u}};
    }
    if ((word & 0xffe0fc00) == 0x4e001c00) {
        const auto imm = (word >> 16) & 31;
        const auto element = std::countr_zero(imm);
        if (element == 2 || element == 3)
            return {VectorTransfer{Register{armReg(rn)}, VectorRegister{rd}, true,
                1u << element, imm >> (element + 1)}};
    }
    const auto ld4 = word & 0xfffff000;
    if ((ld4 == 0x4c400000 || ld4 == 0x4cdf0000) && ((word >> 10) & 3) >= 2)
        return transfer(InterleavedLoad4{VectorRegister{rd}, {rn, 0}, 1u << ((word >> 10) & 3)}, rn,
            ld4 == 0x4cdf0000 ? 64 : 0);
    if ((word & 0xbff89c00) == 0x0f000400) {
        const auto immediate = ((word >> 11) & 0xe0) | ((word >> 5) & 0x1f);
        const auto lane = immediate << (((word >> 13) & 3) * 8);
        const auto upper = word & 0x40000000 ? lane : 0;
        return {VectorImmediate{VectorRegister{rd}, {lane, lane, upper, upper}}};
    }
    if (auto simd = decodeArmSimd(word))
        return std::move(*simd);
    const auto pairOpcode = word & 0x3e000000;
    if (pairOpcode == 0x28000000 || pairOpcode == 0x2c000000) {
        const bool vector = pairOpcode == 0x2c000000;
        const auto mode = (word >> 23) & 3;
        const bool load = word & 0x00400000;
        const bool sign = !vector && load && (word >> 30) == 1 && mode != 0;
        const unsigned encoding = word >> 30;
        const unsigned width = vector ? 4u << encoding : sign ? 4 : size;
        const auto second = (word >> 10) & 31;
        const bool update = mode == 1 || mode == 3;
        if ((!vector && (encoding & 1) && !sign) || (vector && encoding == 3) ||
            (load && rd == second && (vector || rd != 31)) ||
            (!vector && update && rn != 31 && (rn == rd || rn == second)))
            unsupported();
        const auto offset = signExtend((word >> 15) & 127, 7) * width;
        return {PairTransfer{width, vector ? rd : armReg(rd), vector ? second : armReg(second),
            {rn, mode == 1 ? 0 : offset}, update ? offset : 0, load, vector, sign}};
    }

    const bool vectorScaled = (word & 0x3f000000) == 0x3d000000;
    const bool vectorIndexed = (word & 0x3f200c00) == 0x3c200800;
    if (vectorScaled || vectorIndexed || (word & 0x3f200000) == 0x3c000000) {
        const unsigned width = word & 0x00800000 ? 16 : 1u << (word >> 30);
        if (width == 16 && (word >> 30) != 0)
            unsupported();
        const auto offset = vectorScaled ? Address(((word >> 10) & 0xfff) * width)
                                        : signExtend((word >> 12) & 0x1ff, 9);
        const auto mode = vectorScaled || vectorIndexed ? 0 : (word >> 10) & 3;
        if (mode == 2)
            unsupported();
        const auto update = mode ? offset : 0;
        const auto option = (word >> 13) & 7;
        if (vectorIndexed && !(option & 2))
            unsupported();
        const auto indexWidth = option & 1 ? IndexWidth::Full : option & 4 ? IndexWidth::Signed32 : IndexWidth::Unsigned32;
        const auto at = vectorIndexed ? EffectiveAddress{rn, 0, armReg(rm), word & 0x1000 ? width : 1, indexWidth}
                                      : EffectiveAddress{rn, mode == 1 ? 0 : offset};
        const VectorMemory mem{at, false};
        if (word & 0x00400000)
            return transfer(VectorMove{VectorRegister{rd}, mem, width}, rn, update);
        return transfer(VectorMove{mem, VectorRegister{rd}, width}, rn, update);
    }

    const bool immediateOffset = (word & 0x3f000000) == 0x39000000;
    const bool registerOffset = (word & 0x3f200c00) == 0x38200800;
    if (immediateOffset || registerOffset || (word & 0x3f200000) == 0x38000000) {
        const unsigned width = 1u << (word >> 30);
        const auto offset = immediateOffset ? Address(((word >> 10) & 0xfff) * width)
                                            : signExtend((word >> 12) & 0x1ff, 9);
        const auto mode = immediateOffset || registerOffset ? 0 : (word >> 10) & 3;
        if (mode == 2 || (mode != 0 && rn == rd && rn != 31))
            unsupported();
        const auto update = mode ? offset : 0;
        const auto option = (word >> 13) & 7;
        if (registerOffset && !(option & 2))
            unsupported();
        const auto indexWidth = option & 1 ? IndexWidth::Full : option & 4 ? IndexWidth::Signed32 : IndexWidth::Unsigned32;
        const auto at = registerOffset ? EffectiveAddress{rn, 0, armReg(rm), word & 0x1000 ? width : 1, indexWidth}
                                       : EffectiveAddress{rn, mode == 1 ? 0 : offset};
        const auto kind = (word >> 22) & 3;
        if (kind == 0)
            return transfer(Store{width, at, Register{armReg(rd)}}, rn, update);
        if (kind >= 2) {
            if (width == 8 || (width == 4 && kind == 3))
                unsupported();
            return transfer(Extend{kind == 2 ? 8u : 4u, armReg(rd), Memory{at}, width * 8, 0, true}, rn, update);
        }
        if (width < 4)
            return transfer(Extend{4, armReg(rd), Memory{at}, width * 8, 0, false}, rn, update);
        return transfer(Move{width, armReg(rd), Memory{at}}, rn, update);
    }
    unsupported();
}
}
