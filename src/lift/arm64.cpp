#include "decode.h"

#include <array>
#include <bit>
#include <utility>

namespace ir::decode {
namespace {
unsigned armReg(unsigned index) {
    return index == 31 ? Zero : index;
}

Instruction transfer(Effect effect, unsigned base, Address writeback) {
    Instruction instruction{std::move(effect)};
    if (writeback)
        instruction.after = Binary{BinaryOp::Add, 8, base, base, immediate(writeback), false};
    return instruction;
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

    if (word == 0xd503201f)
        return {};
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
    if ((word & 0x3fe00800) == 0x1a800000) {
        const auto variant = ((word >> 29) & 2) | ((word >> 10) & 1);
        constexpr std::array actions{SelectElse::Copy, SelectElse::Increment, SelectElse::Invert, SelectElse::Negate};
        return {Select{size, armReg(rd), Register{armReg(rn)}, Register{armReg(rm)},
            (word >> 12) & 15, actions[variant]}};
    }
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
        return {FloatBinary{operations[(word >> 12) & 3], floatSize, floatSize, VectorRegister{rd}, VectorRegister{rm}}};
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
    const auto vectorAdd = word & 0xffe0fc00;
    if (vectorAdd == 0x4ea08400 || vectorAdd == 0x6ea08400)
        return {VectorBinary{vectorAdd == 0x4ea08400 ? VectorOp::AddDwords : VectorOp::SubDwords,
            VectorRegister{rd}, VectorRegister{rm}, VectorRegister{rn}}};
    if ((word & 0xbff89c00) == 0x0f000400) {
        const auto immediate = ((word >> 11) & 0xe0) | ((word >> 5) & 0x1f);
        const auto lane = immediate << (((word >> 13) & 3) * 8);
        const auto upper = word & 0x40000000 ? lane : 0;
        return {VectorImmediate{VectorRegister{rd}, {lane, lane, upper, upper}}};
    }
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
        if (width < 4 || (width == 16 && (word >> 30) != 0))
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
