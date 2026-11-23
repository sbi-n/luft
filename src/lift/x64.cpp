#include "decode.h"

#include <array>
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
    if (prefix == 0x66 && opcode == 0x73 && mode == 3) {
        const auto group = (modrm >> 3) & 7;
        if (group == 3 || group == 7)
            return {VectorShiftBytes{VectorRegister{rmReg}, unsigned(reader.read(1)), group == 7}};
        unsupported();
    }
    if (prefix == 0xf3 && opcode == 0xe6)
        return {VectorIntToDouble{reg, operandAt(false)}};
    if (prefix == 0x66 && opcode == 0x70) {
        const auto operand = operandAt(false, 1);
        return {VectorShuffleDwords{reg, operand, unsigned(reader.read(1))}};
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
    const bool binary = logical ||
        (prefix == 0x66 && (opcode == 0xef || opcode == 0x62 || opcode == 0x6c || opcode == 0xfe || opcode == 0xfa));
    if (!alignedMoves && !unalignedMoves && !binary)
        unsupported();
    const VectorOperand operand = mode == 3 ? VectorOperand(VectorRegister{rmReg})
        : VectorOperand(VectorMemory{x64Address(reader, mode, rm, rex), !unalignedMoves});
    if (binary) {
        const auto kind = opcode == 0xfe ? VectorOp::AddDwords : opcode == 0xfa ? VectorOp::SubDwords :
            opcode == 0x62 ? VectorOp::UnpackLowDwords :
            opcode == 0x6c ? VectorOp::UnpackLowQwords : opcode == 0x54 ? VectorOp::And :
            opcode == 0x55 ? VectorOp::AndNot : opcode == 0x56 ? VectorOp::Or : VectorOp::Xor;
        return {VectorBinary{kind, reg, operand}};
    }
    if (opcode == 0x29 || opcode == 0x11 || opcode == 0x7f)
        return {VectorMove{operand, reg}};
    return {VectorMove{reg, operand}};
}

Instruction decodeX64Prefix(Reader& reader, unsigned prefix) {
    auto opcode = reader.read(1);
    unsigned rex = 0;
    if (opcode >= 0x40 && opcode <= 0x4f) {
        rex = opcode & 15;
        opcode = reader.read(1);
    }
    if (prefix == 0xf3 && (opcode == 0xaa || opcode == 0xab))
        return {RepeatStore{opcode == 0xaa ? 1u : (rex & 8) ? 8u : 4u}};
    if (prefix == 0x66 && opcode == 0x90 && !(rex & 1))
        return {};
    if (opcode == 0x0f) {
        const auto extension = reader.read(1);
        if (prefix == 0xf3 && rex == 0 && extension == 0x1e && reader.read(1) == 0xfa)
            return {};
        if (prefix == 0x66 && extension == 0x1f) {
            skipMultiByteNop(reader, rex);
            return {};
        }
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
    if (opcode == 0x64)
        return decodeStackGuard(reader);
    if (opcode == 0x65 && !locked) {
        const auto rex = reader.read(1);
        const auto operation = reader.read(1);
        const auto destination = reader.read(1);
        if ((rex & 0xfb) == 0x48 && operation == 0x8b && (destination & 0xc7) == 4 &&
            reader.read(1) == 0x25 && reader.read(4) == 0x58) {
            const auto reg = unsigned((destination >> 3) & 7) + unsigned(rex & 4) * 2;
            return {Move{8, reg, ThreadLocalStorage{}}};
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
            return {.effect = Move{8, 4, Register{5}}, .after = Move{8, 5, StackTop{}}};
        case 0xd9: {
            const auto modrm = reader.read(1);
            const auto mode = unsigned(modrm >> 6);
            const auto group = (modrm >> 3) & 7;
            if (mode == 3 || (group != 5 && group != 7))
                unsupported();
            return {FloatingControl{x64Address(reader, mode, modrm & 7, rex), 2, group == 5}};
        }
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
            if (locked)
                unsupported();
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
            if ((extension >= 0x10 && extension <= 0x13) || extension == 0x16 || extension == 0x17 ||
                extension == 0x28 || extension == 0x29 ||
                extension == 0x2e || extension == 0x2f || extension == 0x50 || (extension >= 0x54 && extension <= 0x57))
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
    if ((opcode & 0xc7) == 4 && x64Operations[opcode >> 3]) {
        const auto op = opcode >> 3;
        return {ByteBinary{*x64Operations[op], Register{0}, 0, Immediate{reader.read(1)}, 0, op != 7}};
    }

    const bool registerAlu = (opcode & 0xc5) == 1 && x64Operations[opcode >> 3].has_value();
    const bool byteAlu = (opcode & 0xc5) == 0 && x64Operations[opcode >> 3].has_value();
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
            if (opcode & 2)
                return {ByteBinary{*x64Operations[operation], reg, regField, operand, rmField, operation != 7}};
            return {ByteBinary{*x64Operations[operation], operand, rmField, reg, regField, operation != 7}};
        }
        if (opcode == 0x88)
            return {ByteMove{operand, rmField, reg, regField}};
        return {ByteMove{reg, regField, operand, rmField}};
    }
    if (opcode == 0x87) {
        const Value target = mode == 3 ? Value(Register{dst}) : Value(Memory{x64Address(reader, mode, rm, rex)});
        return {Exchange{size, target, Register{src}}};
    }
    if (opcode == 0xf6 && group == 3) {
        const auto [target, field] = byteRegister(dst, rexPresent);
        const Value operand = mode == 3 ? Value(target) : Value(Memory{x64Address(reader, mode, rm, rex)});
        return {ByteBinary{BinaryOp::Sub, operand, field, Immediate{0}, 0, true, false, true}};
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
    if (opcode == 0xf7 && group == 6) {
        const Value divisor = mode == 3 ? Value(Register{dst})
                                        : Value(Memory{x64Address(reader, mode, rm, rex)});
        return {Divide{size, divisor}};
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
    if (opcode == 0x80 && x64Operations[group]) {
        const auto [target, field] = byteRegister(dst, rexPresent);
        const Value operand = mode == 3 ? Value(target) : Value(Memory{x64Address(reader, mode, rm, rex, 1)});
        return {ByteBinary{*x64Operations[group], operand, field, Immediate{reader.read(1)}, 0, group != 7}};
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
    if (mode != 3 && (opcode == 0x81 || opcode == 0x83) && x64Operations[group]) {
        const unsigned bytes = opcode == 0x83 ? 1 : 4;
        const auto addr = x64Address(reader, mode, rm, rex, bytes);
        const auto rhs = immediate(signExtend(reader.read(bytes), 8 * bytes));
        return {MemoryBinary{*x64Operations[group], size, Memory{addr}, rhs, group != 7}};
    }
    if (opcode == 0xf7 && group == 0) {
        const Value target = mode == 3 ? Value(Register{dst})
            : Value(Memory{x64Address(reader, mode, rm, rex, 4)});
        const auto rhs = immediate(signExtend(reader.read(4), 32));
        return {MemoryBinary{BinaryOp::And, size, target, rhs, false}};
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
