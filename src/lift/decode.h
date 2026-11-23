#pragma once

#include "ir/graph.h"

#include <stdexcept>

namespace ir::decode {
struct Reader {
    std::span<const std::uint8_t> image;
    Address pc;
    bool mapped;

    std::uint64_t read(unsigned count) {
        if (pc < 0 || pc + count > Address(image.size()))
            throw std::runtime_error("truncated instruction");
        std::uint64_t value = 0;
        for (unsigned i = 0; i < count; ++i)
            value |= std::uint64_t(image[pc++]) << (8 * i);
        return value;
    }
};

struct Instruction {
    Effect effect = Nop{};
    std::optional<Terminator> end = {};
    std::optional<Address> addressTaken = {};
    Address next = 0;
    std::optional<Effect> after = {};
};

inline Address signExtend(std::uint32_t value, unsigned bits) {
    const auto sign = Address(1) << (bits - 1);
    return (value ^ sign) - sign;
}

inline Immediate immediate(Address value) {
    return {std::uint64_t(value)};
}

[[noreturn]] inline void unsupported() {
    throw std::runtime_error("unsupported instruction");
}

Instruction decodeX64(Reader& reader);
Instruction decodeArm(Reader& reader);
}
