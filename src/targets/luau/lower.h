#pragma once

#include "runtime.h"

#include <array>
#include <stdexcept>

namespace luau {
inline std::string_view bitOperation(ir::BinaryOp op) {
    switch (op) {
        case ir::BinaryOp::And: return "band";
        case ir::BinaryOp::Or: return "bor";
        case ir::BinaryOp::Xor: return "bxor";
        default: throw std::logic_error("expected bitwise IR operation");
    }
}

inline std::span<const unsigned> argumentRegisters(bool arm, CallingConvention convention) {
    static constexpr std::array<unsigned, 8> arm64{0, 1, 2, 3, 4, 5, 6, 7};
    static constexpr std::array<unsigned, 6> sysv{7, 6, 2, 1, 8, 9};
    static constexpr std::array<unsigned, 4> microsoft{1, 2, 8, 9};
    if (arm)
        return arm64;
    if (convention == CallingConvention::Microsoft)
        return microsoft;
    return sysv;
}

std::optional<std::string> lowerDirect(const ir::Graph& graph, ir::Address entry, bool arm,
    CallingConvention convention);
std::string lowerModule(const ir::Graph& graph, const ir::References& references,
    Architecture architecture, std::span<const GuestExport> exports,
    std::span<const GuestRegion> regions, std::span<const GuestImport> imports,
    std::span<const GuestObject> objects, std::span<const std::size_t> initializers,
    std::span<const std::uint8_t> image, std::span<const ir::CodeRange> code, CallingConvention convention,
    const ProgramOptions& program = {});
std::string printModule(const std::map<ir::Address, std::string>& functions,
    std::span<const GuestExport> exports, const RuntimeFeatures& runtime, const Data& data,
    const ProgramOptions& program = {});
}
