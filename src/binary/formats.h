#pragma once

#include "recompiler.h"

namespace binary {
struct PeInitRange {
    std::size_t start;
    std::size_t end;
};

std::string recompileMachO(Architecture architecture, std::span<const std::uint8_t> file,
    std::span<const GuestExport> exports, bool initialize = false,
    std::span<const std::span<const std::uint8_t>> libraries = {}, const ProgramOptions& program = {});
std::string recompilePe(Architecture architecture, std::span<const std::uint8_t> file,
    std::span<const GuestExport> exports, std::span<const GuestExport> initializers = {},
    std::span<const PeInitRange> ranges = {}, const ProgramOptions& program = {});
}
