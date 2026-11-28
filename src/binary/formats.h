#pragma once

#include "recompiler.h"

namespace binary {
struct LibraryDependencies {
    std::string_view name;
    std::vector<std::string_view> needed;
};

std::string_view libraryName(std::string_view path);
std::vector<std::size_t> loadDependencies(std::vector<LibraryDependencies> dependencies, const LibraryReader& read,
    std::vector<std::vector<std::uint8_t>>& files,
    const std::function<LibraryDependencies(std::span<const std::uint8_t>)>& load);

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
