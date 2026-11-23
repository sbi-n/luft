#pragma once

#include <cstddef>
#include <cstdint>
#include <optional>
#include <span>
#include <string>
#include <string_view>

enum class Architecture { X86_64, Arm64 };
enum class CallingConvention { Native, Microsoft };

struct GuestExport {
    std::string name;
    std::size_t offset;
    std::string symbol = {};
};

inline constexpr std::size_t MaxImageSize = 64 * 1024;
inline constexpr std::size_t MaxExecutableSize = 16 * 1024 * 1024;

struct GuestRegion {
    std::size_t start;
    std::size_t end;
    bool readable;
    bool writable;
    bool executable;
    bool protectable = false;
};

struct GuestImport {
    std::size_t start;
    std::size_t size;
    std::string_view name;
    bool callable;
    bool leadingUnderscore = false;
    std::string_view library = {};
};

struct GuestObject {
    std::size_t start;
    std::size_t size;
};
struct GuestBinding {
    std::size_t slot;
    std::size_t target;
    bool fixed = true;
};

std::string recompile(Architecture architecture, std::span<const std::uint8_t> image,
    std::span<const GuestExport> exports = {});
std::string recompileMapped(Architecture architecture, std::span<const std::uint8_t> image,
    std::span<const GuestExport> exports, std::span<const GuestRegion> regions,
    std::span<const GuestImport> imports, std::span<const GuestObject> objects = {},
    std::span<const std::size_t> initializers = {}, CallingConvention convention = CallingConvention::Native,
    std::span<const GuestBinding> bindings = {}, std::span<const std::size_t> functionPointers = {},
    std::optional<std::size_t> tlsVector = {});
std::string recompileElf(Architecture architecture, std::span<const std::uint8_t> file,
    std::span<const GuestExport> exports, bool initialize = false,
    std::span<const std::span<const std::uint8_t>> libraries = {});
inline std::string recompileElf(std::span<const std::uint8_t> file, std::span<const GuestExport> exports,
    bool initialize = false) {
    return recompileElf(Architecture::X86_64, file, exports, initialize);
}
