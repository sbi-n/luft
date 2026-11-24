#pragma once

#include <array>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <span>
#include <string>
#include <string_view>

enum class Architecture { X86_64, Arm64 };
enum class CallingConvention { Native, Microsoft };

// How a translated module starts. Library modules export functions; programs export `run` and start the
// guest the way its platform loader would.
enum class Startup {
    Library,
    ElfStack,       // _start with a System V initial stack; __libc_start_main calls main.
    MainArguments,  // Mach-O LC_MAIN: main(argc, argv, envp, apple) after the initializers.
    WindowsProcess, // PE AddressOfEntryPoint with no arguments; the CRT asks KERNEL32 for its command line.
};

struct ProgramOptions {
    Startup startup = Startup::Library;
    // Guest basic blocks to execute per export call before failing; zero removes the checks.
    std::uint64_t instructionLimit = 40000000;
    // Synthetic C library FILE objects for stdin, stdout, and stderr, or zero when the image has none.
    std::array<std::size_t, 3> streams{};
    // A synthetic Windows thread environment block for GS-relative loads, or zero.
    std::size_t threadBlock = 0;
    // Darwin ABI details: variadic arguments on the stack and BSD open() flags and struct stat.
    bool darwin = false;
    // Record recently executed guest blocks and report them with runtime errors.
    bool trace = false;
};

// The guest stack sits right after the image. Executables get a larger one than raw code.
inline constexpr std::size_t MappedStackSize = 1 << 20;
inline constexpr std::size_t RawStackSize = 1 << 16;

struct GuestExport {
    std::string name;
    std::size_t offset;
    std::string symbol = {};
};

// Export target naming the executable's entry point (ELF e_entry, Mach-O LC_MAIN, PE AddressOfEntryPoint).
inline constexpr std::string_view EntrySymbol = "@entry";

inline constexpr std::size_t MaxImageSize = 64 * 1024;
inline constexpr std::size_t MaxExecutableSize = 16 * 1024 * 1024;

struct GuestRegion {
    std::size_t start;
    std::size_t end;
    bool readable;
    bool writable;
    bool executable;
    bool protectable = false;
    bool threadLocal = false;
};

struct GuestImport {
    std::size_t start;
    std::size_t size;
    std::string_view name;
    bool callable;
    bool leadingUnderscore = false;
    std::string_view library = {};
    // A copy relocation: the range is the imported object itself rather than a pointer to it.
    bool copy = false;
};

// Size of each synthetic C library FILE object; larger than glibc's and Darwin's structures.
inline constexpr std::size_t StreamObjectSize = 256;

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
    std::optional<std::size_t> tlsVector = {}, const ProgramOptions& program = {});
std::string recompileElf(Architecture architecture, std::span<const std::uint8_t> file,
    std::span<const GuestExport> exports, bool initialize = false,
    std::span<const std::span<const std::uint8_t>> libraries = {}, const ProgramOptions& program = {});
inline std::string recompileElf(std::span<const std::uint8_t> file, std::span<const GuestExport> exports,
    bool initialize = false) {
    return recompileElf(Architecture::X86_64, file, exports, initialize);
}
