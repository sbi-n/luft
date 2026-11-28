#pragma once

#include <array>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <optional>
#include <set>
#include <span>
#include <string>
#include <string_view>
#include <vector>

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

// Code an unwinder transfers control to, and the code range that makes it reachable: a landing pad's call
// site, or the function whose Windows handler data names a funclet or continuation.
struct LandingPad {
    std::size_t target;
    std::size_t siteStart;
    std::size_t siteEnd;
};

// A mapped object's exception metadata, which the runtime reports to unwinders that look it up.
struct UnwindObject {
    std::size_t start = 0;
    std::size_t end = 0;
    // The Mach-O header.
    std::size_t header = 0;
    // ELF PT_GNU_EH_FRAME (.eh_frame_hdr).
    std::size_t frameHeader = 0;
    // .eh_frame or __eh_frame; the .pdata function table on Windows.
    std::size_t frames = 0;
    std::size_t framesSize = 0;
    // Mach-O __unwind_info.
    std::size_t compact = 0;
    std::size_t compactSize = 0;
};

using LibraryReader = std::function<std::optional<std::vector<std::uint8_t>>(std::string_view)>;

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
    // Exception landing pads and handler code that unwinders transfer to, found in the image's unwind data.
    std::vector<LandingPad> landingPads = {};
    // Where a Windows image is mapped, which GetModuleHandle and the unwinder report.
    std::size_t imageBase = 0;
    // Where the guest's unwinders find each mapped object's exception metadata.
    std::vector<UnwindObject> unwindObjects = {};
    // Function extents reported by the image, as half-open guest address ranges.
    std::vector<std::pair<std::size_t, std::size_t>> functionRanges = {};
    // Darwin thread-local templates by address, with their initial bytes, for guest threads' copies.
    std::vector<std::pair<std::size_t, std::string>> threadTemplates = {};
    // ELF thread-local blocks by address, with their initial bytes: switching guest threads swaps their contents.
    std::vector<std::pair<std::size_t, std::string>> threadBlocks = {};
    // Reports translation failures retained in the generated code as runtime traps.
    std::set<std::string>* diagnostics = nullptr;
    // Supplies guest libraries by name while mapping ELF and Mach-O dependencies.
    LibraryReader readLibrary = {};
    // File names of explicitly supplied ELF libraries, used when their images have no SONAME.
    std::span<const std::string_view> libraryNames = {};
};

// The guest stack sits right after the image. Executables get a larger one than raw code: eight megabytes, the
// main thread's stack on Linux and macOS, which deeply recursive programs such as parsers rely on.
inline constexpr std::size_t MappedStackSize = 8 << 20;
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
    std::span<const GuestExport> exports = {}, const ProgramOptions& program = {});
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
