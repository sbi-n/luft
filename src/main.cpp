#include "recompiler.h"
#include "binary/formats.h"

#include "Luau/Compiler.h"
#include "lua.h"
#include "lualib.h"

#include <charconv>
#include <fstream>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string_view>
#include <system_error>
#include <vector>

namespace {
enum class Format { Raw, Elf, MachO, Pe };

GuestExport parseExport(std::string_view spec) {
    const auto separator = spec.find('=');
    if (separator == std::string_view::npos || separator == 0)
        throw std::runtime_error("expected --export NAME=OFFSET");
    const auto name = spec.substr(0, separator);
    auto address = spec.substr(separator + 1);
    const bool hex = address.starts_with("0x") || address.starts_with("0X");
    const auto target = address;
    if (hex)
        address.remove_prefix(2);

    std::size_t offset = 0;
    const auto end = address.data() + address.size();
    const auto result = std::from_chars(address.data(), end, offset, hex ? 16 : 10);
    if (result.ec != std::errc{} || result.ptr != end) {
        if (target.empty() || hex || (target.front() >= '0' && target.front() <= '9') || target.front() == '-')
            throw std::runtime_error("invalid offset for export " + std::string(name));
        return {std::string(name), 0, std::string(target)};
    }
    return {std::string(name), offset};
}

std::vector<std::uint8_t> readImage(const char* path, std::size_t limit) {
    std::ifstream file(path, std::ios::binary);
    if (!file)
        throw std::runtime_error("could not open " + std::string(path));
    std::vector<std::uint8_t> image(limit + 1);
    file.read(reinterpret_cast<char*>(image.data()), image.size());
    if (file.bad() || (file.fail() && !file.eof()))
        throw std::runtime_error("could not read " + std::string(path));
    image.resize(file.gcount());
    if (image.size() > limit)
        throw std::runtime_error("input exceeds the size limit: " + std::string(path));
    return image;
}

binary::PeInitRange parsePeRange(std::string_view text) {
    const auto separator = text.find(':');
    if (separator == std::string_view::npos)
        throw std::runtime_error("expected --pe-init-table START:END");
    const auto start = parseExport("start=" + std::string(text.substr(0, separator)));
    const auto end = parseExport("end=" + std::string(text.substr(separator + 1)));
    if (!start.symbol.empty() || !end.symbol.empty())
        throw std::runtime_error("PE initializer table bounds must be addresses");
    return {start.offset, end.offset};
}
}

int main(int argc, char** argv) {
    constexpr auto usage =
        "Usage: Luft <x86_64|arm64> <binary> [--emit | --module [--export NAME=OFFSET]...]\n"
        "       Luft <x86_64|arm64> <elf> --module --elf [--elf-init] [--elf-library PATH]... --export NAME=SYMBOL|ADDRESS\n"
        "       Luft <x86_64|arm64> <mach-o> --module --macho [--macho-init] [--macho-library PATH]... --export NAME=SYMBOL|ADDRESS\n"
        "       Luft <x86_64|arm64> <pe> --module --pe [--pe-init SYMBOL|ADDRESS] [--pe-init-table START:END] --export NAME=SYMBOL|ADDRESS\n"
        "Execute little-endian machine code starting at file offset 0.\n"
        "Print RAX or X0 as 16 hex digits on return.\n"
        "Pass --emit to print standalone Luau source, or --module to print a callable module.\n"
        "Module exports use decimal or hex file offsets and default to entry=0.\n"
        "Arguments are {lo, hi} words passed in the input ABI's integer argument registers.\n"
        "Mach-O and PE accept symbol names, virtual addresses, or image-relative addresses.\n"
        "Pass --program with an executable format to translate the whole program: the module exports\n"
        "run({args = {...}, stdin = text, files = {[path] = bytes}}) returning {exitCode, stdout, stderr, files}.\n"
        "Pass --instruction-limit N to bound guest basic blocks per call (0 disables the check).\n"
        "Pass --trace to report the most recently executed guest blocks with runtime errors.\n";
    if (argc == 2 && std::string_view(argv[1]) == "--help") {
        std::cout << usage;
        return 0;
    }
    if (argc < 3) {
        std::cerr << usage;
        return 1;
    }

    try {
        const std::string_view machine = argv[1];
        if (machine != "x86_64" && machine != "arm64")
            throw std::runtime_error("expected x86_64 or arm64");
        const auto architecture = machine == "arm64" ? Architecture::Arm64 : Architecture::X86_64;

        bool emit = false;
        bool module = false;
        bool program = false;
        bool trace = false;
        std::optional<std::uint64_t> instructionLimit;
        auto format = Format::Raw;
        bool elfInit = false;
        bool machoInit = false;
        std::vector<GuestExport> exports;
        std::vector<GuestExport> peInitializers;
        std::vector<binary::PeInitRange> peInitRanges;
        std::vector<const char*> elfLibraries;
        std::vector<const char*> machoLibraries;
        for (int i = 3; i < argc; ++i) {
            const std::string_view option = argv[i];
            if (option == "--emit" && !emit)
                emit = true;
            else if (option == "--module" && !module)
                module = true;
            else if (format == Format::Raw && option == "--elf")
                format = Format::Elf;
            else if (format == Format::Raw && option == "--macho")
                format = Format::MachO;
            else if (format == Format::Raw && option == "--pe")
                format = Format::Pe;
            else if (option == "--elf-init" && !elfInit)
                elfInit = true;
            else if (option == "--macho-init" && !machoInit)
                machoInit = true;
            else if (option == "--pe-init" && i + 1 < argc)
                peInitializers.push_back(parseExport(std::string("initializer=") + argv[++i]));
            else if (option == "--pe-init-table" && i + 1 < argc)
                peInitRanges.push_back(parsePeRange(argv[++i]));
            else if (option == "--elf-library" && i + 1 < argc)
                elfLibraries.push_back(argv[++i]);
            else if (option == "--macho-library" && i + 1 < argc)
                machoLibraries.push_back(argv[++i]);
            else if (option == "--export" && i + 1 < argc)
                exports.push_back(parseExport(argv[++i]));
            else if (option == "--program" && !program)
                program = true;
            else if (option == "--trace" && !trace)
                trace = true;
            else if (option == "--instruction-limit" && i + 1 < argc && !instructionLimit) {
                const std::string_view text = argv[++i];
                std::uint64_t limit = 0;
                const auto parsed = std::from_chars(text.data(), text.data() + text.size(), limit);
                if (parsed.ec != std::errc{} || parsed.ptr != text.data() + text.size())
                    throw std::runtime_error("invalid --instruction-limit");
                instructionLimit = limit;
            }
            else
                throw std::runtime_error("invalid option: " + std::string(option));
        }
        ProgramOptions options;
        if (program) {
            if (format == Format::Raw || module || emit || !exports.empty())
                throw std::runtime_error("--program requires --elf, --macho, or --pe without --module, --emit, or --export");
            module = true;
            exports.push_back({"run", 0, std::string(EntrySymbol)});
            options.startup = format == Format::Elf ? Startup::ElfStack :
                format == Format::MachO ? Startup::MainArguments : Startup::WindowsProcess;
            options.instructionLimit = 0;
            if (format == Format::Elf)
                elfInit = true;
            else if (format == Format::MachO)
                machoInit = true;
        }
        if (instructionLimit)
            options.instructionLimit = *instructionLimit;
        options.trace = trace;
        if (emit && module)
            throw std::runtime_error("choose either --emit or --module");
        if (format != Format::Raw && (!module || exports.empty()))
            throw std::runtime_error("executable formats require --module and at least one --export");
        if (elfInit && format != Format::Elf)
            throw std::runtime_error("--elf-init requires --elf");
        if (!elfLibraries.empty() && format != Format::Elf)
            throw std::runtime_error("--elf-library requires --elf");
        if (machoInit && format != Format::MachO)
            throw std::runtime_error("--macho-init requires --macho");
        if (!machoLibraries.empty() && format != Format::MachO)
            throw std::runtime_error("--macho-library requires --macho");
        if ((!peInitializers.empty() || !peInitRanges.empty()) && format != Format::Pe)
            throw std::runtime_error("PE initializers require --pe");
        for (const auto& entry : exports)
            if (format == Format::Raw && !entry.symbol.empty())
                throw std::runtime_error("symbol exports require an executable format: " + entry.symbol);
        if (!module && !exports.empty())
            throw std::runtime_error("--export requires --module");
        if (module && exports.empty())
            exports.push_back({"entry", 0});

        const auto maxSize = format == Format::Raw ? MaxImageSize : MaxExecutableSize;
        const auto image = readImage(argv[2], maxSize);
        std::vector<std::vector<std::uint8_t>> libraryImages;
        for (const auto library : format == Format::MachO ? machoLibraries : elfLibraries)
            libraryImages.push_back(readImage(library, MaxExecutableSize));
        std::vector<std::span<const std::uint8_t>> libraries(libraryImages.begin(), libraryImages.end());

        std::string source;
        switch (format) {
            case Format::Raw: source = recompile(architecture, image, exports); break;
            case Format::Elf: source = recompileElf(architecture, image, exports, elfInit, libraries, options); break;
            case Format::MachO:
                source = binary::recompileMachO(architecture, image, exports, machoInit, libraries, options);
                break;
            case Format::Pe:
                source = binary::recompilePe(architecture, image, exports, peInitializers, peInitRanges, options);
                break;
        }
        if (emit || module) {
            std::cout << source;
        } else {
            const auto bytecode = Luau::compile(source);
            const std::unique_ptr<lua_State, decltype(&lua_close)> vm(luaL_newstate(), lua_close);
            if (!vm)
                throw std::runtime_error("could not create Luau state");
            luaL_openlibs(vm.get());
            luaL_sandbox(vm.get());
            if (luau_load(vm.get(), "=guest", bytecode.data(), bytecode.size(), 0) != 0 ||
                lua_pcall(vm.get(), 0, 1, 0) != 0) {
                const auto message = lua_tostring(vm.get(), -1);
                throw std::runtime_error(message ? message : "Luau execution failed");
            }
            std::cout << lua_tostring(vm.get(), -1) << '\n';
        }
        if (!std::cout)
            throw std::runtime_error("could not write output");
    } catch (const std::exception& error) {
        std::cerr << "Luft: " << error.what() << '\n';
        return 1;
    }
}
