#include "image.h"
#include "formats.h"

#include <array>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <optional>

namespace {
using namespace binary;

using Symbols = std::map<std::string_view, std::uint64_t>;

struct MachUnit {
    struct InitSection { std::uint64_t address; std::uint64_t size; unsigned width; };
    std::uint64_t base;
    std::size_t offset;
    std::size_t firstRegion;
    std::size_t regionCount;
    std::string_view name;
    Bytes fixups;
    Symbols definitions;
    Symbols exports;
    std::vector<std::string_view> dependencies;
    std::vector<InitSection> initializers;
    std::optional<std::uint64_t> entry = {};
    // Thread-local templates and the descriptors that address them.
    std::optional<std::size_t> threadTemplate = {};
    std::vector<std::pair<std::size_t, std::size_t>> threadDescriptors = {};
};

Symbols definedSymbols(Bytes table, Bytes strings, bool external = false) {
    Symbols symbols;
    for (std::size_t i = 0; i < table.size(); i += 16) {
        const auto symbol = table.subspan(i, 16);
        if ((symbol[4] & 0xee) == 0x0e && (!external || (symbol[4] & 0x11) == 1))
            symbols.try_emplace(stringAt(strings, read(symbol, 0, 4)), read(symbol, 8, 8));
    }
    return symbols;
}

std::vector<GuestObject> dataObjects(const Image& image, const MachUnit& unit) {
    std::vector<std::uint64_t> addresses;
    for (const auto& [name, address] : unit.definitions)
        if (address >= unit.base)
            addresses.push_back(unit.offset + address - unit.base);
    std::ranges::sort(addresses);
    addresses.erase(std::unique(addresses.begin(), addresses.end()), addresses.end());

    std::vector<GuestObject> objects;
    for (const auto& region : std::span(image.regions).subspan(unit.firstRegion, unit.regionCount)) {
        if (region.executable || !region.readable)
            continue;
        auto next = std::ranges::lower_bound(addresses, region.start);
        const auto prefixEnd = next == addresses.end() ? region.end : std::min(*next, std::uint64_t(region.end));
        if (region.start < prefixEnd)
            objects.push_back({region.start, prefixEnd - region.start});
        // Mach-O nlist has no size field. Use the next symbol or the section boundary.
        while (next != addresses.end() && *next < region.end) {
            const auto start = *next++;
            const auto end = next == addresses.end() ? region.end : std::min(*next, std::uint64_t(region.end));
            objects.push_back({std::size_t(start), std::size_t(end - start)});
        }
    }
    return objects;
}

std::string_view leafName(std::string_view path) {
    return path.substr(path.find_last_of('/') + 1);
}

std::optional<std::uint64_t> findBinding(std::span<const MachUnit> units, const MachUnit& unit,
    unsigned ordinal, std::string_view name) {
    if (ordinal == 0 || ordinal == 0xfd) {
        if (const auto local = unit.definitions.find(name); local != unit.definitions.end() && local->second >= unit.base)
            return unit.offset + local->second - unit.base;
    }
    const auto library = ordinal > 0 && ordinal <= unit.dependencies.size() ?
        leafName(unit.dependencies[ordinal - 1]) : std::string_view{};
    if (!library.empty() || ordinal == 0xfd)
        for (const auto& candidate : units.subspan(1)) {
            if (ordinal != 0xfd && leafName(candidate.name) != library)
                continue;
            const auto symbol = candidate.exports.find(name);
            if (symbol != candidate.exports.end() && symbol->second >= candidate.base)
                return candidate.offset + symbol->second - candidate.base;
        }
    // Libraries re-export symbols from their own dependencies, as libc++ does for libc++abi.
    if (!library.empty())
        for (const auto& candidate : units.subspan(1)) {
            const auto symbol = candidate.exports.find(name);
            if (symbol != candidate.exports.end() && symbol->second >= candidate.base)
                return candidate.offset + symbol->second - candidate.base;
        }
    return {};
}

constexpr unsigned RuneLocaleSize = 3208;

std::size_t addDefaultRuneLocale(Image& image) {
    std::array<std::uint8_t, RuneLocaleSize> data{};
    constexpr std::string_view signature = "RuneMagANONE";
    std::ranges::copy(signature, data.begin());
    const auto put = [&](unsigned at, std::uint32_t value) {
        for (unsigned i = 0; i < 4; ++i)
            data[at + i] = std::uint8_t(value >> (i * 8));
    };
    put(56, 0xfffd);
    for (unsigned c = 0; c < 256; ++c) {
        const bool upper = c >= 'A' && c <= 'Z';
        const bool lower = c >= 'a' && c <= 'z';
        const bool digit = c >= '0' && c <= '9';
        const bool xUpper = c >= 'A' && c <= 'F';
        const bool xLower = c >= 'a' && c <= 'f';
        unsigned type = 0;
        if (upper || lower) type |= 0x100;
        if (c < 32 || c == 127) type |= 0x200;
        if (digit) type |= 0x400 | (c - '0');
        if (c >= 33 && c <= 126) type |= 0x800;
        if (lower) type |= 0x1000;
        if (c >= 33 && c <= 126 && !(upper || lower || digit)) type |= 0x2000;
        if (c == 32 || (c >= 9 && c <= 13)) type |= 0x4000;
        if (upper) type |= 0x8000;
        if (digit || xUpper || xLower) type |= 0x10000;
        if (xUpper || xLower) type |= (c | 32) - 'a' + 10;
        if (c == 9 || c == 32) type |= 0x20000;
        if (c >= 32 && c <= 126) type |= 0x40000;
        put(60 + c * 4, type);
        put(1084 + c * 4, upper ? c + 32 : c);
        put(2108 + c * 4, lower ? c - 32 : c);
    }
    const auto at = (image.bytes.size() + 7) & ~std::size_t(7);
    image.add(at, data.size(), data, true, false, false);
    return at;
}

// Darwin's __stdinp, __stdoutp, and __stderrp variables, each pointing at a synthetic FILE object.
std::size_t addStandardStreams(Image& image, ProgramOptions& program) {
    const auto at = (image.bytes.size() + 15) & ~std::size_t(15);
    std::vector<std::uint8_t> data(3 * StreamObjectSize + 3 * 8);
    for (unsigned i = 0; i < 3; ++i) {
        const auto object = at + i * StreamObjectSize;
        program.streams[i] = object;
        for (unsigned byte = 0; byte < 8; ++byte)
            data[3 * StreamObjectSize + i * 8 + byte] = std::uint8_t(std::uint64_t(object) >> (8 * byte));
    }
    image.add(at, data.size(), data, true, true, false);
    return at;
}

void applyFixups(Image& image, std::span<const MachUnit> units, const MachUnit& unit,
    std::vector<GuestImport>& imports, std::vector<std::size_t>& functionPointers,
    std::vector<GuestBinding>& bindings, std::optional<std::size_t>& stackGuard, std::optional<std::size_t>& runeLocale,
    std::optional<std::size_t>& streams, ProgramOptions& program) {
    const auto fixups = unit.fixups;
    if (read(fixups, 0, 4) != 0 || read(fixups, 20, 4) != 1 || read(fixups, 24, 4) != 0)
        throw std::runtime_error("unsupported Mach-O chained fixup header");
    const auto starts = read(fixups, 4, 4);
    const auto importsAt = read(fixups, 8, 4);
    const auto stringsAt = read(fixups, 12, 4);
    const auto importCount = read(fixups, 16, 4);
    const auto keys = slice(fixups, importsAt, importCount * 4);
    const auto offsets = slice(fixups, starts + 4, read(fixups, starts, 4) * 4);
    for (std::size_t i = 0; i < offsets.size(); i += 4) {
        const auto offset = read(offsets, i, 4);
        if (!offset)
            continue;
        const auto at = starts + offset;
        const auto segment = slice(fixups, at, read(fixups, at, 4));
        const auto size = read(segment, 4, 2);
        const auto kind = read(segment, 6, 2);
        const auto start = unit.offset + read(segment, 8, 8);
        const auto pages = slice(segment, 22, read(segment, 20, 2) * 2);
        if (size < 8 || (kind != 2 && kind != 6) || start >= image.bytes.size())
            throw std::runtime_error("unsupported Mach-O pointer encoding");
        for (std::size_t page = 0; page < pages.size() / 2; ++page) {
            const auto first = read(pages, page * 2, 2);
            if (first == 0xffff)
                continue;
            const auto pageStart = start + page * size;
            for (auto pos = first;;) {
                if (pos > size - 8)
                    throw std::runtime_error("unsupported Mach-O fixup page start or chain");
                const auto address = pageStart + pos;
                const auto value = read(image.bytes, address, 8);
                std::optional<std::uint64_t> target;
                if (value >> 63) {
                    const auto ordinal = value & 0xffffff;
                    const auto key = read(keys, ordinal * 4, 4);
                    const auto name = stringAt(fixups, stringsAt + (key >> 9));
                    const auto dylib = key & 0xff;
                    if (const auto symbol = findBinding(units, unit, dylib, name)) {
                        const auto addend = (value >> 24) & 0xff;
                        target = *symbol + addend - (addend >= 128 ? 256 : 0);
                        if (std::ranges::any_of(image.regions, [&](const GuestRegion& region) {
                            return !region.writable && !region.executable && address >= region.start &&
                                address < region.end && 8 <= region.end - address;
                        }))
                            bindings.push_back({std::size_t(address), std::size_t(*target)});
                    } else if (name == "__DefaultRuneLocale" && (value & 0xff000000) == 0) {
                        if (!runeLocale)
                            runeLocale = addDefaultRuneLocale(image);
                        target = *runeLocale;
                    } else if ((name == "___stdinp" || name == "___stdoutp" || name == "___stderrp") &&
                        (value & 0xff000000) == 0) {
                        if (!streams)
                            streams = addStandardStreams(image, program);
                        const auto index = name == "___stdinp" ? 0 : name == "___stdoutp" ? 1 : 2;
                        target = *streams + 3 * StreamObjectSize + index * 8;
                    } else if (name == "___stack_chk_guard" && (value & 0xff000000) == 0) {
                        if (!stackGuard) {
                            constexpr std::array<std::uint8_t, 8> guard{0, 0xa5, 0xa5, 0xa5, 0x5a, 0x5a, 0x5a, 0x5a};
                            stackGuard = (image.bytes.size() + 7) & ~std::size_t(7);
                            image.add(*stackGuard, guard.size(), guard, true, false, false);
                        }
                        image.relocate(address, *stackGuard);
                    } else {
                        imports.push_back({std::size_t(address), 8, name, true, true});
                        image.relocate(address, 0);
                    }
                } else {
                    const auto pointer = (value & 0xfffffffff) | ((value & 0xff000000000) << 20);
                    if (kind == 2 && pointer < unit.base)
                        throw std::runtime_error("Mach-O rebase target precedes the image");
                    target = unit.offset + (kind == 6 ? pointer : pointer - unit.base);
                }
                if (target) {
                    image.relocate(address, *target);
                    if (std::ranges::any_of(image.regions, [&](const GuestRegion& region) {
                        return region.executable && *target >= region.start && *target < region.end;
                    })) {
                        functionPointers.push_back(*target);
                    } else if (*target < image.bytes.size()) {
                        bindings.push_back({std::size_t(address), std::size_t(*target), false});
                    }
                }
                const auto delta = (value >> 51) & 0xfff;
                if (!delta)
                    break;
                pos += delta * 4;
            }
        }
    }
}

MachUnit mapMachO(Image& image, Architecture architecture, Bytes file, std::size_t mappedBase) {
    const auto cpu = architecture == Architecture::Arm64 ? 0x0100000cu : 0x01000007u;
    if (read(file, 0, 4) != 0xfeedfacf || read(file, 4, 4) != cpu)
        throw std::runtime_error("expected a thin little-endian Mach-O 64-bit image matching the architecture");
    const auto commands = slice(file, 32, read(file, 20, 4));
    const auto commandCount = read(file, 16, 4);
    std::vector<Bytes> segments;
    std::vector<std::string_view> dependencies;
    std::string_view name;
    std::optional<std::uint64_t> entry;
    Bytes symbols, strings, fixups;
    std::optional<std::uint64_t> base;
    std::size_t offset = 0;
    for (std::size_t i = 0; i < commandCount; ++i) {
        const auto command = slice(commands, offset, read(commands, offset + 4, 4));
        if (command.size() < 8)
            throw std::runtime_error("invalid Mach-O load command");
        switch (read(command, 0, 4)) {
            case 0x19:
                if (read(command, 48, 8) && (!base || read(command, 24, 8) < *base))
                    base = read(command, 24, 8);
                segments.push_back(command);
                break;
            case 0x02:
                symbols = slice(file, read(command, 8, 4), read(command, 12, 4) * 16);
                strings = slice(file, read(command, 16, 4), read(command, 20, 4));
                break;
            case 0x80000034:
                fixups = slice(file, read(command, 8, 4), read(command, 12, 4));
                break;
            case 0x0d:
                name = stringAt(command, read(command, 8, 4));
                break;
            case 0x80000028:
                entry = read(command, 8, 8);
                break;
            case 0x0c:
            case 0x80000018:
            case 0x8000001f:
            case 0x20:
            case 0x80000023:
                dependencies.push_back(stringAt(command, read(command, 8, 4)));
                break;
            case 0x22:
            case 0x80000022:
                if (read(command, 12, 4) || read(command, 20, 4) || read(command, 28, 4) || read(command, 36, 4))
                    throw std::runtime_error("legacy Mach-O dyld relocations are unsupported");
                break;
        }
        offset += command.size();
    }
    if (!base || offset != commands.size())
        throw std::runtime_error("Mach-O has invalid load commands or no loadable segments");

    const auto firstRegion = image.regions.size();
    std::vector<MachUnit::InitSection> initSections;
    std::optional<std::size_t> threadTemplate;
    std::vector<std::pair<std::size_t, std::size_t>> threadDescriptors;
    for (const auto segment : segments) {
        const auto permissions = read(segment, 60, 4);
        const bool writable = (permissions & 2) && !(read(segment, 68, 4) & 0x10);
        const auto sections = slice(segment, 72, read(segment, 64, 4) * 80);
        for (std::size_t i = 0; i < sections.size(); i += 80) {
            const auto section = sections.subspan(i, 80);
            const auto address = read(section, 32, 8);
            const auto length = read(section, 40, 8);
            const auto flags = read(section, 64, 4);
            const auto type = flags & 0xff;
            const bool zeroFill = type == 1 || type == 0xc || type == 0x12;
            const bool executable = (permissions & 4) && ((flags & 0x80000400) || type == 8);
            if (address < *base)
                throw std::runtime_error("Mach-O section address precedes the image");
            const auto data = zeroFill ? Bytes{} : slice(file, read(section, 48, 4), length);
            image.add(mappedBase + address - *base, length, data, permissions & 1, writable, executable);
            if (type == 9 || type == 0x16)
                initSections.push_back({mappedBase + address - *base, length, type == 9 ? 8u : 4u});
            if ((type == 0x11 || type == 0x12) && !threadTemplate)
                threadTemplate = mappedBase + address - *base;
            if (type == 0x13)
                threadDescriptors.emplace_back(mappedBase + address - *base, length);
        }
    }

    return {*base, mappedBase, firstRegion, image.regions.size() - firstRegion, name, fixups,
        definedSymbols(symbols, strings), definedSymbols(symbols, strings, true),
        std::move(dependencies), std::move(initSections), entry, threadTemplate, std::move(threadDescriptors)};
}

void appendInitializers(const Image& image, const MachUnit& unit, std::vector<std::size_t>& initializers) {
    for (const auto& section : unit.initializers) {
        if (section.size % section.width != 0)
            throw std::runtime_error("invalid Mach-O initializer section size");
        for (std::uint64_t i = 0; i < section.size; i += section.width) {
            auto target = read(image.bytes, section.address + i, section.width);
            if (section.width == 4)
                target += unit.offset;
            else if (unit.fixups.empty() && target >= unit.base)
                target += unit.offset - unit.base;
            if (!std::ranges::any_of(image.regions, [&](const GuestRegion& region) {
                return region.executable && target >= region.start && target < region.end;
            }))
                throw std::runtime_error("Mach-O initializer target is not executable");
            initializers.push_back(std::size_t(target));
        }
    }
}
}

std::string binary::recompileMachO(Architecture architecture, Bytes file,
    std::span<const GuestExport> exports, bool initialize, std::span<const Bytes> libraries,
    const ProgramOptions& options) {
    auto program = options;
    program.darwin = true;
    std::optional<std::size_t> streams;
    Image image;
    std::vector<MachUnit> units{mapMachO(image, architecture, file, 0)};
    for (const auto library : libraries) {
        const auto offset = (image.bytes.size() + 16383) & ~std::size_t(16383);
        auto unit = mapMachO(image, architecture, library, offset);
        if (unit.name.empty())
            throw std::runtime_error("Mach-O dependency has no dylib install name");
        if (std::ranges::any_of(units, [&](const MachUnit& other) { return leafName(other.name) == leafName(unit.name); }))
            throw std::runtime_error("duplicate Mach-O dependency install name");
        units.push_back(std::move(unit));
    }
    if (std::getenv("LUFT_DEBUG"))
        for (const auto& unit : units)
            std::fprintf(stderr, "Luft: Mach-O %s at guest %#zx (vm base %#llx)\n",
                std::string(unit.name.empty() ? "main" : unit.name).c_str(), unit.offset, (unsigned long long)unit.base);
    std::vector<GuestImport> imports;
    std::vector<std::size_t> functionPointers;
    std::vector<GuestBinding> bindings;
    std::vector<std::size_t> initializers;
    std::vector<GuestObject> objects;
    std::optional<std::size_t> stackGuard;
    std::optional<std::size_t> runeLocale;
    for (const auto& unit : units) {
        if (!unit.fixups.empty())
            applyFixups(image, units, unit, imports, functionPointers, bindings, stackGuard, runeLocale, streams, program);
        auto unitObjects = dataObjects(image, unit);
        objects.insert(objects.end(), unitObjects.begin(), unitObjects.end());
        // A single guest thread keeps each thread-local variable in its template. The descriptor's key word,
        // which dyld fills with a pthread key, instead records where the template starts.
        if (unit.threadTemplate)
            for (const auto& [start, size] : unit.threadDescriptors)
                for (std::size_t at = start; at + 24 <= start + size; at += 24)
                    image.relocate(at + 8, *unit.threadTemplate);
    }
    if (runeLocale)
        objects.push_back({*runeLocale, RuneLocaleSize});
    if (initialize) {
        // Programs initialize their libraries before the executable itself.
        if (program.startup != Startup::Library)
            for (std::size_t i = 1; i < units.size(); ++i)
                appendInitializers(image, units[i], initializers);
        appendInitializers(image, units.front(), initializers);
    }
    if (streams)
        objects.push_back({*streams, 3 * StreamObjectSize + 3 * 8});
    const auto& main = units.front();
    std::vector<GuestExport> mapped(exports.begin(), exports.end());
    for (auto& entry : mapped) {
        auto address = std::uint64_t(entry.offset);
        if (entry.symbol == EntrySymbol) {
            // LC_MAIN stores the entry point as an offset into the __TEXT segment, which maps at the image base.
            if (!main.entry)
                throw std::runtime_error("Mach-O has no LC_MAIN entry point");
            address = main.base + *main.entry;
        } else if (!entry.symbol.empty()) {
            const auto symbol = main.definitions.find(entry.symbol);
            if (symbol == main.definitions.end())
                throw std::runtime_error("Mach-O symbol not found: " + entry.symbol);
            address = symbol->second;
        }
        entry.offset = address >= main.base ? address - main.base : address;
    }
    return recompileMapped(architecture, image.bytes, mapped, image.regions, imports,
        objects, initializers, CallingConvention::Native, bindings, functionPointers, {}, program);
}
