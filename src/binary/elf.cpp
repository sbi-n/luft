#include "recompiler.h"
#include "binary/unwind.h"

#include <algorithm>
#include <array>
#include <bit>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <optional>
#include <stdexcept>
#include <vector>

namespace {
using Bytes = std::span<const std::uint8_t>;
constexpr std::uint64_t LoadBase = 64 * 1024;

Bytes slice(Bytes data, std::uint64_t offset, std::uint64_t size) {
    if (offset > data.size() || size > data.size() - offset)
        throw std::runtime_error("ELF table or segment lies outside the file");
    return data.subspan(offset, size);
}

std::uint64_t read(Bytes data, std::size_t offset, unsigned size) {
    std::uint64_t value = 0;
    const auto field = slice(data, offset, size);
    for (unsigned i = 0; i < size; ++i)
        value |= std::uint64_t(field[i]) << (i * 8);
    return value;
}

std::string_view symbolName(Bytes strings, std::uint64_t offset) {
    if (offset >= strings.size())
        throw std::runtime_error("invalid ELF symbol name offset");
    const auto rest = strings.subspan(offset);
    const auto end = std::find(rest.begin(), rest.end(), 0);
    if (end == rest.end())
        throw std::runtime_error("unterminated ELF symbol name");
    return {reinterpret_cast<const char*>(rest.data()), std::size_t(end - rest.begin())};
}

struct Sections {
    Bytes file;
    Bytes headers;

    Bytes header(std::uint64_t index) const {
        if (index >= headers.size() / 64)
            throw std::runtime_error("invalid ELF section index");
        return slice(headers, index * 64, 64);
    }

    Bytes data(Bytes section) const {
        return slice(file, read(section, 24, 8), read(section, 32, 8));
    }

    Bytes symbols(Bytes section) const {
        const auto type = read(section, 4, 4);
        if ((type != 2 && type != 11) || read(section, 56, 8) != 24)
            throw std::runtime_error("invalid ELF symbol table");
        auto table = data(section);
        if (table.size() % 24 != 0)
            throw std::runtime_error("invalid ELF symbol table size");
        return table;
    }

    Bytes strings(Bytes symbolSection) const {
        const auto section = header(read(symbolSection, 40, 4));
        if (read(section, 4, 4) != 3)
            throw std::runtime_error("invalid ELF string table");
        return data(section);
    }
};

struct SymbolVersions {
    Bytes indices;
    std::uint64_t table = 0;
    std::map<unsigned, std::string_view> names;

    unsigned index(std::uint64_t symbolTable, std::uint64_t ordinal) const {
        return !indices.empty() && symbolTable == table ? unsigned(read(indices, ordinal * 2, 2)) : 0;
    }

    std::string_view version(unsigned index) const {
        index &= 0x7fff;
        if (index < 2)
            return {};
        const auto found = names.find(index);
        if (found == names.end())
            throw std::runtime_error("ELF symbol version has no definition or requirement");
        return found->second;
    }
};

SymbolVersions symbolVersions(const Sections& sections) {
    SymbolVersions result;
    for (std::size_t i = 1; i < sections.headers.size() / 64; ++i) {
        const auto section = sections.header(i);
        const auto type = read(section, 4, 4);
        if (type == 0x6fffffff) {
            result.indices = sections.data(section);
            result.table = read(section, 40, 4);
        }
        if (type != 0x6ffffffd && type != 0x6ffffffe)
            continue;
        const auto strings = sections.data(sections.header(read(section, 40, 4)));
        const auto records = sections.data(section);
        const bool definitions = type == 0x6ffffffd;
        for (std::size_t at = 0; at < records.size();) {
            if (read(records, at, 2) != 1)
                throw std::runtime_error("unsupported ELF symbol version format");
            if (definitions) {
                const auto index = unsigned(read(records, at + 4, 2)) & 0x7fff;
                const auto aux = at + read(records, at + 12, 4);
                result.names.emplace(index, symbolName(strings, read(records, aux, 4)));
            } else {
                auto aux = at + read(records, at + 8, 4);
                const auto count = read(records, at + 2, 2);
                for (std::size_t j = 0; j < count; ++j) {
                    const auto index = unsigned(read(records, aux + 6, 2)) & 0x7fff;
                    result.names.emplace(index, symbolName(strings, read(records, aux + 8, 4)));
                    const auto step = read(records, aux + 12, 4);
                    if (j + 1 < count && step < 16)
                        throw std::runtime_error("invalid ELF symbol version requirement");
                    aux += step;
                }
            }
            const auto next = read(records, at + (definitions ? 16 : 12), 4);
            if (!next)
                break;
            if (next < (definitions ? 20u : 16u) || next >= records.size() - at)
                throw std::runtime_error("invalid ELF symbol version record");
            at += next;
        }
    }
    return result;
}

struct Definition {
    std::uint64_t address;
    unsigned type;
    std::uint64_t size;
    std::size_t tlsBase = 0;
};
using Definitions = std::map<std::pair<std::string_view, std::string_view>, Definition>;
struct CopyRelocation { std::size_t to; std::size_t from; std::size_t size; };

void addDefinitions(const Sections& sections, const SymbolVersions& versions, std::uint64_t base,
    Definitions& definitions, std::optional<GuestObject> tls) {
    for (std::size_t i = 1; i < sections.headers.size() / 64; ++i) {
        const auto section = sections.header(i);
        if (read(section, 4, 4) != 11)
            continue;
        const auto strings = sections.strings(section);
        const auto symbols = sections.symbols(section);
        for (std::size_t j = 0; j < symbols.size() / 24; ++j) {
            const auto symbol = symbols.subspan(j * 24, 24);
            const auto index = read(symbol, 6, 2);
            const auto binding = symbol[4] >> 4;
            const auto type = symbol[4] & 15;
            const auto visibility = symbol[5] & 3;
            if ((binding != 1 && binding != 2 && binding != 10) || (type != 1 && type != 2 && (type != 6 || !tls)) ||
                (visibility != 0 && visibility != 3) || index == 0 || index >= 0xff00)
                continue;
            const auto address = read(symbol, 8, 8);
            if (address >= MaxExecutableSize - base)
                continue;
            const auto name = symbolName(strings, read(symbol, 0, 4));
            const auto version = versions.index(i, j);
            const Definition definition{type == 6 ? address : address + base, unsigned(type), read(symbol, 16, 8),
                type == 6 ? tls->start : 0};
            definitions.try_emplace(std::pair{name, versions.version(version)}, definition);
            if (!(version & 0x8000))
                definitions.try_emplace(std::pair{name, std::string_view{}}, definition);
        }
    }
}

std::uint64_t functionAddress(const Sections& sections, std::string_view name) {
    std::optional<std::uint64_t> address;
    for (std::size_t i = 1; i < sections.headers.size() / 64; ++i) {
        const auto section = sections.header(i);
        const auto type = read(section, 4, 4);
        if (type != 2 && type != 11)
            continue;
        const auto table = sections.symbols(section);
        const auto strings = sections.strings(section);
        for (std::size_t offset = 0; offset < table.size(); offset += 24) {
            const auto symbol = table.subspan(offset, 24);
            const auto sectionIndex = read(symbol, 6, 2);
            if ((symbol[4] & 15) == 2 && sectionIndex != 0 && sectionIndex < 0xff00 &&
                symbolName(strings, read(symbol, 0, 4)) == name) {
                const auto value = read(symbol, 8, 8);
                if (address && *address != value)
                    throw std::runtime_error("ambiguous ELF function symbol: " + std::string(name));
                address = value;
            }
        }
    }
    if (!address)
        throw std::runtime_error("ELF function symbol not found: " + std::string(name));
    return *address;
}

void addDataObjects(const Sections& sections, std::uint64_t base, std::vector<GuestObject>& objects) {
    std::vector<GuestObject> fallback;
    for (std::size_t i = 1; i < sections.headers.size() / 64; ++i) {
        const auto section = sections.header(i);
        const auto type = read(section, 4, 4);
        const auto flags = read(section, 8, 8);
        if ((type == 1 || type == 8) && (flags & 0x407) == 3) {
            const auto address = read(section, 16, 8);
            const auto size = read(section, 32, 8);
            if (address < MaxExecutableSize - base && size && size <= MaxExecutableSize - base - address)
                fallback.push_back({std::size_t(address + base), std::size_t(size)});
        }
        if (type != 2 && type != 11)
            continue;
        const auto table = sections.symbols(section);
        for (std::size_t offset = 0; offset < table.size(); offset += 24) {
            const auto symbol = table.subspan(offset, 24);
            const auto sectionIndex = read(symbol, 6, 2);
            const auto address = read(symbol, 8, 8);
            const auto size = read(symbol, 16, 8);
            if ((symbol[4] & 15) == 1 && sectionIndex != 0 && sectionIndex < 0xff00 &&
                address < MaxExecutableSize - base && size && size <= MaxExecutableSize - base - address) {
                objects.push_back({std::size_t(address + base), std::size_t(size)});
            }
        }
    }
    objects.insert(objects.end(), fallback.begin(), fallback.end());
}

void relocate(const Sections& sections, std::span<std::uint8_t> image,
    std::span<const GuestRegion> regions, std::vector<GuestImport>& imports, Architecture architecture,
    std::uint64_t base, const SymbolVersions& versions, const Definitions& definitions,
    const Definitions& libraryDefinitions, std::vector<CopyRelocation>& copies,
    std::vector<GuestBinding>& bindings, std::vector<std::size_t>& functionPointers,
    std::optional<GuestObject> tls, std::vector<GuestObject>& objects, std::uint64_t threadPointer) {
    const bool arm = architecture == Architecture::Arm64;
    const unsigned copy = arm ? 1024 : 5;
    const unsigned global = arm ? 1025 : 6;
    const unsigned jump = arm ? 1026 : 7;
    const unsigned relative = arm ? 1027 : 8;
    const unsigned absolute = arm ? 257 : 1;
    for (std::size_t i = 1; i < sections.headers.size() / 64; ++i) {
        const auto section = sections.header(i);
        if (!(read(section, 8, 8) & 2))
            continue;
        const auto sectionType = read(section, 4, 4);
        if (sectionType == 9 || sectionType == 19)
            throw std::runtime_error("unsupported ELF relocation table format");
        if (sectionType != 4)
            continue;
        const auto table = sections.data(section);
        if (read(section, 56, 8) != 24 || table.size() % 24 != 0)
            throw std::runtime_error("invalid ELF RELA table");
        const auto symbolTable = read(section, 40, 4);
        const auto linked = sections.header(symbolTable);
        const auto symbols = sections.symbols(linked);
        const auto strings = sections.strings(linked);

        for (std::size_t offset = 0; offset < table.size(); offset += 24) {
            const auto entry = table.subspan(offset, 24);
            const auto address = read(entry, 0, 8);
            const auto info = read(entry, 8, 8);
            const auto type = std::uint32_t(info);
            if (type == 0 || (arm && type == 256))
                continue;
            if (address >= MaxExecutableSize - base)
                throw std::runtime_error("ELF relocation target is outside guest memory");
            const auto at = address + base;
            const auto symbol = slice(symbols, (info >> 32) * 24, 24);
            const auto width = type == copy ? std::max(std::uint64_t(1), read(symbol, 16, 8))
                                        : std::uint64_t(8);
            const auto mapped = [&](std::uint64_t size) {
                return std::ranges::any_of(regions, [&](const GuestRegion& region) {
                    return at >= region.start && at < region.end && size <= region.end - at;
                });
            };
            if (!mapped(width))
                throw std::runtime_error("ELF relocation target is outside load segments");

            const auto name = symbolName(strings, read(symbol, 0, 4));
            const auto addend = read(entry, 16, 8);
            const auto version = versions.version(versions.index(symbolTable, info >> 32));
            if (type == copy && base == LoadBase) {
                const auto source = libraryDefinitions.find({name, version});
                if (source != libraryDefinitions.end() && source->second.type == 1 && source->second.size >= width &&
                    std::ranges::any_of(regions, [&](const GuestRegion& region) {
                        return region.readable && !region.executable && source->second.address >= region.start &&
                            source->second.address < region.end && width <= region.end - source->second.address;
                    })) {
                    copies.push_back({std::size_t(at), std::size_t(source->second.address), std::size_t(width)});
                    continue;
                }
            }
            std::optional<std::uint64_t> result;
            const auto symbolIndex = read(symbol, 6, 2);
            const auto symbolType = unsigned(symbol[4] & 15);
            const bool local = symbolIndex != 0 && ((symbol[4] >> 4) == 0 || (symbol[5] & 3) != 0);
            const auto found = definitions.find({name, version});
            if (type == relative && (info >> 32) == 0) {
                result = base + addend;
            } else if ((!arm && (type == 16 || type == 17 || (type == 18 && threadPointer))) ||
                (arm && type == 1030 && threadPointer)) {
                // Use the TLS block address as its unique module identifier in this guest.
                std::size_t tlsBase = 0;
                std::uint64_t offset = 0;
                if (!local && found != definitions.end() && found->second.type == 6) {
                    tlsBase = found->second.tlsBase;
                    offset = found->second.address;
                } else if (tls && ((info >> 32) == 0 || (symbolType == 6 && symbolIndex != 0 && symbolIndex < 0xff00))) {
                    tlsBase = tls->start;
                    offset = read(symbol, 8, 8);
                }
                if (tlsBase && type == 16) {
                    if (!mapped(16))
                        throw std::runtime_error("ELF TLS descriptor is outside load segments");
                    result = tlsBase;
                    objects.push_back({std::size_t(at), 16});
                } else if (tlsBase && (type == 18 || type == 1030)) {
                    // R_X86_64_TPOFF64 and R_AARCH64_TLS_TPREL64: initial-exec code adds this to the thread pointer.
                    result = tlsBase + offset + addend - threadPointer;
                } else if (tlsBase) {
                    result = offset + addend;
                }
            } else if ((type == absolute || type == jump || type == global) &&
                (arm || name != "__tls_get_addr" || symbolIndex != 0 || (type != jump && type != global))) {
                if (!local && found != definitions.end() && found->second.type != 6 &&
                    (symbolType == 0 || symbolType == found->second.type))
                    result = found->second.address;
                else if (symbolIndex != 0 && symbolIndex < 0xff00 && symbolType <= 2)
                    result = base + read(symbol, 8, 8);
                if (result && (arm || type == absolute))
                    *result += addend;
                if (result && (type == jump || type == global) && *result < image.size())
                    bindings.push_back({std::size_t(at), std::size_t(*result)});
            }
            if (result) {
                for (unsigned byte = 0; byte < 8; ++byte)
                    image[at + byte] = std::uint8_t(*result >> (byte * 8));
                if ((type == relative || type == absolute) && *result < image.size())
                    bindings.push_back({std::size_t(at), std::size_t(*result), false});
                if ((type == relative || type == absolute) && std::ranges::any_of(regions, [&](const GuestRegion& region) {
                    return region.executable && *result >= region.start && *result < region.end;
                }))
                    functionPointers.push_back(*result);
            } else {
                // Absolute relocations to functions fill tables of function pointers, such as SQLite's system calls.
                const bool callable = read(symbol, 6, 2) == 0 &&
                    (type == jump || ((type == global || (type == absolute && addend == 0)) && (symbol[4] & 15) == 2));
                imports.push_back({std::size_t(at), std::size_t(width),
                    name.empty() ? "unknown ELF relocation" : name, callable, false, {}, type == copy});
            }
        }
    }
}

std::vector<std::size_t> initArray(const Sections& sections, Bytes mapped,
    std::span<const GuestRegion> regions, std::uint64_t base) {
    std::vector<std::size_t> result;
    for (std::size_t i = 1; i < sections.headers.size() / 64; ++i) {
        const auto section = sections.header(i);
        if (read(section, 4, 4) != 14 || !(read(section, 8, 8) & 2))
            continue;
        const auto address = read(section, 16, 8);
        const auto size = read(section, 32, 8);
        if (address >= MaxExecutableSize - base || size % 8 != 0)
            throw std::runtime_error("invalid ELF initializer array");
        const auto table = slice(mapped, address + base, size);
        for (std::size_t offset = 0; offset < table.size(); offset += 8) {
            const auto target = read(table, offset, 8);
            if (target == 0 || target == UINT64_MAX)
                continue;
            if (!std::ranges::any_of(regions, [&](const GuestRegion& region) {
                return region.executable && target >= region.start && target < region.end;
            }))
                throw std::runtime_error("ELF initializer target is not executable");
            result.push_back(target);
        }
    }
    return result;
}

Sections mapElf(Architecture architecture, Bytes file, std::uint64_t base,
    std::vector<std::uint8_t>& image, std::vector<GuestRegion>& regions) {
    const unsigned machine = architecture == Architecture::Arm64 ? 183 : 62;
    if (file.size() < 64 || file.size() > MaxExecutableSize ||
        read(file, 0, 4) != 0x464c457f || file[4] != 2 || file[5] != 1 || file[6] != 1 ||
        read(file, 16, 2) != 3 || read(file, 18, 2) != machine || read(file, 20, 4) != 1 ||
        read(file, 52, 2) != 64 || read(file, 54, 2) != 56 || read(file, 58, 2) != 64) {
        throw std::runtime_error("expected an ELF64 little-endian PIE matching the architecture");
    }

    const auto programs = slice(file, read(file, 32, 8), read(file, 56, 2) * 56);
    const Sections sections{file, slice(file, read(file, 40, 8), read(file, 60, 2) * 64)};
    const auto previous = regions.size();
    for (std::size_t offset = 0; offset < programs.size(); offset += 56) {
        const auto section = programs.subspan(offset, 56);
        if (read(section, 0, 4) != 1)
            continue;
        const auto flags = read(section, 4, 4);
        const auto address = read(section, 16, 8);
        if (address >= MaxExecutableSize - base)
            throw std::runtime_error("ELF segment address is outside guest memory");
        const auto at = address + base;
        const auto data = slice(file, read(section, 8, 8), read(section, 32, 8));
        const auto size = read(section, 40, 8);
        if (at > MaxExecutableSize || size > MaxExecutableSize - at || data.size() > size ||
            (!regions.empty() && at < regions.back().end) || ((flags & 3) == 3)) {
            throw std::runtime_error("unsupported ELF load segment layout");
        }
        if (size == 0)
            continue;
        image.resize(at + size);
        std::ranges::copy(data, image.begin() + at);
        regions.push_back({std::size_t(at), std::size_t(at + size),
            bool(flags & 4), bool(flags & 2), bool(flags & 1)});
    }
    if (regions.size() == previous || sections.headers.empty())
        throw std::runtime_error("ELF requires load segments and a section table");

    // Executable segments often hold read-only data too, such as jump tables and string literals. Only
    // SHF_EXECINSTR sections stay executable so the translator can read the rest as data.
    std::vector<std::pair<std::size_t, std::size_t>> code;
    for (std::size_t i = 1; i < sections.headers.size() / 64; ++i) {
        const auto section = sections.header(i);
        const auto flags = read(section, 8, 8);
        const auto address = read(section, 16, 8);
        const auto size = read(section, 32, 8);
        if ((flags & 6) == 6 && size && address < MaxExecutableSize - base && size <= MaxExecutableSize - base - address)
            code.emplace_back(std::size_t(address + base), std::size_t(address + base + size));
    }
    std::ranges::sort(code);
    std::vector<GuestRegion> refined(regions.begin(), regions.begin() + std::ptrdiff_t(previous));
    for (auto i = previous; i < regions.size(); ++i) {
        const auto region = regions[i];
        std::vector<std::pair<std::size_t, std::size_t>> inside;
        for (const auto& [first, last] : code)
            if (first >= region.start && last <= region.end)
                inside.emplace_back(first, last);
        if (!region.executable || inside.empty()) {
            refined.push_back(region);
            continue;
        }
        auto cursor = region.start;
        for (const auto& [first, last] : inside) {
            if (first > cursor)
                refined.push_back({cursor, first, region.readable, region.writable, false});
            if (last > std::max(first, cursor))
                refined.push_back({std::max(first, cursor), last, region.readable, region.writable, true});
            cursor = std::max(cursor, last);
        }
        if (cursor < region.end)
            refined.push_back({cursor, region.end, region.readable, region.writable, false});
    }
    regions = std::move(refined);
    return sections;
}

// Maps an object's TLS template. With `threadPointer`, the block is the executable's and its position sets
// the thread pointer, which is returned there: x86-64 (variant II) puts the block right below the thread
// pointer, and ARM64 (variant I) right above a 16-byte control block at the thread pointer.
std::optional<GuestObject> mapTls(Bytes file, std::uint64_t base, std::vector<std::uint8_t>& image,
    std::vector<GuestRegion>& regions, std::vector<CopyRelocation>& initializers,
    std::uint64_t* threadPointer = nullptr, bool above = false) {
    const auto programs = slice(file, read(file, 32, 8), read(file, 56, 2) * 56);
    for (std::size_t offset = 0; offset < programs.size(); offset += 56) {
        const auto segment = programs.subspan(offset, 56);
        if (read(segment, 0, 4) != 7)
            continue;
        const auto data = slice(file, read(segment, 8, 8), read(segment, 32, 8));
        const auto size = read(segment, 40, 8);
        const auto align = std::max<std::uint64_t>(1, read(segment, 48, 8));
        if (!std::has_single_bit(align) || align > MaxExecutableSize || data.size() > size)
            throw std::runtime_error("unsupported ELF TLS segment layout");
        if (!size)
            return {};
        auto at = (image.size() + align - 1) & ~(align - 1);
        if (threadPointer && above) {
            const auto pointerAlign = std::max<std::uint64_t>(16, align);
            *threadPointer = (image.size() + pointerAlign - 1) & ~(pointerAlign - 1);
            at = *threadPointer + ((16 + align - 1) & ~(align - 1));
            regions.push_back({std::size_t(*threadPointer), std::size_t(*threadPointer + 16), true, true, false});
        } else if (threadPointer) {
            const auto span = (size + align - 1) & ~(align - 1);
            const auto pointerAlign = std::max<std::uint64_t>(64, align);
            *threadPointer = (image.size() + span + pointerAlign - 1) & ~(pointerAlign - 1);
            at = *threadPointer - span;
        }
        if (at >= MaxExecutableSize || size > MaxExecutableSize - at)
            throw std::runtime_error("ELF TLS segment is outside guest memory");
        if (!data.empty()) {
            const auto virtualAddress = read(segment, 16, 8);
            if (virtualAddress >= MaxExecutableSize - base)
                throw std::runtime_error("ELF TLS template is outside guest memory");
            const auto from = base + virtualAddress;
            if (std::ranges::none_of(regions, [&](const GuestRegion& region) {
                    return region.readable && from >= region.start && from < region.end && data.size() <= region.end - from;
                }))
                throw std::runtime_error("ELF TLS template is outside load segments");
            initializers.push_back({std::size_t(at), std::size_t(from), data.size()});
        }
        image.resize(at + size);
        regions.push_back({std::size_t(at), std::size_t(at + size), true, true, false, false, true});
        return GuestObject{std::size_t(at), std::size_t(size)};
    }
    return {};
}
}

// Where libgcc's unwinder finds this object's frame data: _dl_find_object reports PT_GNU_EH_FRAME.
UnwindObject unwindObject(const Sections& sections, std::uint64_t base) {
    const auto file = sections.file;
    const auto programs = slice(file, read(file, 32, 8), read(file, 56, 2) * 56);
    UnwindObject object;
    std::uint64_t low = UINT64_MAX, high = 0;
    for (std::size_t offset = 0; offset < programs.size(); offset += 56) {
        const auto header = programs.subspan(offset, 56);
        const auto type = read(header, 0, 4);
        const auto address = read(header, 16, 8);
        if (type == 1) {
            low = std::min(low, address);
            high = std::max(high, address + read(header, 40, 8));
        } else if (type == 0x6474e550) {
            object.frameHeader = std::size_t(base + address);
        }
    }
    if (low < high) {
        object.start = std::size_t(base + low);
        object.end = std::size_t(base + high);
    }
    const auto names = sections.data(sections.header(read(file, 62, 2)));
    for (std::size_t i = 1; i < sections.headers.size() / 64; ++i) {
        const auto section = sections.header(i);
        if (symbolName(names, read(section, 0, 4)) == ".eh_frame" && read(section, 16, 8)) {
            object.frames = std::size_t(base + read(section, 16, 8));
            object.framesSize = std::size_t(read(section, 32, 8));
        }
    }
    return object;
}

std::string recompileElf(Architecture architecture, Bytes file, std::span<const GuestExport> exports,
    bool initialize, std::span<const Bytes> libraries, const ProgramOptions& options) {
    auto program = options;
    struct Unit {
        Sections sections;
        std::uint64_t base;
        SymbolVersions versions;
        std::optional<GuestObject> tls = {};
    };
    std::vector<GuestRegion> regions;
    std::vector<std::uint8_t> image;
    const auto main = mapElf(architecture, file, LoadBase, image, regions);
    std::vector<Unit> units{{main, LoadBase, symbolVersions(main)}};
    for (const auto library : libraries) {
        const auto base = (image.size() + LoadBase - 1) & ~(LoadBase - 1);
        if (base >= MaxExecutableSize)
            throw std::runtime_error("ELF libraries exceed guest address space");
        auto sections = mapElf(architecture, library, base, image, regions);
        units.push_back({sections, base, symbolVersions(sections)});
    }

    if (std::getenv("LUFT_DEBUG"))
        for (std::size_t i = 0; i < units.size(); ++i)
            std::fprintf(stderr, "Luft: ELF unit %zu at guest %#llx\n", i, (unsigned long long)units[i].base);
    std::vector<CopyRelocation> tlsInitializers;
    std::uint64_t threadPointer = 0;
    std::vector<GuestBinding> bindings;
    std::vector<GuestObject> objects;
    if (architecture == Architecture::X86_64) {
        // Libraries' blocks first, so the executable's ends at the thread pointer, where the thread control
        // block starts with a pointer to itself.
        for (auto unit = units.rbegin(); unit != units.rend(); ++unit)
            unit->tls = mapTls(unit->sections.file, unit->base, image, regions, tlsInitializers,
                unit->base == LoadBase ? &threadPointer : nullptr);
        if (!threadPointer)
            threadPointer = (image.size() + 63) & ~std::size_t(63);
        constexpr std::size_t ControlBlockSize = 64;
        if (threadPointer + ControlBlockSize > MaxExecutableSize)
            throw std::runtime_error("ELF thread control block is outside guest memory");
        image.resize(threadPointer + ControlBlockSize);
        regions.push_back({std::size_t(threadPointer), std::size_t(threadPointer + ControlBlockSize), true, true, false});
        for (unsigned i = 0; i < 8; ++i)
            image[threadPointer + i] = std::uint8_t(threadPointer >> (8 * i));
        objects.push_back({std::size_t(threadPointer), ControlBlockSize});
        bindings.push_back({std::size_t(threadPointer), std::size_t(threadPointer)});
        program.threadBlock = std::size_t(threadPointer);
    } else {
        for (auto& unit : units)
            unit.tls = mapTls(unit.sections.file, unit.base, image, regions, tlsInitializers,
                unit.base == LoadBase ? &threadPointer : nullptr, true);
        if (!threadPointer) {
            threadPointer = (image.size() + 15) & ~std::size_t(15);
            if (threadPointer + 16 > MaxExecutableSize)
                throw std::runtime_error("ELF thread control block is outside guest memory");
            regions.push_back({std::size_t(threadPointer), std::size_t(threadPointer + 16), true, true, false});
        }
        image.resize(std::max<std::size_t>(image.size(), threadPointer + 16));
        objects.push_back({std::size_t(threadPointer), 16});
        program.threadBlock = std::size_t(threadPointer);
    }
    Definitions definitions, libraryDefinitions;
    for (const auto& unit : units) {
        if (!libraries.empty() || unit.tls)
            addDefinitions(unit.sections, unit.versions, unit.base, definitions, unit.tls);
        if (unit.base != LoadBase)
            addDefinitions(unit.sections, unit.versions, unit.base, libraryDefinitions, unit.tls);
    }
    std::vector<GuestImport> imports;
    std::vector<CopyRelocation> copies;
    std::vector<std::size_t> functionPointers;
    for (const auto& unit : units) {
        relocate(unit.sections, image, regions, imports, architecture, unit.base, unit.versions, definitions,
            libraryDefinitions, copies, bindings, functionPointers, unit.tls, objects, threadPointer);
        addDataObjects(unit.sections, unit.base, objects);
    }
    const auto importCount = imports.size();
    copies.insert(copies.end(), tlsInitializers.begin(), tlsInitializers.end());
    for (const auto& copy : copies) {
        const auto data = slice(image, copy.from, copy.size);
        std::ranges::copy(data, image.begin() + copy.to);
        for (std::size_t i = 0; i < importCount; ++i) {
            auto import = imports[i];
            const auto start = std::max(import.start, copy.from);
            const auto end = std::min(import.start + import.size, copy.from + copy.size);
            if (start < end) {
                import.start = copy.to + start - copy.from;
                import.size = end - start;
                imports.push_back(import);
            }
        }
    }
    std::optional<std::size_t> singleThreaded;
    std::optional<std::size_t> stackGuard;
    // glibc's stdin, stdout, and stderr variables point at synthetic FILE objects the runtime recognizes.
    std::optional<std::size_t> streams;
    const auto standardStream = [](std::string_view name) -> std::optional<unsigned> {
        if (name == "stdin") return 0;
        if (name == "stdout") return 1;
        if (name == "stderr") return 2;
        return std::nullopt;
    };
    std::erase_if(imports, [&](const GuestImport& import) {
        const auto stream = import.callable || import.size != 8 ? std::nullopt : standardStream(import.name);
        if (stream) {
            if (!streams) {
                const auto at = (image.size() + 15) & ~std::size_t(15);
                const auto size = 3 * StreamObjectSize + 3 * 8;
                if (at + size > MaxExecutableSize)
                    return false;
                image.resize(at + size);
                regions.push_back({at, at + size, true, true, false});
                objects.push_back({at, size});
                for (unsigned i = 0; i < 3; ++i) {
                    const auto object = at + i * StreamObjectSize;
                    program.streams[i] = object;
                    for (unsigned byte = 0; byte < 8; ++byte)
                        image[at + 3 * StreamObjectSize + i * 8 + byte] = std::uint8_t(std::uint64_t(object) >> (8 * byte));
                }
                streams = at;
            }
            const auto object = *streams + *stream * StreamObjectSize;
            const auto variable = *streams + 3 * StreamObjectSize + *stream * 8;
            // A copy relocation places the FILE pointer itself in the executable; a GOT entry points to it.
            const auto value = import.copy ? object : variable;
            for (unsigned i = 0; i < 8; ++i)
                image[import.start + i] = std::uint8_t(std::uint64_t(value) >> (8 * i));
            bindings.push_back({import.start, value, !import.copy});
            return true;
        }
        if (!import.callable && import.name == "__stack_chk_guard" && import.size == 8) {
            // AArch64 reads the stack protector canary through the GOT. Point it at a synthetic value.
            if (!stackGuard) {
                const auto at = (image.size() + 7) & ~std::size_t(7);
                if (at + 8 > MaxExecutableSize)
                    return false;
                image.resize(at + 8);
                constexpr std::array<std::uint8_t, 8> guard{0, 0xa5, 0xa5, 0xa5, 0x5a, 0x5a, 0x5a, 0x5a};
                std::ranges::copy(guard, image.begin() + at);
                regions.push_back({at, at + 8, true, false, false});
                objects.push_back({at, 8});
                stackGuard = at;
            }
            for (unsigned i = 0; i < 8; ++i)
                image[import.start + i] = std::uint8_t(std::uint64_t(*stackGuard) >> (8 * i));
            bindings.push_back({import.start, *stackGuard});
            return true;
        }
        if (import.callable || import.name != "__libc_single_threaded")
            return false;
        if (import.size == 1) {
            image[import.start] = 1;
            return true;
        }
        if (import.size != 8)
            return false;
        if (!singleThreaded) {
            if (image.size() == MaxExecutableSize)
                return false;
            singleThreaded = image.size();
            image.push_back(1);
            regions.push_back({*singleThreaded, *singleThreaded + 1, true, false, false});
            objects.push_back({*singleThreaded, 1});
        }
        // The translated guest executes on one thread, so glibc's flag stays set.
        for (unsigned i = 0; i < 8; ++i)
            image[import.start + i] = std::uint8_t(std::uint64_t(*singleThreaded) >> (8 * i));
        bindings.push_back({import.start, *singleThreaded});
        return true;
    });
    std::vector<GuestExport> mapped(exports.begin(), exports.end());
    for (auto& entry : mapped) {
        const auto address = entry.symbol == EntrySymbol ? read(file, 24, 8) :
            entry.symbol.empty() ? entry.offset : functionAddress(main, entry.symbol);
        if (address >= MaxExecutableSize - LoadBase)
            throw std::runtime_error("ELF export address is outside guest memory");
        entry.offset = std::size_t(address + LoadBase);
    }
    std::vector<std::size_t> initializers;
    if (initialize) {
        // Programs initialize their libraries before the executable itself.
        if (program.startup != Startup::Library)
            for (std::size_t i = 1; i < units.size(); ++i) {
                const auto unitInitializers = initArray(units[i].sections, image, regions, units[i].base);
                initializers.insert(initializers.end(), unitInitializers.begin(), unitInitializers.end());
            }
        const auto mainInitializers = initArray(main, image, regions, LoadBase);
        initializers.insert(initializers.end(), mainInitializers.begin(), mainInitializers.end());
    }
    // C++ landing pads are reached only through the unwinder, which reads them from the frame data.
    for (const auto& unit : units) {
        const auto object = unwindObject(unit.sections, unit.base);
        program.unwindObjects.push_back(object);
        if (object.frames)
            binary::frameLandingPads(image, object.frames, object.framesSize, program.landingPads);
    }
    // Code reaches thread-local variables at a fixed thread pointer, so switching guest threads swaps the
    // contents of every object's block.
    for (const auto& unit : units)
        if (unit.tls && unit.tls->size)
            program.threadBlocks.emplace_back(unit.tls->start, std::string(image.begin() + std::ptrdiff_t(unit.tls->start),
                image.begin() + std::ptrdiff_t(unit.tls->start + unit.tls->size)));
    return recompileMapped(architecture, image, mapped, regions, imports, objects, initializers,
        CallingConvention::Native, bindings, functionPointers, {}, program);
}
