#include "recompiler.h"

#include <algorithm>
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
};
using Definitions = std::map<std::pair<std::string_view, std::string_view>, Definition>;
struct CopyRelocation { std::size_t to; std::size_t from; std::size_t size; };

void addDefinitions(const Sections& sections, const SymbolVersions& versions, std::uint64_t base,
    Definitions& definitions) {
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
            if ((binding != 1 && binding != 2 && binding != 10) || (type != 1 && type != 2) ||
                (visibility != 0 && visibility != 3) || index == 0 || index >= 0xff00)
                continue;
            const auto address = read(symbol, 8, 8);
            if (address >= MaxExecutableSize - base)
                continue;
            const auto name = symbolName(strings, read(symbol, 0, 4));
            const auto version = versions.index(i, j);
            const Definition definition{address + base, unsigned(type), read(symbol, 16, 8)};
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
    std::vector<GuestBinding>& bindings, std::vector<std::size_t>& functionPointers) {
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
            const auto mapped = std::ranges::any_of(regions, [&](const GuestRegion& region) {
                return at >= region.start && at < region.end && width <= region.end - at;
            });
            if (!mapped)
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
            if (type == relative && (info >> 32) == 0) {
                result = base + addend;
            } else if (type == absolute || type == jump || type == global) {
                const auto symbolIndex = read(symbol, 6, 2);
                const auto symbolType = unsigned(symbol[4] & 15);
                const bool local = symbolIndex != 0 && ((symbol[4] >> 4) == 0 || (symbol[5] & 3) != 0);
                const auto found = definitions.find({name, version});
                if (!local && found != definitions.end() && (symbolType == 0 || symbolType == found->second.type))
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
                const bool callable = read(symbol, 6, 2) == 0 &&
                    (type == jump || (type == global && (symbol[4] & 15) == 2));
                imports.push_back({std::size_t(at), std::size_t(width),
                    name.empty() ? "unknown ELF relocation" : name, callable});
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
    return sections;
}
}

std::string recompileElf(Architecture architecture, Bytes file, std::span<const GuestExport> exports,
    bool initialize, std::span<const Bytes> libraries) {
    struct Unit {
        Sections sections;
        std::uint64_t base;
        SymbolVersions versions;
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

    Definitions definitions, libraryDefinitions;
    if (!libraries.empty())
        for (const auto& unit : units) {
            addDefinitions(unit.sections, unit.versions, unit.base, definitions);
            if (unit.base != LoadBase)
                addDefinitions(unit.sections, unit.versions, unit.base, libraryDefinitions);
        }
    std::vector<GuestImport> imports;
    std::vector<CopyRelocation> copies;
    std::vector<GuestBinding> bindings;
    std::vector<std::size_t> functionPointers;
    std::vector<GuestObject> objects;
    for (const auto& unit : units) {
        relocate(unit.sections, image, regions, imports, architecture, unit.base, unit.versions, definitions,
            libraryDefinitions, copies, bindings, functionPointers);
        addDataObjects(unit.sections, unit.base, objects);
    }
    const auto importCount = imports.size();
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
    std::erase_if(imports, [&](const GuestImport& import) {
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
        const auto address = entry.symbol.empty() ? entry.offset : functionAddress(main, entry.symbol);
        if (address >= MaxExecutableSize - LoadBase)
            throw std::runtime_error("ELF export address is outside guest memory");
        entry.offset = std::size_t(address + LoadBase);
    }
    const auto initializers = initialize ? initArray(main, image, regions, LoadBase) : std::vector<std::size_t>{};
    return recompileMapped(architecture, image, mapped, regions, imports, objects, initializers,
        CallingConvention::Native, bindings, functionPointers);
}
