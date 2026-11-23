#include "image.h"
#include "formats.h"

#include <array>

namespace {
using namespace binary;

std::vector<std::size_t> applyRelocations(Image& image, Bytes table, std::uint64_t base) {
    std::vector<std::size_t> functionPointers;
    for (std::size_t block = 0; block < table.size();) {
        const auto page = read(table, block, 4);
        const auto bytes = read(table, block + 4, 4);
        if (bytes < 8 || bytes % 2)
            throw std::runtime_error("invalid PE relocation block");
        const auto entries = slice(table, block + 8, bytes - 8);
        for (std::size_t i = 0; i < entries.size(); i += 2) {
            const auto entry = read(entries, i, 2);
            const auto type = entry >> 12;
            if (!type)
                continue;
            if (type != 10)
                throw std::runtime_error("unsupported PE relocation type");
            const auto at = page + (entry & 0xfff);
            const auto pointer = read(image.bytes, at, 8);
            if (pointer < base)
                throw std::runtime_error("PE relocation points before the image");
            const auto address = pointer - base;
            image.relocate(at, address);
            if (std::ranges::any_of(image.regions, [&](const GuestRegion& region) {
                return region.executable && address >= region.start && address < region.end;
            }))
                functionPointers.push_back(address);
        }
        block += bytes;
    }
    return functionPointers;
}

std::vector<GuestImport> readImports(Bytes image, Bytes directory) {
    std::vector<GuestImport> imports;
    for (std::size_t i = 0; i + 20 <= directory.size(); i += 20) {
        const auto descriptor = directory.subspan(i, 20);
        const auto first = read(descriptor, 16, 4);
        if (!first)
            return imports;
        const auto lookup = read(descriptor, 0, 4);
        const auto library = stringAt(image, read(descriptor, 12, 4));
        for (std::uint64_t j = 0;; j += 8) {
            const auto ordinal = read(image, (lookup ? lookup : first) + j, 8);
            if (!ordinal)
                break;
            slice(image, first + j, 8);
            const auto name = ordinal >> 63 ? std::string_view("ordinal import") : stringAt(image, ordinal + 2);
            imports.push_back({std::size_t(first + j), 8, name, true, false, library});
        }
    }
    if (!directory.empty())
        throw std::runtime_error("PE import table is not terminated");
    return imports;
}

std::uint64_t exportedAddress(Bytes image, Bytes directory, std::uint64_t start, std::string_view symbol) {
    if (!directory.empty()) {
        const auto functions = slice(image, read(directory, 28, 4), read(directory, 20, 4) * 4);
        const auto count = read(directory, 24, 4);
        const auto names = slice(image, read(directory, 32, 4), count * 4);
        const auto indexes = slice(image, read(directory, 36, 4), count * 2);
        for (std::size_t i = 0; i < count; ++i) {
            if (stringAt(image, read(names, i * 4, 4)) != symbol)
                continue;
            const auto target = read(functions, read(indexes, i * 2, 2) * 4, 4);
            if (target >= start && target < start + directory.size())
                throw std::runtime_error("forwarded PE export is unsupported: " + std::string(symbol));
            return target;
        }
    }
    throw std::runtime_error("PE export was not found: " + std::string(symbol));
}
}

std::string binary::recompilePe(Architecture architecture, binary::Bytes file, std::span<const GuestExport> exports,
    std::span<const GuestExport> initializers, std::span<const PeInitRange> ranges) {
    using namespace binary;
    if (read(file, 0, 2) != 0x5a4d)
        throw std::runtime_error("expected a PE image");
    const auto header = read(file, 60, 4);
    const auto cpu = architecture == Architecture::Arm64 ? 0xaa64u : 0x8664u;
    if (read(file, header, 4) != 0x00004550 || read(file, header + 4, 2) != cpu)
        throw std::runtime_error("PE machine does not match the requested architecture");
    const auto opt = slice(file, header + 24, read(file, header + 20, 2));
    if (read(opt, 0, 2) != 0x20b)
        throw std::runtime_error("expected a PE32+ image");
    const auto base = read(opt, 24, 8);
    const auto sections = slice(file, header + 24 + opt.size(), read(file, header + 6, 2) * 40);
    Image image;
    for (std::size_t i = 0; i < sections.size(); i += 40) {
        const auto section = sections.subspan(i, 40);
        const auto start = read(section, 12, 4);
        const auto size = read(section, 8, 4);
        const auto length = read(section, 16, 4);
        const auto flags = read(section, 36, 4);
        const auto data = slice(file, read(section, 20, 4), std::min(size, length));
        constexpr std::array<std::uint8_t, 8> functionPointers{'.', 'f', 'p', 't', 'a', 'b', 'l', 'e'};
        const bool protectable = std::ranges::equal(section.first(8), functionPointers);
        image.add(start, size, data, flags & 0x40000000, flags & 0x80000000, flags & 0x20000000, protectable);
    }
    if (image.regions.empty())
        throw std::runtime_error("PE has no loadable sections");
    const auto directories = slice(opt, 112, read(opt, 108, 4) * 8);
    const auto directoryRva = [&](std::size_t id) {
        return id < directories.size() / 8 ? read(directories, id * 8, 4) : 0;
    };
    const auto directory = [&](std::size_t id) -> Bytes {
        const auto at = directoryRva(id);
        return at ? slice(image.bytes, at, read(directories, id * 8 + 4, 4)) : Bytes{};
    };
    const auto functionPointers = applyRelocations(image, directory(5), base);
    auto imports = readImports(image.bytes, directory(1));
    const auto relative = [base](std::uint64_t address) { return std::size_t(address >= base ? address - base : address); };
    std::optional<std::size_t> tlsVector;
    std::vector<GuestBinding> bindings;
    if (const auto tls = directory(9); !tls.empty()) {
        const auto start = relative(read(tls, 0, 8));
        const auto end = relative(read(tls, 8, 8));
        const auto index = relative(read(tls, 16, 8));
        const auto zeroFill = read(tls, 32, 4);
        if (end < start || (end > start && !std::ranges::any_of(image.regions, [&](const GuestRegion& region) {
            return region.readable && !region.executable && start >= region.start && end <= region.end;
        })) || !std::ranges::any_of(image.regions, [&](const GuestRegion& region) {
            return region.writable && index >= region.start && index < region.end && region.end - index >= 4;
        }))
            throw std::runtime_error("invalid PE thread-local storage directory");
        const auto initial = slice(image.bytes, start, end - start);
        const std::vector<std::uint8_t> templateBytes(initial.begin(), initial.end());
        const auto storage = (image.bytes.size() + 15) & ~std::size_t(15);
        image.add(storage, std::max(std::uint64_t(1), end - start + zeroFill), templateBytes, true, true, false);
        tlsVector = (image.bytes.size() + 7) & ~std::size_t(7);
        image.add(*tlsVector, 8, {}, true, false, false);
        image.relocate(*tlsVector, storage);
        std::fill_n(image.bytes.begin() + index, 4, 0);
        bindings.push_back({*tlsVector, storage, false});
    }
    const auto resolve = [&](const GuestExport& entry) {
        const auto address = entry.symbol.empty() ? entry.offset :
            exportedAddress(image.bytes, directory(0), directoryRva(0), entry.symbol);
        return relative(address);
    };
    std::vector<GuestExport> mapped(exports.begin(), exports.end());
    for (auto& entry : mapped)
        entry.offset = resolve(entry);
    std::vector<std::size_t> init;
    const auto addInitializer = [&](std::size_t address) {
        if (!std::ranges::any_of(image.regions, [&](const GuestRegion& region) {
            return region.executable && address >= region.start && address < region.end;
        }))
            throw std::runtime_error("PE initializer target is not executable");
        init.push_back(address);
    };
    for (const auto& entry : initializers)
        addInitializer(resolve(entry));
    for (const auto& range : ranges) {
        const auto start = relative(range.start);
        const auto end = relative(range.end);
        if (start > end || (end - start) % 8 || !std::ranges::any_of(image.regions, [&](const GuestRegion& region) {
            return region.readable && !region.executable && start >= region.start && end <= region.end;
        })) {
            throw std::runtime_error("invalid PE initializer table");
        }
        for (auto offset = start; offset < end; offset += 8) {
            const auto target = read(image.bytes, offset, 8);
            if (target)
                addInitializer(relative(target));
        }
    }
    std::vector<GuestObject> objects;
    // Stripped PE images lack data symbol sizes. Materialize a writable section once it is referenced.
    for (const auto& section : image.regions)
        if (section.readable && (section.writable || section.protectable))
            objects.push_back({section.start, section.end - section.start});
    if (tlsVector)
        objects.push_back({*tlsVector, 8});
    return recompileMapped(architecture, image.bytes, mapped, image.regions, imports, objects, init,
        CallingConvention::Microsoft, bindings, functionPointers, tlsVector);
}
