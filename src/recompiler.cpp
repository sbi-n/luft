#include "recompiler.h"
#include "targets/luau/lower.h"

#include <stdexcept>

namespace {
using namespace ir;

bool validExportName(std::string_view name) {
    return name.find_first_of("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz_") == 0 &&
        name.find_first_not_of("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz_0123456789") == std::string_view::npos;
}

}

std::string recompile(Architecture architecture, std::span<const std::uint8_t> image,
    std::span<const GuestExport> exports) {
    if (image.empty() || image.size() > MaxImageSize)
        throw std::runtime_error("guest image must contain 1 to 65536 bytes");
    return recompileMapped(architecture, image, exports, {}, {});
}

std::string recompileMapped(Architecture architecture, std::span<const std::uint8_t> image,
    std::span<const GuestExport> exports, std::span<const GuestRegion> regions,
    std::span<const GuestImport> imports, std::span<const GuestObject> objects,
    std::span<const std::size_t> initializers, CallingConvention convention,
    std::span<const GuestBinding> bindings, std::span<const std::size_t> functionPointers,
    std::optional<std::size_t> tlsVector, const ProgramOptions& program) {
    const bool arm = architecture == Architecture::Arm64;
    std::set<std::string_view> names;
    for (const auto& entry : exports) {
        if (!validExportName(entry.name))
            throw std::runtime_error("invalid export name: " + entry.name);
        if (!names.insert(entry.name).second)
            throw std::runtime_error("duplicate export name: " + entry.name);
        if (entry.offset >= executableEnd(entry.offset, image.size(), regions) || (arm && entry.offset % 4 != 0))
            throw std::runtime_error("invalid guest offset for export " + entry.name);
    }

    std::vector<CodeRange> code;
    References references;
    for (const auto target : functionPointers) {
        if (target < executableEnd(target, image.size(), regions) && (!arm || target % 4 == 0))
            references.functions.insert(target);
    }
    for (const auto& binding : bindings)
        if (binding.target < image.size() && binding.target >= executableEnd(binding.target, image.size(), regions))
            references.data.insert(binding.target);
    std::vector<GuestExport> roots(exports.begin(), exports.end());
    for (const auto pc : initializers)
        roots.push_back({"", pc});
    auto graph = lift(architecture, image, roots, regions, regions.empty() ? &code : nullptr,
        &references, bindings, convention, tlsVector, program.threadBlock);
    // Landing pads become entry points only where their call sites were lifted: each one pulls in the code
    // it reaches, and most functions in mapped libraries never run. Lifting repeats as the pads expose code.
    std::set<std::size_t> pads;
    for (bool added = true; added && !program.landingPads.empty();) {
        added = false;
        for (const auto& pad : program.landingPads) {
            if (pads.contains(pad.target) || pad.target >= executableEnd(pad.target, image.size(), regions) ||
                (arm && pad.target % 4 != 0))
                continue;
            const auto block = graph.lower_bound(Address(pad.siteStart));
            if (block == graph.end() || block->first > Address(pad.siteEnd))
                continue;
            pads.insert(pad.target);
            references.functions.insert(pad.target);
            added = true;
        }
        if (added)
            graph = lift(architecture, image, roots, regions, nullptr, &references, bindings, convention, tlsVector,
                program.threadBlock);
    }
    return luau::lowerModule(graph, references, architecture, exports, regions, imports, objects,
        initializers, image, code, convention, program);
}
