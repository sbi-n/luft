#include "lower.h"

#include <format>

namespace luau {
std::string printModule(const std::map<ir::Address, std::string>& functions,
    std::span<const GuestExport> exports, const RuntimeFeatures& runtime, const Data& data) {
    std::string source = "--!strict\n--!optimize 2\n--!nolint FunctionUnused\n--!nolint LocalUnused\n\n"
        "export type Word = {lo: number, hi: number}\n";
    luau::appendRuntime(source, runtime, data);

    std::string body;
    for (const auto& [entry, code] : functions)
        body += std::format("\nlocal function entry_{}(...: Word): Word\n{}end\n", entry, code);
    source += body;

    if (exports.empty()) {
        source += "\nlocal result = entry_0()\nreturn string.format(\"0x%08x%08x\", result.hi, result.lo)\n";
    } else {
        source += "\nreturn table.freeze({\n";
        for (const auto& entry : exports)
            source += std::format("    [\"{}\"] = entry_{},\n", entry.name, entry.offset);
        source += "})\n";
    }
    return source;
}
}
