#include "lower.h"

#include <format>

namespace luau {
namespace {
constexpr std::string_view ProgramTypes = R"luau(
export type RunOptions = {
    args: {string}?,
    env: {string}?,
    stdin: string?,
    files: {[string]: string}?,
    stdout: ((string) -> ())?,
    stderr: ((string) -> ())?,
}
export type RunResult = {exitCode: number, stdout: string, stderr: string, files: {[string]: string}}
)luau";
}

std::string printModule(const std::map<ir::Address, std::string>& functions,
    std::span<const GuestExport> exports, const RuntimeFeatures& runtime, const Data& data,
    const ProgramOptions& program) {
    const bool isProgram = program.startup != Startup::Library;
    std::string source = "--!strict\n--!optimize 2\n--!nolint FunctionUnused\n--!nolint LocalUnused\n\n"
        "export type Word = {lo: number, hi: number}\n";
    if (isProgram) {
        // Every run builds a fresh guest process from the shared compiled code.
        source += ProgramTypes;
        source += "\nlocal function instantiate(): (RunOptions?) -> RunResult\n";
    }
    luau::appendRuntime(source, runtime, data);
    if (runtime.process) {
        source += std::format("libc.darwin, libc.arm = {}, {}\n", program.darwin, false);
        for (unsigned i = 0; i < program.streams.size(); ++i)
            if (program.streams[i])
                source += std::format("host.streams[{}] = {}\n", program.streams[i], i);
    }

    std::string body;
    for (const auto& [entry, code] : functions)
        body += std::format("\nlocal function entry_{}(...: Word): Word\n{}end\n", entry, code);
    source += body;

    if (isProgram) {
        const auto entry = exports.front().offset;
        source += std::format(R"luau(
local function run(options: RunOptions?): RunResult
    local settings: RunOptions = options or {{}}
    host.args = settings.args or {{"program"}}
    host.env = settings.env or {{}}
    host.stdin = settings.stdin or ""
    host.stdinAt = 1
    host.output = {{{{}}, {{}}}}
    host.writers = {{settings.stdout, settings.stderr}}
    host.files = table.clone(settings.files or {{}})
    local ok, failure = pcall(entry_{})
    local code = 0
    if not ok then
        if type(failure) == "table" and (failure :: any).luftExit ~= nil then
            code = (failure :: any).luftExit
        elseif {} then
            error(tostring(failure) .. "\n" .. describeTrace(), 0)
        else
            error(failure, 0)
        end
    end
    for fd in host.descriptors do
        hostClose(fd)
    end
    return {{exitCode = code, stdout = table.concat(host.output[1]), stderr = table.concat(host.output[2]),
        files = host.files}}
end

return run
end

-- Each call runs the program in a new guest process.
return table.freeze({{run = function(options: RunOptions?): RunResult
    return instantiate()(options)
end}})
)luau", entry, program.trace);
        return source;
    }

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
