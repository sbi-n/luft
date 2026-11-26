#include "lower.h"

#include <format>

namespace luau {
namespace {
constexpr std::string_view ProgramTypes = R"luau(
export type RunOptions = {
    args: {string}?,
    env: {string}?,
    stdin: string?,
    -- Files by path, relative to `cwd` or absolute. The result's files keep these names; files the program makes
    -- are named relative to `cwd` when they are inside it.
    files: {[string]: string}?,
    -- The working directory, "/work" by default. It and the directories that hold the files exist.
    cwd: string?,
    stdout: ((string) -> ())?,
    stderr: ((string) -> ())?,
    -- Runs about every `yieldInterval` seconds (0.05 by default) while the program runs, for example to yield
    -- with task.wait so the host stays responsive. An error it raises stops the program and comes out of run.
    yield: (() -> ())?,
    yieldInterval: number?,
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
        source += std::format("libc.darwin, libc.arm, libc.windows = {}, {}, {}\n", program.darwin, runtime.arm,
            runtime.windows);
        for (unsigned i = 0; i < program.streams.size(); ++i)
            if (program.streams[i])
                source += std::format("host.streams[{}] = {}\n", program.streams[i], i);
        for (const auto& [start, bytes] : program.threadTemplates)
            source += std::format("process.threadTemplates[{}] = {}\n", start, quoted(bytes));
        for (const auto& [start, bytes] : program.threadBlocks)
            source += std::format("process.threadBlocks[{}] = {}\n", start, quoted(bytes));
    }

    // Entry functions live in one table rather than a local each: the runtime already declares most of the
    // 200 locals a Luau function (here the module or instantiate()) may have, and libraries export many functions.
    std::string body = "\nlocal entries: {[string]: (...Word) -> Word} = {}\n";
    for (const auto& [entry, code] : functions)
        body += std::format("\nentries.entry_{} = function(...: Word): Word\n{}end\n", entry, code);
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
    host.load(settings.files, settings.cwd)
    process.yield = settings.yield
    process.yieldInterval = settings.yieldInterval or 0.05
    process.yieldAt = os.clock()
    local ok, failure = pcall(entries.entry_{})
    local code = 0
    if not ok then
        if type(failure) == "string" and string.find(failure, "buffer access out of bounds", 1, true) then
            -- Translated code indexes the guest memory buffer directly: its bounds check failing is a guest fault.
            failure = "guest accessed unmapped memory (" .. failure .. ")"
        end
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
        files = host.results()}}
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
        source += "\nlocal result = entries.entry_0()\nreturn string.format(\"0x%08x%08x\", result.hi, result.lo)\n";
    } else {
        source += "\nreturn table.freeze({\n";
        for (const auto& entry : exports)
            source += std::format("    [\"{}\"] = entries.entry_{},\n", entry.name, entry.offset);
        source += "})\n";
    }
    return source;
}
}
