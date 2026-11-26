#!/usr/bin/env python3
"""Differential tests: native executables versus their Luft translations.

Each program in tests/programs exports functions of the form
`uint64_t name(uint64_t, uint64_t)`. The harness compiles every program for each
target, runs a native driver for the expected results, translates the same
executable with Luft, runs the Luau module, and compares the outputs.

Linux and Windows targets are built inside the `luft-toolchain` Docker image
(see tests/Dockerfile); Linux x86-64 executables run under qemu-user there.
Windows executables have no native runner, so they reuse the Linux x86-64 results.
"""
import argparse
import concurrent.futures
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
PROGRAMS = ROOT / "programs"
IMAGE = "luft-toolchain"

INPUTS = [
    (0, 0), (1, 2), (5, 7), (100, 3), (7, 0), (2**64 - 1, 1), (2**63, 2**64 - 1),
    (123456789, 987654321), (0xDEADBEEFCAFEBABE, 0x0123456789ABCDEF), (2**32 + 5, 2**31 - 1),
    (2**31, 2**32 - 1), (0x7FF8000000000000, 0x3FF0000000000000), (0x4059000000000000, 0xC059000000000000),
    (2**64 - 1000, 999), (65535, 255),
]

# C++ apps run where a C++ runtime can be mapped: x86-64 Mach-O would need the system's, in the dyld cache.
CXX_TARGETS = {"arm64-macho", "arm64-elf", "x86_64-elf", "x86_64-pe"}
LLVM = Path(os.environ.get("LLVM_PREFIX", "/opt/homebrew/opt/llvm"))
MACHO_CXX_LIBRARIES = [str(LLVM / "lib/c++/libc++.1.dylib"), str(LLVM / "lib/c++/libc++abi.1.dylib"),
                       str(LLVM / "lib/unwind/libunwind.1.dylib")]

TARGETS = {
    "arm64-macho": ("arm64", "--macho", "_"),
    "x86_64-macho": ("x86_64", "--macho", "_"),
    "arm64-elf": ("arm64", "--elf", ""),
    "x86_64-elf": ("x86_64", "--elf", ""),
    "x86_64-pe": ("x86_64", "--pe", ""),
}


def exports(source: Path):
    return re.findall(r"^EXPORT\s+(\w+)\s*\(", source.read_text(), re.M)


def driver(names, cases):
    lines = ["#include <stdint.h>", "#include <stdio.h>"]
    lines += [f"uint64_t {name}(uint64_t, uint64_t);" for name in names]
    lines.append("int main(void) {")
    for name, a, b in cases:
        lines.append(f'    printf("{name} %016llx %016llx %016llx\\n", {a}ull, {b}ull, '
                     f"(unsigned long long){name}({a}ull, {b}ull));")
    lines += ["    return 0;", "}"]
    return "\n".join(lines) + "\n"


def runner(module: str, cases):
    lines = [f'local m = require("./{module}")',
             "local function emit(name, a, b, ok, r)",
             "    if ok then",
             '        print(string.format("%s %s %s %08x%08x", name, a, b, r.hi, r.lo))',
             "    else",
             '        print(string.format("%s %s %s ERROR %s", name, a, b, tostring(r)))',
             "    end",
             "end"]
    for name, a, b in cases:
        lines.append(f'emit("{name}", "{a:016x}", "{b:016x}", pcall(m.{name}, '
                     f"{{lo = {a & 0xFFFFFFFF}, hi = {a >> 32}}}, {{lo = {b & 0xFFFFFFFF}, hi = {b >> 32}}}))")
    return "\n".join(lines) + "\n"


def run(command, **kwargs):
    return subprocess.run(command, capture_output=True, text=True, **kwargs)


def docker(work: Path, script: str):
    result = run(["docker", "run", "--rm", "-v", f"{work}:/work", "-w", "/work", IMAGE, "bash", "-c", script])
    if result.returncode != 0:
        raise RuntimeError(f"docker build failed:\n{result.stdout}\n{result.stderr}")
    return result.stdout


def build(work: Path, program: Path, targets, levels):
    """Compile the program and its driver for every requested target and level."""
    executables = {}
    linux = []
    for target in targets:
        for level in levels:
            name = f"{program.stem}-{target}-{level}"
            out = work / name
            sources = f"{program.name} driver.c"
            if target.endswith("macho"):
                arch = TARGETS[target][0]
                result = run(["clang", "-arch", arch, f"-{level}", "-w", "-o", str(out),
                              str(work / program.name), str(work / "driver.c")])
                if result.returncode:
                    raise RuntimeError(result.stderr)
            elif target == "arm64-elf":
                linux.append(f"gcc -{level} -w -fPIE -pie -o {name} {sources} -lm")
            elif target == "x86_64-elf":
                linux.append(f"x86_64-linux-gnu-gcc -{level} -w -fPIE -pie -o {name} {sources} -lm")
            elif target == "x86_64-pe":
                linux.append(f"x86_64-w64-mingw32-gcc -{level} -w -Wl,--export-all-symbols -o {name}.exe {sources}")
                out = work / f"{name}.exe"
            executables[(target, level)] = out
    if linux:
        docker(work, " && ".join(linux))
    return executables


def expected(work: Path, executables):
    results = {}
    linux = {}
    for (target, level), path in executables.items():
        if target == "arm64-macho":
            results[(target, level)] = run([str(path)]).stdout
        elif target == "x86_64-macho":
            results[(target, level)] = run(["arch", "-x86_64", str(path)]).stdout
        elif target == "arm64-elf":
            linux[(target, level)] = f"./{path.name}"
        elif target == "x86_64-elf":
            linux[(target, level)] = f"qemu-x86_64 -L /usr/x86_64-linux-gnu ./{path.name}"
    if linux:
        marker = "@@LUFT@@"
        script = "; ".join(f"echo {marker}{i}; {command}" for i, command in enumerate(linux.values()))
        output = docker(work, script)
        parts = re.split(rf"{marker}(\d+)\n", output)
        keys = list(linux)
        for index, text in zip(parts[1::2], parts[2::2]):
            results[keys[int(index)]] = text
    for (target, level) in executables:
        if target == "x86_64-pe":
            fallback = results.get(("x86_64-elf", level))
            if fallback is None:
                raise RuntimeError("x86_64-pe requires the x86_64-elf target for its expected results")
            results[(target, level)] = fallback
    return results


def translate(args, work: Path, target, level, path: Path, names, cases):
    arch, flag, prefix = TARGETS[target]
    module = f"{path.stem.replace('.', '_')}_module"
    command = [args.luft, arch, str(path), "--module", flag]
    for name in names:
        command += ["--export", f"{name}={prefix}{name}"]
    result = run(command, timeout=600)
    if result.returncode:
        return f"LUFT ERROR {result.stderr.strip()}"
    (work / f"{module}.luau").write_text(result.stdout)
    script = work / f"{module}_run.luau"
    script.write_text(runner(module, cases))
    try:
        result = run([args.luau, script.name], cwd=work, timeout=args.timeout)
    except subprocess.TimeoutExpired:
        return "LUAU TIMEOUT"
    if result.returncode:
        return f"LUAU ERROR {result.stderr.strip()[:2000]}"
    return result.stdout


def compare(expected_text: str, actual_text: str):
    """Return {function: (failed cases, first failure)} for mismatching results."""
    expected_lines = expected_text.splitlines()
    actual_lines = actual_text.splitlines()
    if len(actual_lines) != len(expected_lines):
        return {"*": (len(expected_lines), actual_text.strip()[:1500] or "no output")}
    failures = {}
    for want, got in zip(expected_lines, actual_lines):
        if want != got:
            name = want.split()[0]
            count, first = failures.get(name, (0, None))
            failures[name] = (count + 1, first or f"want {want}\n          got  {got}")
    return failures


APPS = ROOT / "apps"


def app_spec(source: Path):
    match = re.search(r"^// LUFT: (.*)$", source.read_text(), re.M)
    spec = json.loads(match.group(1)) if match else {}
    spec.setdefault("args", [source.stem])
    spec.setdefault("stdin", "")
    spec.setdefault("files", {})
    spec.setdefault("env", [])
    spec.setdefault("outputs", [])
    # Targets the app does not build for, such as Windows for what msvcrt formats differently from glibc.
    spec.setdefault("skip", [])
    return spec


def luau_literal(value):
    if isinstance(value, str):
        return '"' + "".join(c if 32 <= ord(c) < 127 and c not in '"\\' else f"\\x{ord(c):02x}" for c in value) + '"'
    if isinstance(value, list):
        return "{" + ", ".join(luau_literal(v) for v in value) + "}"
    if isinstance(value, dict):
        return "{" + ", ".join(f"[{luau_literal(k)}] = {luau_literal(v)}" for k, v in value.items()) + "}"
    raise TypeError(value)


def app_report(code, stdout, stderr, files):
    return json.dumps({"exitCode": code, "stdout": stdout, "stderr": stderr, "files": files}, indent=1, sort_keys=True)


def build_apps(work: Path, apps, targets, levels):
    executables = {}
    linux = []
    for app in apps:
        cxx = app.suffix == ".cpp"
        skipped = app_spec(app)["skip"]
        for target in targets:
            if (cxx and target not in CXX_TARGETS) or target in skipped:
                continue
            for level in levels:
                name = f"{app.stem}-{target}-{level}"
                if target.endswith("macho"):
                    arch = TARGETS[target][0]
                    result = run(["clang++" if cxx else "clang", "-arch", arch, f"-{level}", "-w",
                                  *(["-std=c++17"] if cxx else []), "-o", str(work / name), str(work / app.name)])
                    if result.returncode:
                        raise RuntimeError(result.stderr)
                    executables[(app.stem, target, level)] = work / name
                elif target.endswith("elf"):
                    compiler = ("g++" if cxx else "gcc") if target == "arm64-elf" else \
                        ("x86_64-linux-gnu-g++" if cxx else "x86_64-linux-gnu-gcc")
                    # The C++ runtime links statically, so the translation needs no shared libraries.
                    runtime = " -std=c++17 -static-libstdc++ -static-libgcc" if cxx else ""
                    linux.append(f"{compiler} -{level} -w -fPIE -pie{runtime} -o {name} {app.name} -lm")
                    executables[(app.stem, target, level)] = work / name
                elif target == "x86_64-pe":
                    compiler = "x86_64-w64-mingw32-g++ -std=c++17" if cxx else "x86_64-w64-mingw32-gcc"
                    linux.append(f"{compiler} -{level} -w -static -o {name}.exe {app.name}")
                    executables[(app.stem, target, level)] = work / f"{name}.exe"
    if linux:
        docker(work, " && ".join(linux))
    return executables


def native_apps(work: Path, executables, specs):
    """Run each executable natively in a scratch directory holding its input files."""
    results = {}
    linux = []
    for key, path in executables.items():
        app, target, level = key
        spec = specs[app]
        if target == "x86_64-pe":
            continue
        scratch = work / f"run-{path.name}"
        scratch.mkdir(exist_ok=True)
        for name, content in spec["files"].items():
            (scratch / name).parent.mkdir(parents=True, exist_ok=True)
            (scratch / name).write_bytes(content.encode("latin-1"))
        if target.endswith("macho"):
            env = dict(item.split("=", 1) for item in spec["env"])
            result = subprocess.run(spec["args"], executable=str(path), cwd=scratch, input=spec["stdin"].encode("latin-1"),
                                    capture_output=True, env=env)
            files = {name: (scratch / name).read_bytes().decode("latin-1") for name in spec["outputs"]
                     if (scratch / name).exists()}
            results[key] = app_report(result.returncode, result.stdout.decode("latin-1"),
                                      result.stderr.decode("latin-1"), files)
        else:
            # The streams and status sit beside the program's working directory, not in it.
            (work / f"{scratch.name}.stdin").write_bytes(spec["stdin"].encode("latin-1"))
            runner = f"qemu-x86_64 -0 {shlex.quote(spec['args'][0])} -L /usr/x86_64-linux-gnu" \
                if target == "x86_64-elf" else f"bash -c 'exec -a \"$0\" \"$@\"' {shlex.quote(spec['args'][0])}"
            arguments = " ".join(shlex.quote(a) for a in spec["args"][1:])
            env = " ".join(shlex.quote(e) for e in spec["env"])
            linux.append((key, f"cd {shlex.quote(scratch.name)} && env -i {env} {runner} ../{path.name} {arguments} "
                               f"< ../{scratch.name}.stdin > ../{scratch.name}.stdout 2> ../{scratch.name}.stderr; "
                               f"echo $? > ../{scratch.name}.status"))
    if linux:
        docker(work, " ; ".join(f"( {command} )" for _, command in linux))
        for key, _ in linux:
            scratch = work / f"run-{executables[key].name}"
            spec = specs[key[0]]
            files = {name: (scratch / name).read_bytes().decode("latin-1") for name in spec["outputs"]
                     if (scratch / name).exists()}
            stream = lambda kind: (work / f"{scratch.name}.{kind}").read_bytes().decode("latin-1")
            results[key] = app_report(int(stream("status")), stream("stdout"), stream("stderr"), files)
    for key in executables:
        if key[1] == "x86_64-pe":
            results[key] = results.get((key[0], "x86_64-elf", key[2]))
    return results


def translate_app(args, work: Path, key, path: Path, spec):
    app, target, level = key
    arch, flag, _ = TARGETS[target]
    module = f"{path.stem.replace('.', '_').replace('-', '_')}_program"
    libraries = []
    if spec["cxx"] and target == "arm64-macho":
        # The system C++ runtime lives in the dyld cache; standalone copies stand in for it.
        libraries = [item for library in MACHO_CXX_LIBRARIES for item in ("--macho-library", library)]
    result = run([args.luft, arch, str(path), "--program", flag, *libraries], timeout=900)
    if result.returncode:
        return f"LUFT ERROR {result.stderr.strip()}"
    (work / f"{module}.luau").write_text(result.stdout)
    options = luau_literal({"args": spec["args"], "stdin": spec["stdin"], "files": spec["files"], "env": spec["env"]})
    outputs = luau_literal(spec["outputs"])
    script = work / f"{module}_run.luau"
    script.write_text(f"""local program = require("./{module}")
local result = program.run({options})
local function quote(text: string): string
    return '"' .. string.gsub(text, '[%c"\\\\\\128-\\255]', function(c)
        return string.format("\\\\u%04x", string.byte(c))
    end) .. '"'
end
local files = {{}}
for _, name in {outputs} do
    if result.files[name] then table.insert(files, quote(name) .. ": " .. quote(result.files[name])) end
end
print("@@" .. result.exitCode)
print(quote(result.stdout))
print(quote(result.stderr))
print("{{" .. table.concat(files, ", ") .. "}}")
""")
    try:
        result = run([args.luau, script.name], cwd=work, timeout=args.timeout)
    except subprocess.TimeoutExpired:
        return "LUAU TIMEOUT"
    if result.returncode:
        return f"LUAU ERROR {result.stderr.strip()[:3000]}"
    lines = result.stdout.splitlines()
    code = int(lines[-4][2:])
    return app_report(code, json.loads(lines[-3]), json.loads(lines[-2]), json.loads(lines[-1]))


def test_apps(args, targets, levels):
    apps = sorted(APPS.glob("*.c")) + sorted(APPS.glob("*.cpp"))
    if args.apps:
        wanted = set(args.apps.split(","))
        apps = [a for a in apps if a.stem in wanted]
    if not apps:
        return 0
    work = Path(args.work) / "apps"
    if work.exists():
        shutil.rmtree(work)
    work.mkdir(parents=True)
    specs = {}
    for app in apps:
        shutil.copy(app, work / app.name)
        specs[app.stem] = app_spec(app)
        specs[app.stem]["cxx"] = app.suffix == ".cpp"
    executables = build_apps(work, apps, targets, levels)
    wanted = native_apps(work, executables, specs)
    failures = 0
    with concurrent.futures.ThreadPoolExecutor(args.jobs) as pool:
        jobs = {key: pool.submit(translate_app, args, work, key, path, specs[key[0]]) for key, path in executables.items()}
        for key, job in jobs.items():
            actual = job.result()
            expected_report = wanted[key]
            stem = "-".join(key)
            (work / f"{stem}.expected").write_text(expected_report or "")
            (work / f"{stem}.actual").write_text(actual)
            ok = actual == expected_report
            print(f"{key[0]:12} {key[1]:14} {key[2]:3} {'ok' if ok else 'FAILED'}", flush=True)
            if not ok:
                print("    " + actual[:1500].replace("\n", "\n    "))
            failures += not ok
    return failures


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--luft", default=os.environ.get("LUFT", "Luft"))
    parser.add_argument("--luau", default=os.environ.get("LUAU", "luau"))
    parser.add_argument("--work", default=str(ROOT / ".work"))
    parser.add_argument("--targets", default=",".join(TARGETS))
    parser.add_argument("--levels", default="O0,O1,O2,O3,Os")
    parser.add_argument("--programs", default="")
    parser.add_argument("--timeout", type=int, default=300)
    parser.add_argument("--jobs", type=int, default=os.cpu_count() or 4)
    parser.add_argument("--apps", default="", help="comma-separated whole-program tests in tests/apps")
    parser.add_argument("--skip-apps", action="store_true")
    parser.add_argument("--skip-functions", action="store_true")
    args = parser.parse_args()

    targets = args.targets.split(",")
    levels = args.levels.split(",")
    programs = sorted(PROGRAMS.glob("*.c"))
    if args.programs:
        wanted = set(args.programs.split(","))
        programs = [p for p in programs if p.stem in wanted]

    total_failures = 0
    for program in [] if args.skip_functions else programs:
        work = Path(args.work) / program.stem
        if work.exists():
            shutil.rmtree(work)
        work.mkdir(parents=True)
        names = exports(program)
        cases = [(name, a, b) for name in names for a, b in INPUTS]
        shutil.copy(program, work / program.name)
        (work / "driver.c").write_text(driver(names, cases))
        executables = build(work, program, targets, levels)
        wanted = expected(work, executables)
        with concurrent.futures.ThreadPoolExecutor(args.jobs) as pool:
            jobs = {key: pool.submit(translate, args, work, key[0], key[1], path, names, cases)
                    for key, path in executables.items()}
            for key, job in jobs.items():
                actual = job.result()
                stem = f"{program.stem}-{key[0]}-{key[1]}"
                (work / f"{stem}.expected").write_text(wanted[key])
                (work / f"{stem}.actual").write_text(actual)
                failures = compare(wanted[key], actual)
                status = "ok" if not failures else f"{len(failures)} functions FAILED"
                print(f"{program.stem:12} {key[0]:14} {key[1]:3} {status}", flush=True)
                for name, (count, first) in failures.items():
                    print(f"    {name} ({count}/{len(INPUTS)}): {first}")
                total_failures += bool(failures)
    if not args.skip_apps:
        total_failures += test_apps(args, targets, levels)
    print("all passed" if not total_failures else f"{total_failures} configurations failed")
    return 1 if total_failures else 0


if __name__ == "__main__":
    sys.exit(main())
