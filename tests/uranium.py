#!/usr/bin/env python3
"""End-to-end test: run the uranium Luau decompiler as Luau code produced by Luft.

uranium (https://github.com/sbi-n/uranium) ships release builds for Linux (ELF, x86-64), macOS (Mach-O,
arm64), and Windows (PE, x86-64). Luft translates each build into a Luau program. Every script in
tests/uranium is compiled with luau-compile at several optimization and debug levels; the translated
decompilers must reproduce the native macOS build's output byte for byte in the default, --ir, and --source
modes.

The Linux build needs Ubuntu 24.04's x86-64 libstdc++.so.6 and libgcc_s.so.1, and the macOS build needs
standalone libc++, libc++abi, and libunwind dylibs (Homebrew's llvm provides them).
"""
import argparse
import concurrent.futures
import os
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
CORPUS = ROOT / "uranium"
LEVELS = [("O0", "g0"), ("O1", "g1"), ("O2", "g2"), ("O2", "g0"), ("O1", "g2")]


def luau_string(data: bytes) -> str:
    return '"' + "".join(chr(b) if 32 <= b < 127 and chr(b) not in '"\\' else f"\\x{b:02x}" for b in data) + '"'


def cases(compile_luau: str, work: Path):
    """Yields (name, argv, files) for every script, level, and mode."""
    result = []
    for script in sorted(CORPUS.glob("*.luau")):
        source = script.read_bytes()
        result.append((f"{script.stem}.source", ["uranium", "--source", "input.luau"], {"input.luau": source}))
        for optimize, debug in LEVELS:
            compiled = subprocess.run([compile_luau, "--binary", f"-{optimize}", f"-{debug}", str(script)],
                                      capture_output=True, check=True).stdout
            name = f"{script.stem}.{optimize}{debug}"
            (work / f"{name}.luauc").write_bytes(compiled)
            result.append((name, ["uranium", "input.luauc"], {"input.luauc": compiled}))
            if (optimize, debug) == ("O2", "g2"):
                result.append((f"{name}.ir", ["uranium", "--ir", "input.luauc"], {"input.luauc": compiled}))
    return result


def native(binary: Path, work: Path, case):
    name, argv, files = case
    scratch = work / "native" / name
    scratch.mkdir(parents=True, exist_ok=True)
    for path, data in files.items():
        (scratch / path).write_bytes(data)
    result = subprocess.run([str(binary), *argv[1:]], cwd=scratch, capture_output=True)
    return result.returncode, result.stdout, result.stderr


def translated(args, module: Path, work: Path, all_cases):
    """Runs every case through one translated module in a single Luau process."""
    script = work / f"{module.stem}_cases.luau"
    lines = [f'local program = require("./{module.stem}")', "local cases = {"]
    for name, argv, files in all_cases:
        file_table = ", ".join(f"[{luau_string(k.encode())}] = {luau_string(v)}" for k, v in files.items())
        lines.append(f"    {{name = {luau_string(name.encode())}, args = {{{', '.join(luau_string(a.encode()) for a in argv)}}}, "
                     f"files = {{{file_table}}}}},")
    lines += ["}",
              "for _, case in cases do",
              "    local ok, result = pcall(program.run, {args = case.args, files = case.files})",
              "    if ok then",
              '        print(string.format("@@CASE %s %d %d %d", case.name, result.exitCode, #result.stdout, #result.stderr))',
              "        print(result.stdout .. result.stderr)",
              "    else",
              '        local message = tostring(result)',
              '        print(string.format("@@CASE %s -1 %d 0", case.name, #message))',
              "        print(message)",
              "    end",
              "end"]
    script.write_text("\n".join(lines) + "\n")
    started = time.time()
    result = subprocess.run([args.luau, script.name], cwd=work, capture_output=True, timeout=args.timeout)
    elapsed = time.time() - started
    if result.returncode:
        raise RuntimeError(f"{module.name} failed: {result.stderr.decode(errors='replace')[:3000]}")
    outputs = {}
    data = result.stdout
    position = 0
    while True:
        start = data.find(b"@@CASE ", position)
        if start < 0:
            break
        header_end = data.index(b"\n", start)
        _, name, code, out_length, err_length = data[start:header_end].decode().split(" ")
        body_start = header_end + 1
        out_length, err_length = int(out_length), int(err_length)
        stdout = data[body_start:body_start + out_length]
        stderr = data[body_start + out_length:body_start + out_length + err_length]
        outputs[name] = (int(code), stdout, stderr)
        position = body_start + out_length + err_length
    return outputs, elapsed


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--release", required=True, help="directory with linux-x86_64, macos-aarch64, windows-x86_64")
    parser.add_argument("--luft", required=True)
    parser.add_argument("--luau", required=True)
    parser.add_argument("--luau-compile", required=True)
    parser.add_argument("--work", required=True)
    parser.add_argument("--elf-libraries", default="", help="comma-separated libstdc++.so.6 and libgcc_s.so.1")
    parser.add_argument("--macho-libraries", default="", help="comma-separated libc++, libc++abi, libunwind dylibs")
    parser.add_argument("--variants", default="elf,macho,pe")
    parser.add_argument("--timeout", type=int, default=3600)
    args = parser.parse_args()

    release = Path(args.release)
    work = Path(args.work)
    work.mkdir(parents=True, exist_ok=True)
    variants = {
        "elf": ["x86_64", release / "linux-x86_64" / "uranium", "--elf"] +
               [item for path in filter(None, args.elf_libraries.split(",")) for item in ("--elf-library", path)],
        "macho": ["arm64", release / "macos-aarch64" / "uranium", "--macho"] +
                 [item for path in filter(None, args.macho_libraries.split(",")) for item in ("--macho-library", path)],
        "pe": ["x86_64", release / "windows-x86_64" / "uranium.exe", "--pe"],
    }
    selected = args.variants.split(",")

    all_cases = cases(args.luau_compile, work)
    reference_binary = release / "macos-aarch64" / "uranium"
    reference = {case[0]: native(reference_binary, work, case) for case in all_cases}
    print(f"{len(all_cases)} cases; native reference collected", flush=True)

    def translate(variant):
        arch, binary, *rest = variants[variant]
        module = work / f"uranium_{variant}.luau"
        started = time.time()
        result = subprocess.run([args.luft, arch, str(binary), "--program", *map(str, rest)], capture_output=True)
        if result.returncode:
            raise RuntimeError(f"Luft failed for {variant}: {result.stderr.decode(errors='replace')}")
        module.write_bytes(result.stdout)
        return module, time.time() - started

    failures = 0
    with concurrent.futures.ThreadPoolExecutor(len(selected)) as pool:
        modules = {variant: pool.submit(translate, variant) for variant in selected}
        runs = {}
        for variant in selected:
            module, seconds = modules[variant].result()
            size = module.stat().st_size / 1e6
            print(f"{variant:6} translated in {seconds:.1f}s ({size:.1f} MB of Luau)", flush=True)
            runs[variant] = pool.submit(translated, args, module, work, all_cases)
        for variant in selected:
            outputs, elapsed = runs[variant].result()
            mismatched = []
            saved = work / "results" / variant
            saved.mkdir(parents=True, exist_ok=True)
            for name, want in reference.items():
                got = outputs.get(name)
                if got is not None and variant == "pe":
                    # The Windows CRT writes text-mode output with CRLF line endings.
                    got = (got[0], got[1].replace(b"\r\n", b"\n"), got[2].replace(b"\r\n", b"\n"))
                (saved / f"{name}.expected").write_bytes(want[1] + want[2])
                (saved / f"{name}.actual").write_bytes(b"" if got is None else got[1] + got[2])
                if got != want:
                    mismatched.append((name, want, got))
            print(f"{variant:6} {len(all_cases) - len(mismatched)}/{len(all_cases)} cases match native "
                  f"({elapsed:.1f}s in Luau)", flush=True)
            for name, want, got in mismatched[:20]:
                print(f"    {name}: want exit {want[0]}, got {'nothing' if got is None else got[0]}")
                if got is not None:
                    detail = (got[1] + got[2]).decode(errors="replace").strip().splitlines()
                    print("        " + "\n        ".join(detail[:6]))
            failures += len(mismatched)
    print("all cases match" if not failures else f"{failures} mismatches")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
