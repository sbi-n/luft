# Luft tests

## Differential tests (`run.py`)

`programs/*.c` export `uint64_t f(uint64_t, uint64_t)` functions; `apps/*.c` are whole programs whose first
line may carry a `// LUFT: {...}` spec (`args`, `stdin`, `files`, `env`, `outputs`). Each is built for
arm64/x86-64 Mach-O (host clang; x86-64 runs under Rosetta), arm64/x86-64 ELF, and x86-64 PE (MinGW), run
natively, translated with Luft (`--module` or `--program`), run with the `luau` CLI, and compared.

```sh
docker build -t luft-toolchain tests      # Linux and MinGW toolchains, qemu-user for x86-64 ELF
python3 tests/run.py --luft path/to/Luft --luau path/to/luau [--levels O0,O2] [--targets arm64-elf,...]
```

Windows programs have no native runner; they reuse the x86-64 ELF results.

## uranium end to end (`uranium.py`)

Translates the [uranium](https://github.com/sbi-n/uranium) release builds (Linux ELF, macOS Mach-O, Windows PE)
with `--program` and checks that they decompile every script in `uranium/` exactly like the native macOS build,
for several `luau-compile` optimization and debug levels and the `--ir` and `--source` modes.

```sh
python3 tests/uranium.py --release DIR --luft Luft --luau luau --luau-compile luau-compile --work DIR \
    --elf-libraries libstdc++.so.6,libgcc_s.so.1 \
    --macho-libraries libc++.1.dylib,libc++abi.1.dylib,libunwind.1.dylib
```

The Linux build maps Ubuntu 24.04's x86-64 libstdc++ and libgcc_s; the macOS build maps standalone libc++,
libc++abi, and libunwind (Homebrew's llvm provides them), since the system copies live in the dyld cache.
The Windows build writes CRLF line endings, which the comparison normalizes.
