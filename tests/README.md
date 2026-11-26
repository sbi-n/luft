# Luft tests

## Differential tests (`run.py`)

`programs/*.c` export `uint64_t f(uint64_t, uint64_t)` functions; `apps/*.c` are whole programs whose first
line may carry a `// LUFT: {...}` spec (`args`, `stdin`, `files`, `env`, `outputs`, and `skip`, targets the app
does not build for). Each is built for
arm64/x86-64 Mach-O (host clang; x86-64 runs under Rosetta), arm64/x86-64 ELF, and x86-64 PE (MinGW), run
natively, translated with Luft (`--module` or `--program`), run with the `luau` CLI, and compared.

```sh
docker build -t luft-toolchain tests      # Linux and MinGW toolchains, qemu-user for x86-64 ELF
python3 tests/run.py --luft path/to/Luft --luau path/to/luau [--levels O0,O2] [--targets arm64-elf,...]
```

Windows programs have no native runner; they reuse the x86-64 ELF results, so apps whose output msvcrt formats
differently from glibc (`posix_formats.c`) skip `x86_64-pe`, and apps print 64-bit values portably (Windows has a
32-bit `long`). `workloads.c` runs compute-bound code that compilers vectorize at `-O2` and above (structured
loads, table lookups, widening multiplies, fused multiply-adds), so it covers SIMD lifting on every target.
`atomics.c` covers `__atomic` builtins (ARM64 LSE and CAS, x86 `lock` forms) and rounding and by-element vector
code.

Apps that use the POSIX services real programs depend on skip `x86_64-pe`. `files.c` covers the emulated file
system: directories, `stat`, `rename`, `chdir`, `strerror`, calendar time, and `scanf`. A run starts in `/work`
(or the runner's `cwd`), where its files are; `/tmp` always exists. `threads.c` and `threads_cpp.cpp` run guest
threads (pthreads, `std::thread`, condition variables, thread-local variables), which the translation schedules
cooperatively; they print the same lines in any order the threads run. `system.c` covers pseudo-random
sequences, `realloc` and `malloc_size`, `pread`/`pwrite`, `fcntl` locks, temporary files, `fstatfs`, signal
sets, tables of pointers to C library functions, and switches that need no bounds check.

C++ apps (`apps/*.cpp`, built as C++17) cover exceptions and the standard library. ELF builds link the C++
runtime statically; arm64 Mach-O builds map standalone libc++, libc++abi, and libunwind from `$LLVM_PREFIX`
(default `/opt/homebrew/opt/llvm`), since the system copies live in the dyld cache. x86-64 Mach-O has no such
runtime to map, so it skips C++ apps.

## uranium end to end (`uranium.py`)

Translates the [uranium](https://github.com/sbi-n/uranium) release builds (Linux ELF, macOS Mach-O, Windows PE)
with `--program` and checks that they decompile every script in `uranium/` exactly like the native macOS build,
for several `luau-compile` optimization and debug levels and the `--ir` and `--source` modes.

```sh
python3 tests/uranium.py --release DIR --luft Luft --luau luau --luau-compile luau-compile --work DIR \
    --elf-libraries libstdc++.so.6,libgcc_s.so.1 \
    --macho-libraries libc++.1.dylib,libc++abi.1.dylib,libunwind.1.dylib
```

`--corpus DIR` decompiles another directory of scripts instead, such as Luau's `tests/conformance`; the native
build rejects a few of those scripts, and the translated builds must report the same errors.

The Linux build maps Ubuntu 24.04's x86-64 libstdc++ and libgcc_s; the macOS build maps standalone libc++,
libc++abi, and libunwind (Homebrew's llvm provides them), since the system copies live in the dyld cache.
The Windows build writes CRLF line endings, which the comparison normalizes.
