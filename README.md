# Luft

Luft recompiles x86-64 and arm64 machine code (raw, ELF, Mach-O, PE) into Luau.

```sh
Luft <x86_64|arm64> <binary> [--emit | --module]
Luft <x86_64|arm64> <executable> --program <format>
```

Use `--elf`, `--macho`, or `--pe` for `<format>`. With ELF or Mach-O, pass `--library-dir PATH` to include
dependencies from their actual guest libraries. Luft follows the executable's and each library's dependency
list and looks up file names in the specified directories. Repeat the option to search more than one directory.
Use `--elf-library PATH` or `--macho-library PATH` to supply a particular library file explicitly.
Libraries are needed during translation. The generated Luau contains the code it uses.
When Luft emits source, it reports known translation gaps on standard error. If a program reaches one of
those paths, the generated Luau reports the error at runtime.

Run `Luft --help` for the full usage.

## Third-party notices

The Luft executable statically links [Luau](https://github.com/luau-lang/luau), which is distributed under the following license:

```text
MIT License

Copyright (c) 2019-2025 Roblox Corporation
Copyright (c) 1994–2019 Lua.org, PUC-Rio.

Permission is hereby granted, free of charge, to any person obtaining a copy of
this software and associated documentation files (the "Software"), to deal in
the Software without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
of the Software, and to permit persons to whom the Software is furnished to do
so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
```
