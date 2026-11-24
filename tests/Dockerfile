FROM ubuntu:24.04
RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
    gcc g++ gcc-x86-64-linux-gnu g++-x86-64-linux-gnu clang lld llvm \
    mingw-w64 g++-mingw-w64-x86-64 qemu-user binutils file make cmake ninja-build ca-certificates git \
    && rm -rf /var/lib/apt/lists/*
