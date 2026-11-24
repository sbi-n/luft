cmake_minimum_required(VERSION 4.4)
project(Luft)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

include(FetchContent)
set(LUAU_BUILD_CLI OFF CACHE BOOL "Build the Luau CLI")
set(LUAU_BUILD_TESTS OFF CACHE BOOL "Build the Luau test suite")
FetchContent_Declare(luau
    GIT_REPOSITORY https://github.com/luau-lang/luau.git
    GIT_TAG 0.736
    GIT_SHALLOW TRUE
    EXCLUDE_FROM_ALL
)
FetchContent_MakeAvailable(luau)

add_library(Luft.IR STATIC src/ir/analysis.cpp)
target_include_directories(Luft.IR PRIVATE src)

add_library(Luft.Target.Luau STATIC
    src/targets/luau/lower.cpp
    src/targets/luau/direct.cpp
    src/targets/luau/printer.cpp
    src/targets/luau/runtime.cpp
)
target_include_directories(Luft.Target.Luau PRIVATE src)
target_link_libraries(Luft.Target.Luau PRIVATE Luft.IR)

add_executable(Luft
    src/main.cpp
    src/recompiler.cpp
    src/binary/elf.cpp
    src/binary/macho.cpp
    src/binary/pe.cpp
    src/binary/unwind.cpp
    src/lift/builder.cpp
    src/lift/x64.cpp
    src/lift/arm64.cpp
)
target_include_directories(Luft PRIVATE src)
target_link_libraries(Luft PRIVATE Luft.Target.Luau Luft.IR Luau.Compiler Luau.VM)
