#include "formats.h"

#include <array>
#include <cerrno>
#include <cstdlib>
#include <fstream>
#include <initializer_list>
#include <iostream>
#include <stdexcept>
#include <system_error>
#include <vector>

#ifdef _WIN32
#include <process.h>
#else
#include <spawn.h>
#include <sys/wait.h>
extern char** environ;
#endif

namespace binary {
namespace {
void runSpider(const char* executable, std::initializer_list<const char*> arguments) {
    std::vector<std::string> words{executable};
    words.insert(words.end(), arguments.begin(), arguments.end());
#ifdef _WIN32
    for (auto& word : words) {
        if (word.find('"') != std::string::npos)
            throw std::runtime_error("invalid quote in Windows Spider argument");
        if (word.find_first_of(" \t") != std::string::npos) {
            const auto last = word.find_last_not_of('\\');
            word = "\"" + word + std::string(word.size() - last - 1, '\\') + '"';
        }
    }
#endif
    std::vector<char*> argv;
    for (auto& word : words)
        argv.push_back(word.data());
    argv.push_back(nullptr);
    std::cout.flush();

#ifdef _WIN32
    const auto result = _spawnvp(_P_WAIT, executable, argv.data());
    if (result == -1)
        throw std::system_error(errno, std::generic_category(), "could not start Spider (LUFT_SPIDER or PATH)");
    const bool success = result == 0;
#else
    pid_t pid;
    const auto launch = posix_spawnp(&pid, executable, nullptr, nullptr, argv.data(), environ);
    if (launch != 0)
        throw std::system_error(launch, std::generic_category(), "could not start Spider (LUFT_SPIDER or PATH)");
    int status = 0;
    while (waitpid(pid, &status, 0) < 0) {
        if (errno != EINTR)
            throw std::system_error(errno, std::generic_category(), "could not wait for Spider");
    }
    const bool success = WIFEXITED(status) && WEXITSTATUS(status) == 0;
#endif
    if (!success)
        throw std::runtime_error("Spider could not translate the WebAssembly module");
}
}

void emitWasmLuau(const char* file) {
    constexpr std::array<char, 8> header{0, 'a', 's', 'm', 1, 0, 0, 0};
    std::array<char, header.size()> actual{};
    std::ifstream input(file, std::ios::binary);
    if (!input.read(actual.data(), actual.size()) || actual != header)
        throw std::runtime_error("expected a WebAssembly v1 module");

    const auto* executable = std::getenv("LUFT_SPIDER");
    if (!executable || !*executable)
        executable = "spider-cli";

    std::cout << "return function(imports)\n"
        "    local rt_import_map = {}\n"
        "    local rt_export_map = {}\n";
    runSpider(executable, {"compile", "--source", "web-assembly", "--target", "luau", "--", file});
    std::cout << "\n    if imports then\n"
        "        for name, instance in imports do\n"
        "            rt_import_map[name] = instance\n"
        "        end\n"
        "    end\n"
        "    module()\n"
        "    return rt_export_map\n"
        "end\n";
    if (!std::cout)
        throw std::runtime_error("could not write WebAssembly translation");
}
}
