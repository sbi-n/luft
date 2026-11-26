#pragma once

#include "graph.h"

#include <array>

namespace ir {
std::optional<Address> jumpTarget(const Block& block);
using Constants = std::array<std::optional<std::uint64_t>, RegisterCount>;

void visitEdges(const Block& block, const auto& visit) {
    if (const auto target = jumpTarget(block)) {
        visit(*target);
    } else if (const auto* jump = std::get_if<Jump>(&block.end)) {
        for (const auto destination : jump->destinations)
            visit(destination);
    } else if (const auto* branch = std::get_if<Branch>(&block.end)) {
        visit(branch->taken);
        visit(branch->other);
    }
}

// Control flow edges within guest code, including where each call resumes.
void visitSuccessors(const Block& block, const auto& visit) {
    visitEdges(block, visit);
    if (const auto* call = std::get_if<Call>(&block.end))
        visit(call->resume);
}

using LoopExits = std::map<Address, std::vector<Address>>;

struct Features {
    bool stack = false;
    bool calls = false;
    bool flags = false;
    bool parity = false;
};

// Natural loops of at most `maxBlocks` blocks with one entry and at most four exits, by header, with their blocks
// in `bodies`. A loop whose header is one of `entries`, such as a function that starts with its loop, is entered
// there by calls. Loops nested in larger or irreducible cycles are found too.
LoopExits recoverLoops(const Graph& graph, const std::set<Address>& entries = {},
    std::map<Address, std::set<Address>>* bodies = nullptr, std::size_t maxBlocks = 16);
// Each block's immediate post-dominator within its function: the nearest block that every path from the block to
// the function's exit (a return, a tail jump to one of `entries`, or control flow that leaves the graph) passes
// through. Calls continue at their resume address; paths that only end in traps are ignored. Blocks whose paths
// meet only at the exit, or that never reach it, are absent.
std::map<Address, Address> postDominators(const Graph& graph, const std::set<Address>& entries);
bool readsFlags(const Effect& effect);
// Whether the effect may change a general-purpose register (conservatively true for unknown cases).
bool writesRegister(const Effect& effect, unsigned reg);
bool writesFlags(const Effect& effect);
bool overwritesFlags(const Effect& effect);
bool observesExitFlags(const Block& block, bool calls);
std::set<Address> liveFlagsAtEntry(const Graph& graph, bool calls);
std::optional<std::uint64_t> knownAddress(const EffectiveAddress& address, const Constants& constants);
std::uint64_t fold(BinaryOp op, std::uint64_t lhs, std::uint64_t rhs);
Features detectFeatures(const Graph& graph, Address entry, bool arm,
    std::span<const std::size_t> initializers);
}
