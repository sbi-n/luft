#pragma once

#include "graph.h"

#include <array>

namespace ir {
std::optional<Address> jumpTarget(const Block& block);
using Constants = std::array<std::optional<std::uint64_t>, 33>;

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

using LoopExits = std::map<Address, std::vector<Address>>;

struct Features {
    bool stack = false;
    bool calls = false;
    bool flags = false;
    bool parity = false;
};

LoopExits recoverLoops(const Graph& graph);
bool readsFlags(const Block& block);
bool readsFlags(const Effect& effect);
bool writesFlags(const Effect& effect);
std::set<Address> liveFlagsAtEntry(const Graph& graph);
std::optional<std::uint64_t> knownAddress(const EffectiveAddress& address, const Constants& constants);
std::uint64_t fold(BinaryOp op, std::uint64_t lhs, std::uint64_t rhs);
Features detectFeatures(const Graph& graph, Address entry, bool arm,
    std::span<const std::size_t> initializers);
}
