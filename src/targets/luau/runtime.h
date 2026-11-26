#pragma once

#include "ir/graph.h"

#include <set>

namespace luau {
struct RuntimeFeatures {
    bool flags = false;
    bool shifts = false;
    bool division = false;
    bool multiply = false;
    bool jumpFrames = false;
    bool memory = false;
    bool stackGuard = false;
    bool heap = false;
    bool floating = false;
    bool prime = false;
    bool structured = false;
    bool decimal = false;
    bool vector = false;
    bool process = false;
    bool x87 = false;
    // Windows structured exception dispatch and unwinding.
    bool seh = false;
    // Indirect jumps that resume landing pads.
    bool landingPads = false;
    // The guest's architecture, which C library structures such as struct stat lay out differently.
    bool arm = false;
    // A Windows guest, whose C library (msvcrt) lays out structures such as struct tm its own way.
    bool windows = false;
};

// Calls through a pointer to an import reach it through this value plus the import slot's address.
inline constexpr std::uint64_t ImportTokenBase = 0xf0000000ull;

struct Data {
    std::span<const std::uint8_t> image;
    std::span<const GuestRegion> regions;
    std::span<const GuestImport> imports;
    std::span<const ir::CodeRange> code;
    std::span<const GuestObject> objects;
    // Materialized byte ranges, start to end, kept disjoint and merged.
    std::map<std::size_t, std::size_t> emitted;
    // Code that exception unwinders transfer control to.
    std::set<std::size_t> landingPads = {};
    std::span<const UnwindObject> unwindObjects = {};
    // Import slots whose memory holds the import's token, for code that reads them at run time.
    std::map<std::size_t, const GuestImport*> tokenSlots = {};

    const GuestImport* unresolved(std::uint64_t at, unsigned size) const;
    bool writable(std::uint64_t at, unsigned size) const;
    bool readable(std::uint64_t at, unsigned size) const;
    std::optional<std::uint64_t> immutableWord(std::uint64_t at, unsigned size) const;
    void materialize(std::size_t at, unsigned size);
    bool materializeObject(std::uint64_t at);
    void materializeIndexed(std::uint64_t at);
    void materializeAddress(std::uint64_t at);
    // Every readable data region except unresolved import slots.
    void materializeAll();
    bool materialized(std::uint64_t at) const;
    std::string source() const;
};

std::string quoted(std::string_view value);
void appendRuntime(std::string& source, const RuntimeFeatures& features, const Data& data);
}
