#pragma once

#include "recompiler.h"

#include <algorithm>
#include <stdexcept>
#include <vector>

namespace binary {
using Bytes = std::span<const std::uint8_t>;

inline Bytes slice(Bytes image, std::uint64_t start, std::uint64_t size) {
    if (start > image.size() || size > image.size() - start)
        throw std::runtime_error("binary field lies outside its image");
    return image.subspan(start, size);
}

inline std::uint64_t read(Bytes image, std::uint64_t start, unsigned size) {
    std::uint64_t value = 0;
    unsigned shift = 0;
    for (auto byte : slice(image, start, size)) {
        value |= std::uint64_t(byte) << shift;
        shift += 8;
    }
    return value;
}

inline std::string_view stringAt(Bytes image, std::uint64_t start) {
    const auto rest = slice(image, start, start <= image.size() ? image.size() - start : 0);
    const auto end = std::ranges::find(rest, 0);
    if (end == rest.end())
        throw std::runtime_error("binary string is not terminated");
    return {reinterpret_cast<const char*>(rest.data()), std::size_t(end - rest.begin())};
}

struct Image {
    std::vector<std::uint8_t> bytes;
    std::vector<GuestRegion> regions;

    void add(std::uint64_t start, std::uint64_t size, Bytes data, bool r, bool w, bool x, bool protectable = false) {
        if (start > MaxExecutableSize || size > MaxExecutableSize - start || data.size() > size || (w && x))
            throw std::runtime_error("unsupported binary section layout");
        if (!size)
            return;
        const auto end = start + size;
        for (const auto& region : regions)
            if (start < region.end && end > region.start)
                throw std::runtime_error("binary sections overlap");
        if (end > bytes.size())
            bytes.resize(end);
        std::ranges::copy(data, bytes.begin() + start);
        regions.push_back({std::size_t(start), std::size_t(end), r, w, x, protectable});
    }

    void relocate(std::uint64_t at, std::uint64_t value) {
        if (at > bytes.size() || 8 > bytes.size() - at)
            throw std::runtime_error("binary relocation lies outside its image");
        for (unsigned i = 0; i < 8; ++i)
            bytes[at + i] = std::uint8_t(value >> (8 * i));
    }
};
}
