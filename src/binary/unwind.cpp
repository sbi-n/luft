#include "unwind.h"

#include <array>
#include <cstdint>
#include <functional>
#include <map>
#include <optional>

namespace binary {
namespace {
// Reads DWARF exception-handling values (DW_EH_PE encodings) from the mapped image.
struct Cursor {
    Bytes image;
    std::size_t at;

    std::uint64_t take(unsigned size) {
        const auto value = read(image, at, size);
        at += size;
        return value;
    }

    std::uint64_t uleb() {
        std::uint64_t value = 0;
        for (unsigned shift = 0;; shift += 7) {
            const auto byte = take(1);
            if (shift < 64)
                value |= (byte & 0x7f) << shift;
            if (!(byte & 0x80))
                return value;
        }
    }

    std::int64_t sleb() {
        std::int64_t value = 0;
        unsigned shift = 0;
        for (;;) {
            const auto byte = take(1);
            if (shift < 64)
                value |= std::int64_t(byte & 0x7f) << shift;
            shift += 7;
            if (!(byte & 0x80)) {
                if (shift < 64 && (byte & 0x40))
                    value |= -(std::int64_t(1) << shift);
                return value;
            }
        }
    }

    std::uint64_t value(std::uint8_t encoding) {
        switch (encoding & 0x0f) {
        case 0x00: return take(8);
        case 0x01: return uleb();
        case 0x02: return take(2);
        case 0x03: return take(4);
        case 0x04: return take(8);
        case 0x09: return std::uint64_t(sleb());
        case 0x0a: return std::uint64_t(std::int64_t(std::int16_t(take(2))));
        case 0x0b: return std::uint64_t(std::int64_t(std::int32_t(take(4))));
        case 0x0c: return take(8);
        default: throw std::runtime_error("unsupported DWARF pointer encoding");
        }
    }

    // A pointer; zero stays null, as in libgcc and libunwind.
    std::optional<std::uint64_t> pointer(std::uint8_t encoding, std::uint64_t function = 0) {
        if (encoding == 0xff)
            return std::nullopt;
        const auto field = at;
        auto result = value(encoding);
        if (!result)
            return std::nullopt;
        switch (encoding & 0x70) {
        case 0x00: break;
        case 0x10: result += field; break;
        case 0x40: result += function; break;
        default: throw std::runtime_error("unsupported DWARF pointer base");
        }
        if (encoding & 0x80)
            result = read(image, result, 8);
        return result;
    }
};

void lsdaLandingPads(Bytes image, std::uint64_t lsda, std::uint64_t function, std::vector<LandingPad>& pads) {
    Cursor cursor{image, std::size_t(lsda)};
    const auto startEncoding = std::uint8_t(cursor.take(1));
    const auto start = startEncoding == 0xff ? function : cursor.pointer(startEncoding, function).value_or(0);
    if (const auto typeEncoding = cursor.take(1); typeEncoding != 0xff)
        cursor.uleb();
    const auto siteEncoding = std::uint8_t(cursor.take(1) & 0x0f);
    const auto length = cursor.uleb();
    const auto end = cursor.at + length;
    while (cursor.at < end) {
        const auto site = function + cursor.value(siteEncoding);
        const auto length = cursor.value(siteEncoding);
        const auto pad = cursor.value(siteEncoding);
        cursor.uleb();
        if (pad)
            pads.push_back({std::size_t(start + pad), std::size_t(site), std::size_t(site + length)});
    }
}

struct Cie {
    std::uint8_t pointerEncoding = 0;
    std::uint8_t lsdaEncoding = 0xff;
    bool augmented = false;
};

Cie readCie(Bytes image, std::size_t at) {
    Cursor cursor{image, at};
    const auto version = cursor.take(1);
    const auto augmentation = stringAt(image, cursor.at);
    cursor.at += augmentation.size() + 1;
    if (augmentation.find("eh") != std::string_view::npos)
        cursor.take(8);
    cursor.uleb();
    cursor.sleb();
    if (version == 1)
        cursor.take(1);
    else
        cursor.uleb();
    Cie cie;
    if (augmentation.empty() || augmentation[0] != 'z')
        return cie;
    cie.augmented = true;
    cursor.uleb();
    for (const auto ch : augmentation.substr(1)) {
        if (ch == 'L') {
            cie.lsdaEncoding = std::uint8_t(cursor.take(1));
        } else if (ch == 'R') {
            cie.pointerEncoding = std::uint8_t(cursor.take(1));
        } else if (ch == 'P') {
            const auto encoding = std::uint8_t(cursor.take(1));
            cursor.value(encoding);
        } else if (ch != 'S' && ch != 'B' && ch != 'G') {
            break;
        }
    }
    return cie;
}

// Whether `address` lies in a section of the kind; the headers mapped at `base` hold neither metadata nor code.
bool within(std::span<const GuestRegion> regions, std::size_t base, std::uint64_t address, bool executable) {
    return std::ranges::any_of(regions, [&](const GuestRegion& region) {
        return region.start != base && region.readable && region.executable == executable &&
            address >= region.start && address < region.end;
    });
}

// __CxxFrameHandler4 compresses most integers: the low bits of the first byte give the length.
std::uint32_t compressed(Bytes image, std::size_t& at) {
    static constexpr std::array<unsigned, 16> lengths{1, 2, 1, 3, 1, 2, 1, 4, 1, 2, 1, 3, 1, 2, 1, 5};
    static constexpr std::array<unsigned, 16> shifts{25, 18, 25, 11, 25, 18, 25, 4, 25, 18, 25, 11, 25, 18, 25, 0};
    const auto kind = read(image, at, 1) & 15;
    const auto length = lengths[kind];
    if (at + length < 4)
        throw std::runtime_error("invalid compressed integer");
    const auto value = std::uint32_t(read(image, at + length - 4, 4)) >> shifts[kind];
    at += length;
    return value;
}

// A function whose unwind information names a handler: its RVA range and where its handler data lies.
struct WindowsUser {
    std::size_t begin;
    std::size_t end;
    std::size_t data;
};

using Check = std::function<std::size_t(std::uint64_t, bool)>;
using Targets = std::vector<std::size_t>;

// FH4 FuncInfo4: catch funclets, continuations, and unwind actions.
void frameHandler4(Bytes image, const WindowsUser& user, const Check& check, Targets& out) {
    const auto info = check(read(image, user.data, 4), false);
    const auto header = read(image, info, 1);
    if (header & 0x80)
        throw std::runtime_error("invalid FH4 header");
    auto at = info + 1;
    if (header & 0x04)
        compressed(image, at);
    std::size_t unwindMap = 0, tryMap = 0;
    if (header & 0x08) {
        unwindMap = check(read(image, at, 4), false);
        at += 4;
    }
    if (header & 0x10) {
        tryMap = check(read(image, at, 4), false);
        at += 4;
    }
    if (!(header & 0x02))
        check(read(image, at, 4), false);
    if (tryMap) {
        at = tryMap;
        for (auto blocks = compressed(image, at); blocks--;) {
            compressed(image, at);
            compressed(image, at);
            compressed(image, at);
            auto handler = check(read(image, at, 4), false);
            at += 4;
            for (auto handlers = compressed(image, handler); handlers--;) {
                const auto flags = read(image, handler++, 1);
                if (flags & 1)
                    compressed(image, handler);
                if (flags & 2)
                    handler += 4;
                if (flags & 4)
                    compressed(image, handler);
                out.push_back(check(read(image, handler, 4), true));
                handler += 4;
                for (auto count = (flags >> 4) & 3; count--;) {
                    if (flags & 8) {
                        out.push_back(check(read(image, handler, 4), true));
                        handler += 4;
                    } else {
                        out.push_back(check(user.begin + compressed(image, handler), true));
                    }
                }
            }
        }
    }
    if (unwindMap) {
        at = unwindMap;
        for (auto entries = compressed(image, at); entries--;) {
            const auto type = compressed(image, at) & 3;
            if (!type)
                continue;
            out.push_back(check(read(image, at, 4), true));
            at += 4;
            if (type != 3)
                compressed(image, at);
        }
    }
}

// FH3 FuncInfo: catch funclets and unwind actions. FH3 funclets return their continuations, which the
// translator finds as code addresses.
void frameHandler3(Bytes image, const WindowsUser& user, const Check& check, Targets& out) {
    const auto info = check(read(image, user.data, 4), false);
    const auto magic = read(image, info, 4);
    if (magic < 0x19930520 || magic > 0x19930522)
        throw std::runtime_error("invalid FH3 magic");
    const auto states = read(image, info + 4, 4);
    const auto unwindMap = read(image, info + 8, 4);
    const auto blocks = read(image, info + 12, 4);
    const auto tryMap = read(image, info + 16, 4);
    for (std::uint64_t i = 0; i < states && unwindMap; ++i)
        if (const auto action = read(image, check(unwindMap, false) + i * 8 + 4, 4))
            out.push_back(check(action, true));
    for (std::uint64_t i = 0; i < blocks; ++i) {
        const auto block = check(tryMap, false) + i * 20;
        const auto catches = read(image, block + 12, 4);
        const auto handlers = read(image, block + 16, 4);
        for (std::uint64_t j = 0; j < catches; ++j)
            out.push_back(check(read(image, check(handlers, false) + j * 20 + 12, 4), true));
    }
}

// __C_specific_handler scope tables: {begin, end, filter or handler, target}.
void scopeTable(Bytes image, const WindowsUser& user, const Check& check, Targets& out) {
    const auto count = read(image, user.data, 4);
    if (!count || count > 256)
        throw std::runtime_error("invalid scope table");
    for (std::uint64_t i = 0; i < count; ++i) {
        const auto entry = user.data + 4 + i * 16;
        check(read(image, entry, 4), true);
        check(read(image, entry + 4, 4) - 1, true);
        if (const auto handler = read(image, entry + 8, 4); handler > 1)
            out.push_back(check(handler, true));
        if (const auto target = read(image, entry + 12, 4))
            out.push_back(check(target, true));
    }
}
}

// GCC's SEH personality (__gxx_personality_seh0): the handler data is an Itanium LSDA for the function.
void gccPersonality(Bytes image, const WindowsUser& user, const Check& check, Targets& out) {
    const auto function = check(user.begin, true);
    std::vector<LandingPad> pads;
    lsdaLandingPads(image, user.data, function, pads);
    for (const auto& pad : pads) {
        if (pad.target < function || pad.siteStart < function || pad.siteEnd > function + (user.end - user.begin))
            throw std::runtime_error("landing pad lies outside its function");
        out.push_back(check(pad.target - (function - user.begin), true));
    }
}

void windowsHandlerTargets(Bytes image, std::span<const GuestRegion> regions, std::size_t base, std::size_t table,
    std::size_t size, std::vector<LandingPad>& targets) {
    std::map<std::uint64_t, std::vector<WindowsUser>> users;
    for (std::size_t at = table; at + 12 <= table + size; at += 12) {
        const auto begin = read(image, at, 4);
        const auto info = base + read(image, at + 8, 4);
        if (!begin || info + 4 > image.size())
            continue;
        const auto flags = read(image, info, 1) >> 3;
        if (!(flags & 3) || (flags & 4))
            continue;
        const auto codes = read(image, info + 2, 1);
        const auto handler = info + 4 + ((codes + 1) & ~std::uint64_t(1)) * 2;
        if (handler + 8 > image.size())
            continue;
        const auto end = read(image, at + 4, 4);
        users[read(image, handler, 4)].push_back({std::size_t(begin), std::size_t(end), std::size_t(handler + 4)});
    }
    // Handler data holds RVAs.
    const Check check = [&](std::uint64_t rva, bool executable) {
        const auto address = base + rva;
        if (!within(regions, base, address, executable))
            throw std::runtime_error("handler data points outside its section");
        return std::size_t(address);
    };
    using Parser = void (*)(Bytes, const WindowsUser&, const Check&, Targets&);
    // Images carry no symbols, so a handler's kind is the format all of its functions' data parses as.
    static constexpr std::array<Parser, 4> parsers{frameHandler3, frameHandler4, scopeTable, gccPersonality};
    for (const auto& [handler, functions] : users) {
        // The dispatcher calls the handler itself.
        if (within(regions, base, base + handler, true))
            for (const auto& user : functions)
                targets.push_back({std::size_t(base + handler), base + user.begin, base + user.end});
        for (const auto parser : parsers) {
            std::vector<LandingPad> found;
            try {
                for (const auto& user : functions) {
                    Targets named;
                    parser(image, user, check, named);
                    for (const auto target : named)
                        found.push_back({target, base + user.begin, base + user.end});
                }
            } catch (const std::runtime_error&) {
                continue;
            }
            targets.insert(targets.end(), found.begin(), found.end());
            break;
        }
    }
}

void windowsThrowTargets(Bytes image, std::span<const GuestRegion> regions, std::size_t base,
    std::vector<LandingPad>& targets) {
    const auto code = [&](std::uint64_t rva) { return rva == 0 || within(regions, base, base + rva, true); };
    const auto data = [&](std::uint64_t rva) { return rva != 0 && within(regions, base, base + rva, false); };
    // A TypeDescriptor holds a vtable pointer and a spare word, then a decorated name such as ".?AVerror@@".
    const auto typeDescriptor = [&](std::uint64_t rva) {
        if (!data(rva) || base + rva + 20 > image.size() || image[base + rva + 16] != '.')
            return false;
        for (auto at = base + rva + 17; at < image.size() && at < base + rva + 512; ++at) {
            if (!image[at])
                return true;
            if (image[at] < 0x20 || image[at] >= 0x7f)
                return false;
        }
        return false;
    };
    for (const auto& region : regions) {
        if (region.start == base || !region.readable || region.writable || region.executable)
            continue;
        for (auto at = region.start; at + 16 <= region.end; at += 4) {
            // ThrowInfo: attributes, pmfnUnwind, pForwardCompat, and pCatchableTypeArray.
            const auto unwind = read(image, at + 4, 4);
            const auto array = read(image, at + 12, 4);
            if (read(image, at, 4) > 0x1f || !code(unwind) || !code(read(image, at + 8, 4)) || !data(array))
                continue;
            const auto count = read(image, base + array, 4);
            if (!count || count > 32 || base + array + 4 + count * 4 > image.size())
                continue;
            std::vector<std::size_t> found;
            bool valid = true;
            for (std::uint64_t i = 0; i < count && valid; ++i) {
                // CatchableType: properties, pType, thisDisplacement, sizeOrOffset, and copyFunction.
                const auto type = read(image, base + array + 4 + i * 4, 4);
                valid = data(type) && base + type + 28 <= image.size() && read(image, base + type, 4) <= 0xff &&
                    typeDescriptor(read(image, base + type + 4, 4)) && code(read(image, base + type + 24, 4));
                if (valid && read(image, base + type + 24, 4))
                    found.push_back(base + read(image, base + type + 24, 4));
            }
            if (!valid)
                continue;
            if (unwind)
                found.push_back(base + unwind);
            // Thrown objects may come from any code, so these are always reachable.
            for (const auto target : found)
                targets.push_back({target, 0, MaxExecutableSize});
        }
    }
}

void frameLandingPads(Bytes image, std::size_t frames, std::size_t size, std::vector<LandingPad>& pads) {
    std::map<std::size_t, Cie> cies;
    const auto end = std::min(frames + size, image.size());
    for (std::size_t at = frames; at + 4 <= end;) {
        std::uint64_t length = read(image, at, 4);
        auto start = at + 4;
        if (!length)
            break;
        if (length == 0xffffffff) {
            length = read(image, at + 4, 8);
            start = at + 12;
        }
        const auto next = start + length;
        if (length < 4 || next > end)
            break;
        const auto id = read(image, start, 4);
        try {
            if (id) {
                const auto cieAt = start - id;
                auto found = cies.find(cieAt);
                if (found == cies.end())
                    found = cies.emplace(cieAt, readCie(image, cieAt + (read(image, cieAt, 4) == 0xffffffff ? 16 : 8))).first;
                const auto& cie = found->second;
                Cursor cursor{image, start + 4};
                const auto function = cursor.pointer(cie.pointerEncoding);
                cursor.value(cie.pointerEncoding & 0x0f);
                if (cie.augmented && cie.lsdaEncoding != 0xff && function) {
                    cursor.uleb();
                    if (const auto lsda = cursor.pointer(cie.lsdaEncoding))
                        lsdaLandingPads(image, *lsda, *function, pads);
                }
            }
        } catch (const std::runtime_error&) {
            // An entry this reader does not understand cannot name landing pads it can use.
        }
        at = next;
    }
}

void compactLandingPads(Bytes image, std::size_t header, std::size_t info, std::size_t size,
    std::vector<LandingPad>& pads) {
    if (size < 28 || read(image, info, 4) != 1)
        return;
    const auto index = info + read(image, info + 20, 4);
    const auto count = read(image, info + 24, 4);
    if (!count)
        return;
    const auto first = read(image, index + 8, 4);
    const auto last = read(image, index + (count - 1) * 12 + 8, 4);
    for (auto entry = first; entry + 8 <= last && entry + 8 <= size; entry += 8) {
        const auto function = header + read(image, info + entry, 4);
        const auto lsda = header + read(image, info + entry + 4, 4);
        try {
            lsdaLandingPads(image, lsda, function, pads);
        } catch (const std::runtime_error&) {
        }
    }
}
}
