#include "runtime.h"

#include <algorithm>
#include <format>
#include <initializer_list>
#include <span>

namespace luau {
namespace {
// MSVC rejects a string literal longer than 16380 bytes (C2026), so each Luau source below is an array of raw
// literals that concatenate to it. Split one that grows too long at a line break.
constexpr std::size_t LiteralLimit = 16380;

void appendChunks(std::string& out, std::span<const std::string_view> chunks) {
    for (const auto chunk : chunks)
        out += chunk;
}

void appendQuoted(std::string& out, std::span<const std::uint8_t> bytes) {
    constexpr std::string_view hex = "0123456789abcdef";
    out += '"';
    for (const auto byte : bytes) {
        if (byte >= 32 && byte <= 126 && byte != '"' && byte != '\\') {
            out += char(byte);
        } else {
            out += "\\x";
            out += hex[byte >> 4];
            out += hex[byte & 15];
        }
    }
    out += '"';
}

constexpr std::string_view ArgumentReader[] = {R"(
local function readArguments(maximum: number, ...: Word): {Word}
    local count = select("#", ...)
    if count > maximum then
        error("too many guest register arguments", 0)
    end
    local args: {Word} = {}
    for index = 1, count do
        local value = select(index, ...)
        if type(value) ~= "table" then
            error("expected {lo, hi} at guest argument " .. index, 0)
        end
        local lo, hi = rawget(value, "lo"), rawget(value, "hi")
        if type(lo) ~= "number" or type(hi) ~= "number" or
            lo < 0 or lo >= 4294967296 or lo % 1 ~= 0 or
            hi < 0 or hi >= 4294967296 or hi % 1 ~= 0 then
            error("expected two unsigned 32-bit values at guest argument " .. index, 0)
        end
        args[index] = {lo = lo, hi = hi}
    end
    return args
end
)"};

constexpr std::string_view FlagOperators[] = {R"(
local function evenParity(value: number): boolean
    return bit32.extract(0x9669, bit32.band(bit32.bxor(value, bit32.rshift(value, 4)), 15)) == 1
end

local function addFlags(subtract: boolean, arm: boolean, size: number,
    alo: number, ahi: number, blo: number, bhi: number, carryIn: boolean?): (number, number, boolean, boolean, boolean, boolean)
    local sign = if subtract then -1 else 1
    local sum = alo + sign * (blo + (if carryIn then 1 else 0))
    if size <= 2 then
        local modulus = if size == 1 then 256 else 65536
        local half = modulus // 2
        local lo = sum % modulus
        local negative = lo >= half
        local carry = if subtract then sum < 0 else sum >= modulus
        return lo, 0, carry, ((alo >= half) ~= (blo >= half)) == subtract and negative ~= (alo >= half), negative, lo == 0
    end
    local upper = ahi + sign * bhi + math.floor(sum / 4294967296)
    local lo = sum % 4294967296
    local hi = if size == 8 then upper % 4294967296 else 0
    local negative = (if size == 8 then hi else lo) >= 2147483648
    local a = (if size == 8 then ahi else alo) >= 2147483648
    local b = (if size == 8 then bhi else blo) >= 2147483648
    local total = if size == 8 then upper else sum
    local carry = if subtract then (total < 0) ~= arm else total >= 4294967296
    return lo, hi, carry, (a ~= b) == subtract and negative ~= a, negative, lo == 0 and hi == 0
end
)"};

constexpr std::string_view RoutineOperators[] = {R"(
-- A routine returns nil when its guest function returns, or the next routine to run. When control leaves
-- for a frame other than the caller's, as exception unwinders and longjmp-like code do, it returns the
-- address that frame resumes at and sets unwindStack to the stack pointer there. The calls in between
-- return the address too, until the call whose frame has that stack pointer resumes at it.
type GuestRoutine = (number) -> any

local unwindStack = -1
-- Routines for code that frames resume at, by guest address.
local resumeRoutines: {[number]: any} = {}

local function checkUnwound(address: any)
    if address ~= nil then
        error(if type(address) == "number" then string.format("guest returned to unknown address 0x%x", address)
            else "guest resumed a frame outside translated calls", 0)
    end
end

-- `frameStack` is the calling frame's stack pointer once the call returns. Calls without one, from emulated
-- library code, are never resumed.
local function runGuestRoutine(action: GuestRoutine, expectedReturn: number, frameStack: number?): any
    local nextAction: any = action
    -- run() sets the yield callback before the guest starts. Creating a guest thread replaces it with one that
    -- returns a guest thread's turn to the main thread, which yields to the host.
    local yield = process.yield
    while true do
        if yield then
            process.yieldSteps += 1
            if process.yieldSteps >= 1024 then
                process.yieldSteps = 0
                if os.clock() - process.yieldAt >= process.yieldInterval then
                    yield()
                    process.yieldAt = os.clock()
                end
            end
        end
        local result = nextAction(expectedReturn)
        if result == nil then
            return nil
        elseif type(result) == "number" then
            if frameStack == nil then
                return if result == expectedReturn then nil else result
            elseif unwindStack ~= frameStack then
                return result
            elseif result == expectedReturn then
                return nil
            end
            -- The caller resumes inside its own function: it continues with that routine.
            local resume = resumeRoutines[result]
            if resume == nil then
                error(string.format("guest resumed its frame at 0x%x, which has no translated code", result), 0)
            end
            return resume
        end
        nextAction = result
    end
end
)"};

constexpr std::string_view ShiftOperators[] = {R"(
local function reverseBits(word: number): number
    word = bit32.bor(bit32.lshift(bit32.band(word, 0x55555555), 1), bit32.band(bit32.rshift(word, 1), 0x55555555))
    word = bit32.bor(bit32.lshift(bit32.band(word, 0x33333333), 2), bit32.band(bit32.rshift(word, 2), 0x33333333))
    word = bit32.bor(bit32.lshift(bit32.band(word, 0x0f0f0f0f), 4), bit32.band(bit32.rshift(word, 4), 0x0f0f0f0f))
    return bit32.byteswap(word)
end

local function shiftParts(op: number, size: number, count: number, lo: number, hi: number):
    (number, number, number)
    if op >= 3 then
        local left = op == 4
        if left then count = (size * 8 - count) % (size * 8) end
        if size == 4 then
            local result = bit32.rrotate(lo, count)
            return result, 0, bit32.extract(result, if left then 0 else 31)
        end
        if count >= 32 then
            lo, hi = hi, lo
            count -= 32
        end
        if count == 0 then
            return lo, hi, if left then bit32.extract(lo, 0) else bit32.extract(hi, 31)
        end
        local low = bit32.bor(bit32.rshift(lo, count), bit32.lshift(hi, 32 - count))
        local high = bit32.bor(bit32.rshift(hi, count), bit32.lshift(lo, 32 - count))
        return low, high, if left then bit32.extract(low, 0) else bit32.extract(high, 31)
    end
    if op == 0 then
        if size == 4 then
            return bit32.lshift(lo, count), 0, bit32.extract(lo, 32 - count)
        elseif count < 32 then
            return bit32.lshift(lo, count),
                bit32.bor(bit32.lshift(hi, count), bit32.rshift(lo, 32 - count)),
                bit32.extract(hi, 32 - count)
        else
            return 0, bit32.lshift(lo, count - 32),
                if count == 32 then bit32.band(hi, 1) else bit32.extract(lo, 64 - count)
        end
    end
    -- bit32 calls stay direct (not through a local chosen at run time) so that Luau compiles them to fast calls,
    -- and an inlined call with a constant op keeps only one of them.
    if size == 4 then
        return if op == 2 then bit32.arshift(lo, count) else bit32.rshift(lo, count), 0, bit32.extract(lo, count - 1)
    elseif count < 32 then
        return bit32.bor(bit32.rshift(lo, count), bit32.lshift(hi, 32 - count)),
            if op == 2 then bit32.arshift(hi, count) else bit32.rshift(hi, count), bit32.extract(lo, count - 1)
    end
    return if op == 2 then bit32.arshift(hi, count - 32) else bit32.rshift(hi, count - 32),
        if op == 2 and hi >= 2147483648 then 4294967295 else 0,
        if count == 32 then bit32.extract(lo, 31) else bit32.extract(hi, count - 33)
end

local function rotateWord(op: number, size: number, count: number, lo: number, hi: number):
    (number, number, boolean, boolean)
    local low, high, out = shiftParts(op, size, count, lo, hi)
    local upper = if size == 8 then high else low
    local other = if op == 4 then out else bit32.extract(upper, 30)
    return low, high, out == 1, count == 1 and bit32.extract(upper, 31) ~= other
end

local function shiftWord(op: number, size: number, count: number, lo: number, hi: number):
    (number, number, boolean, boolean, boolean, boolean)
    local low, high, shiftedOut = shiftParts(op, size, count, lo, hi)
    local sign = (if size == 8 then hi else lo) >= 2147483648
    local negative = (if size == 8 then high else low) >= 2147483648
    local carry = shiftedOut == 1
    local overflow = count == 1 and (if op == 0 then negative ~= carry else op == 1 and sign)
    return low, high, carry, overflow, negative, low == 0 and high == 0
end

local function bitfieldWord(size: number, start: number, width: number, position: number, signed: boolean,
    lo: number, hi: number): (number, number)
    if start ~= 0 then
        lo, hi = shiftParts(1, size, start, lo, hi)
    end
    if width <= 32 then
        local bound = 2 ^ width
        lo %= bound
        if signed and lo >= bound / 2 then
            lo += 4294967296 - bound
            hi = 4294967295
        else
            hi = 0
        end
    else
        local bound = 2 ^ (width - 32)
        hi %= bound
        if signed and hi >= bound / 2 then
            hi += 4294967296 - bound
        end
    end
    if position ~= 0 then
        lo, hi = shiftParts(0, size, position, lo, hi)
    end
    return lo, if size == 8 then hi else 0
end

local function doubleShift(left: boolean, size: number, count: number, dlo: number, dhi: number,
    slo: number, shi: number): (number, number)
    count %= if size == 8 then 64 else 32
    if count == 0 then return dlo, if size == 8 then dhi else 0 end
    local alo, ahi = shiftParts(if left then 0 else 1, size, count, dlo, dhi)
    local blo, bhi = shiftParts(if left then 1 else 0, size, size * 8 - count, slo, shi)
    return bit32.bor(alo, blo), if size == 8 then bit32.bor(ahi, bhi) else 0
end

local function shiftRegister(op: number, size: number, count: number, lo: number, hi: number): (number, number)
    count %= size * 8
    if count == 0 then return lo, if size == 8 then hi else 0 end
    local low, high = shiftParts(op, size, count, lo, hi)
    return low, high
end

local function populationByByte(value: number): number
    value -= bit32.band(bit32.rshift(value, 1), 0x55555555)
    value = bit32.band(value, 0x33333333) + bit32.band(bit32.rshift(value, 2), 0x33333333)
    return bit32.band(value + bit32.rshift(value, 4), 0x0f0f0f0f)
end

local function sumBytes(value: number): number
    return bit32.extract(value, 0, 8) + bit32.extract(value, 8, 8)
        + bit32.extract(value, 16, 8) + bit32.extract(value, 24, 8)
end
)"};

constexpr std::string_view FloatingOperators[] = {R"(
local floatScratch = buffer.create(8)
local function decodeFloat(size: number, lo: number, hi: number): number
    buffer.writeu32(floatScratch, 0, lo)
    if size == 4 then
        return buffer.readf32(floatScratch, 0)
    end
    buffer.writeu32(floatScratch, 4, hi)
    return buffer.readf64(floatScratch, 0)
end

local function encodeFloat(size: number, value: number): (number, number)
    if size == 4 then
        buffer.writef32(floatScratch, 0, value)
        return buffer.readu32(floatScratch, 0), 0
    end
    buffer.writef64(floatScratch, 0, value)
    return buffer.readu32(floatScratch, 0), buffer.readu32(floatScratch, 4)
end

local function integerAsFloat(size: number, floatSize: number, signed: boolean, lo: number, hi: number): number
    if size == 4 then
        return lo - (if signed and lo >= 2147483648 then 4294967296 else 0)
    end
    local negative = signed and hi >= 2147483648
    if floatSize == 8 then
        return (hi - (if negative then 4294967296 else 0)) * 4294967296 + lo
    end
    if negative then
        lo, hi = (-lo) % 4294967296, (-hi - (if lo == 0 then 0 else 1)) % 4294967296
    end
    -- Round the two limbs directly to 24 significant bits, avoiding double rounding.
    local shift = 40 - bit32.countlz(hi)
    if hi == 0 then
        return if negative then -lo else lo
    end
    local unit = 2 ^ shift
    local q, tail, halfway, extra
    if shift <= 32 then
        q = hi * (4294967296 / unit) + math.floor(lo / unit)
        tail, halfway, extra = lo % unit, unit / 2, false
    else
        local hiUnit = unit / 4294967296
        q = math.floor(hi / hiUnit)
        tail, halfway, extra = hi % hiUnit, hiUnit / 2, lo ~= 0
    end
    if tail > halfway or (tail == halfway and (extra or q % 2 ~= 0)) then
        q += 1
    end
    return if negative then -(q * unit) else q * unit
end

local function truncateFloat(size: number, arm: boolean, signed: boolean, value: number): (number, number)
    local limit = 2 ^ (size * 8 - (if signed then 1 else 0))
    if arm then
        if value ~= value or (not signed and value <= 0) then return 0, 0 end
        if value >= limit then
            local max = if signed then 2147483647 else 4294967295
            if size == 4 then return max, 0 end
            return 4294967295, max
        end
        if signed and value <= -limit then
            if size == 4 then return 2147483648, 0 end
            return 0, 2147483648
        end
    elseif value ~= value or value >= limit or value <= -limit - 1 then
        if size == 4 then return 2147483648, 0 end
        return 0, 2147483648
    end
    local n = if value < 0 then math.ceil(value) else math.floor(value)
    return n % 4294967296, if size == 8 then math.floor(n / 4294967296) % 4294967296 else 0
end
)"};

// Vector lanes are four little-endian 32-bit words. Element access goes through scratch buffers.
constexpr std::string_view VectorOperators[] = {R"(
local laneA, laneB, laneR = buffer.create(16), buffer.create(16), buffer.create(16)

-- TBL and TBX: each byte of the index lanes selects a byte of the table, `limit` bytes of lanes t0 onward. An
-- index past the table keeps the byte of the `kept` lanes, which are zero for TBL.
local vectorTable: (limit: number, size: number, i0: number, i1: number, i2: number, i3: number, k0: number,
    k1: number, k2: number, k3: number, ...number) -> (number, number, number, number)
do
    local bytes = buffer.create(64)
    local function lane(limit: number, indices: number, kept: number): number
        local result = 0
        for shift = 0, 24, 8 do
            local index = bit32.extract(indices, shift, 8)
            local byte = if index < limit then buffer.readu8(bytes, index) else bit32.extract(kept, shift, 8)
            result = bit32.replace(result, byte, shift, 8)
        end
        return result
    end
    vectorTable = function(limit, size, i0, i1, i2, i3, k0, k1, k2, k3, ...)
        for word = 1, limit // 4 do
            buffer.writeu32(bytes, (word - 1) * 4, (select(word, ...)))
        end
        if size == 8 then
            return lane(limit, i0, k0), lane(limit, i1, k1), 0, 0
        end
        return lane(limit, i0, k0), lane(limit, i1, k1), lane(limit, i2, k2), lane(limit, i3, k3)
    end
end

local function storeLanes(target: buffer, a: number, b: number, c: number, d: number)
    buffer.writeu32(target, 0, a)
    buffer.writeu32(target, 4, b)
    buffer.writeu32(target, 8, c)
    buffer.writeu32(target, 12, d)
end

local function loadLanes(source: buffer, size: number): (number, number, number, number)
    if size == 8 then
        return buffer.readu32(source, 0), buffer.readu32(source, 4), 0, 0
    end
    return buffer.readu32(source, 0), buffer.readu32(source, 4), buffer.readu32(source, 8), buffer.readu32(source, 12)
end

local function readLane(source: buffer, at: number, element: number, signed: boolean): number
    if element == 1 then
        return if signed then buffer.readi8(source, at) else buffer.readu8(source, at)
    elseif element == 2 then
        return if signed then buffer.readi16(source, at) else buffer.readu16(source, at)
    end
    return if signed then buffer.readi32(source, at) else buffer.readu32(source, at)
end

local function writeLane(target: buffer, at: number, element: number, value: number)
    if element == 1 then
        buffer.writeu8(target, at, value % 256)
    elseif element == 2 then
        buffer.writeu16(target, at, value % 65536)
    else
        buffer.writeu32(target, at, value % 4294967296)
    end
end

local function multiplyLow32(a: number, b: number): number
    local al, ah = a % 65536, math.floor(a / 65536)
    return ((ah * (b % 65536) + al * math.floor(b / 65536)) % 65536 * 65536 + al * (b % 65536)) % 4294967296
end

-- LaneOp order matches the IR enumeration.
local signedLaneOps = {[4] = true, [5] = true, [8] = true, [9] = true, [13] = true, [15] = true, [18] = true}

local function wideLanes(op: number, alo: number, ahi: number, blo: number, bhi: number): (number, number)
    if op == 24 then
        local set = bit32.band(alo, blo) ~= 0 or bit32.band(ahi, bhi) ~= 0
        return if set then 4294967295 else 0, if set then 4294967295 else 0
    elseif op == 25 or op == 26 then
        local count = bit32.band(blo, 255)
        if count >= 128 then count -= 256 end
        if count >= 64 then return 0, 0 end
        if count >= 0 then
            if count >= 32 then return 0, bit32.lshift(alo, count - 32) end
            if count == 0 then return alo, ahi end
            return bit32.lshift(alo, count), bit32.bor(bit32.lshift(ahi, count), bit32.rshift(alo, 32 - count))
        end
        count = -count
        local fill = if op == 26 and ahi >= 2147483648 then 4294967295 else 0
        if count >= 64 then return fill, fill end
        if count >= 32 then
            return if op == 26 then bit32.arshift(ahi, count - 32) else bit32.rshift(ahi, count - 32), fill
        end
        return bit32.bor(bit32.rshift(alo, count), bit32.lshift(ahi, 32 - count)),
            if op == 26 then bit32.arshift(ahi, count) else bit32.rshift(ahi, count)
    elseif op == 0 or op == 1 then
        local sum = if op == 0 then alo + blo else alo - blo
        local high = if op == 0 then ahi + bhi else ahi - bhi
        return sum % 4294967296, (high + math.floor(sum / 4294967296)) % 4294967296
    elseif op == 20 or op == 27 then
        local al, ah = alo % 65536, math.floor(alo / 65536)
        local bl, bh = blo % 65536, math.floor(blo / 65536)
        local cross = al * bh + ah * bl
        local lower = al * bl + cross % 65536 * 65536
        local upper = ah * bh + math.floor(cross / 65536) + math.floor(lower / 4294967296)
        if op == 27 then
            -- A negative factor is its unsigned value less 2^32: the product loses the other factor times 2^32.
            if alo >= 2147483648 then upper -= blo end
            if blo >= 2147483648 then upper -= alo end
        end
        return lower % 4294967296, upper % 4294967296
    end
    local sa, sb = ahi, bhi
    if signedLaneOps[op] then
        sa = if ahi >= 2147483648 then ahi - 4294967296 else ahi
        sb = if bhi >= 2147483648 then bhi - 4294967296 else bhi
    end
    local greater = sa > sb or (sa == sb and alo > blo)
    local equal = sa == sb and alo == blo
    local result
    if op == 3 then result = equal
    elseif op == 4 or op == 6 then result = greater
    elseif op == 5 or op == 7 then result = greater or equal
    elseif op == 8 or op == 10 then return if greater then blo else alo, if greater then bhi else ahi
    elseif op == 9 or op == 11 then return if greater then alo else blo, if greater then ahi else bhi
    else error("unsupported 64-bit vector lane operation " .. op, 0) end
    return if result then 4294967295 else 0, if result then 4294967295 else 0
end

local function laneOperation(op: number, element: number, size: number, a0: number, a1: number, a2: number, a3: number,
    b0: number, b1: number, b2: number, b3: number): (number, number, number, number)
    if op >= 28 and op <= 32 then
        -- Pairwise: lane i combines lanes 2i and 2i + 1 of the first operand followed by the second.
        if element == 8 then
            local r0, r1 = wideLanes(0, a0, a1, a2, a3)
            local r2, r3 = wideLanes(0, b0, b1, b2, b3)
            return r0, r1, r2, r3
        end
        storeLanes(laneA, a0, a1, a2, a3)
        storeLanes(laneB, b0, b1, b2, b3)
        local half, signed = size / 2, op == 29 or op == 31
        for at = 0, size - element, element do
            local source, from = if at < half then laneA else laneB, (at % half) * 2
            local x, y = readLane(source, from, element, signed), readLane(source, from + element, element, signed)
            writeLane(laneR, at, element, if op == 28 then x + y elseif op <= 30 then math.max(x, y) else math.min(x, y))
        end
        return loadLanes(laneR, size)
    end
    if element == 8 then
        local r0, r1 = wideLanes(op, a0, a1, b0, b1)
        if size == 8 then return r0, r1, 0, 0 end
        local r2, r3 = wideLanes(op, a2, a3, b2, b3)
        return r0, r1, r2, r3
    end
    storeLanes(laneA, a0, a1, a2, a3)
    storeLanes(laneB, b0, b1, b2, b3)
    if op == 23 then
        for i = 0, 15 do
            local control = buffer.readu8(laneB, i)
            buffer.writeu8(laneR, i, if control >= 128 then 0 else buffer.readu8(laneA, control % 16))
        end
        return loadLanes(laneR, 16)
    end
    if op == 21 or op == 22 then
        local target = element / 2
        local bits = target * 8
        local low = if op == 21 then -2 ^ (bits - 1) else 0
        local high = if op == 21 then 2 ^ (bits - 1) - 1 else 2 ^ bits - 1
        local count = 16 / element
        for i = 0, count - 1 do
            writeLane(laneR, i * target, target, math.clamp(readLane(laneA, i * element, element, true), low, high))
            writeLane(laneR, (count + i) * target, target, math.clamp(readLane(laneB, i * element, element, true), low, high))
        end
        return loadLanes(laneR, 16)
    end
    local signed = signedLaneOps[op] == true
    local bits = element * 8
    local mask = 2 ^ bits - 1
    local low, high = if signed then -2 ^ (bits - 1) else 0, if signed then 2 ^ (bits - 1) - 1 else mask
    for at = 0, size - element, element do
        local x, y = readLane(laneA, at, element, signed), readLane(laneB, at, element, signed)
        local r
        if op == 0 then r = x + y
        elseif op == 1 then r = x - y
        elseif op == 2 then r = if element == 4 then multiplyLow32(x % 4294967296, y % 4294967296) else x * y
        elseif op == 3 then r = if x == y then mask else 0
        elseif op == 4 or op == 6 then r = if x > y then mask else 0
        elseif op == 5 or op == 7 then r = if x >= y then mask else 0
        elseif op == 8 or op == 10 then r = math.min(x, y)
        elseif op == 9 or op == 11 then r = math.max(x, y)
        elseif op == 12 or op == 13 then r = math.clamp(x + y, low, high)
        elseif op == 14 or op == 15 then r = math.clamp(x - y, low, high)
        elseif op == 16 then r = math.floor((x + y + 1) / 2)
        elseif op == 17 or op == 18 then r = math.floor(x * y / 2 ^ bits)
        elseif op == 19 then r = math.abs(x - y)
        elseif op == 24 then r = if bit32.band(x % 4294967296, y % 4294967296) ~= 0 then mask else 0
        elseif op == 25 or op == 26 then
            local count = readLane(laneB, at, 1, true)
            if op == 26 then x = readLane(laneA, at, element, true) end
            if count >= 0 then
                r = if count >= bits then 0 else x * 2 ^ count
            else
                r = if -count >= bits then (if x < 0 then -1 else 0) else math.floor(x / 2 ^ -count)
            end
        else error("unsupported vector lane operation " .. op, 0) end
        writeLane(laneR, at, element, r)
    end
    return loadLanes(laneR, size)
end

local function readFloatLane(source: buffer, at: number, element: number): number
    return if element == 4 then buffer.readf32(source, at) else buffer.readf64(source, at)
end

local function writeFloatLane(target: buffer, at: number, element: number, value: number)
    if element == 4 then buffer.writef32(target, at, value) else buffer.writef64(target, at, value) end
end

local function writeMaskLane(target: buffer, at: number, element: number, set: boolean)
    local word = if set then 4294967295 else 0
    buffer.writeu32(target, at, word)
    if element == 8 then buffer.writeu32(target, at + 4, word) end
end
)", R"(
local function vectorFloatLanes(op: number, element: number, size: number, a0: number, a1: number, a2: number, a3: number,
    b0: number, b1: number, b2: number, b3: number): (number, number, number, number)
    storeLanes(laneA, a0, a1, a2, a3)
    storeLanes(laneB, b0, b1, b2, b3)
    for at = 0, size - element, element do
        if op == 17 or op == 18 then
            -- Sign-bit operations keep NaN payloads intact.
            local top = at + element - 4
            for i = at, at + element - 4, 4 do buffer.writeu32(laneR, i, buffer.readu32(laneB, i)) end
            local word = buffer.readu32(laneB, top)
            buffer.writeu32(laneR, top, if op == 17 then bit32.bxor(word, 0x80000000) else bit32.band(word, 0x7fffffff))
            continue
        end
        local x, y = readFloatLane(laneA, at, element), readFloatLane(laneB, at, element)
        local unordered = x ~= x or y ~= y
        if op <= 3 then
            writeFloatLane(laneR, at, element, if op == 0 then x + y elseif op == 1 then x - y elseif op == 2 then x * y else x / y)
        elseif op == 4 or op == 5 then
            -- SSE MIN/MAX return the second operand when either input is NaN or both are zero.
            writeFloatLane(laneR, at, element, if (if op == 4 then x < y else x > y) then x else y)
        elseif op == 6 then
            writeFloatLane(laneR, at, element, math.sqrt(y))
        elseif op >= 7 and op <= 16 then
            local set
            if op == 7 then set = x == y
            elseif op == 8 then set = x < y
            elseif op == 9 then set = x <= y
            elseif op == 10 then set = unordered
            elseif op == 11 then set = not (x == y)
            elseif op == 12 then set = not (x < y)
            elseif op == 13 then set = not (x <= y)
            elseif op == 14 then set = not unordered
            elseif op == 15 then set = x > y
            else set = x >= y end
            writeMaskLane(laneR, at, element, set)
        elseif op >= 23 then
            -- Rounding to an integer keeps the sign of zero, NaN, and infinity.
            local result
            if y ~= y or y == math.huge or y == -math.huge then
                result = y
            elseif op == 25 then
                result = math.floor(y)
            elseif op == 26 then
                result = math.ceil(y)
            elseif op == 27 then
                result = if y >= 0 then math.floor(y) else math.ceil(y)
            else
                local magnitude = math.abs(y)
                local whole = math.floor(magnitude)
                local fraction = magnitude - whole
                if fraction > 0.5 or (fraction == 0.5 and (op == 24 or whole % 2 == 1)) then whole += 1 end
                result = if y < 0 then -whole else whole
            end
            if result == 0 and (y < 0 or 1 / y < 0) then result = -0.0 end
            writeFloatLane(laneR, at, element, result)
        else
            local result
            if op == 19 or op == 20 then
                if x ~= x then result = y elseif y ~= y then result = x
                elseif op == 19 then result = if x < y or (x == y and 1 / x < 0) then x else y
                else result = if x > y or (x == y and 1 / x > 0) then x else y end
            else
                if unordered then result = 0 / 0
                elseif op == 21 then result = if x < y or (x == y and 1 / x < 0) then x else y
                else result = if x > y or (x == y and 1 / x > 0) then x else y end
            end
            writeFloatLane(laneR, at, element, result)
        end
    end
    return loadLanes(laneR, size)
end

local function vectorShift(op: number, element: number, size: number, count: number, a0: number, a1: number,
    a2: number, a3: number): (number, number, number, number)
    local bits = element * 8
    if count >= bits then
        if op ~= 2 then return 0, 0, 0, 0 end
        count = bits - 1
    end
    if element == 8 then
        local function shift(lo: number, hi: number): (number, number)
            if count == 0 then return lo, hi end
            if op == 0 then
                if count >= 32 then return 0, bit32.lshift(lo, count - 32) end
                return bit32.lshift(lo, count), bit32.bor(bit32.lshift(hi, count), bit32.rshift(lo, 32 - count))
            end
            local fill = if op == 2 and hi >= 2147483648 then 4294967295 else 0
            if count >= 32 then
                return if op == 2 then bit32.arshift(hi, count - 32) else bit32.rshift(hi, count - 32), fill
            end
            return bit32.bor(bit32.rshift(lo, count), bit32.lshift(hi, 32 - count)),
                if op == 2 then bit32.arshift(hi, count) else bit32.rshift(hi, count)
        end
        local r0, r1 = shift(a0, a1)
        if size == 8 then return r0, r1, 0, 0 end
        local r2, r3 = shift(a2, a3)
        return r0, r1, r2, r3
    end
    storeLanes(laneA, a0, a1, a2, a3)
    local scale = 2 ^ count
    for at = 0, size - element, element do
        local x = readLane(laneA, at, element, op == 2)
        writeLane(laneR, at, element, if op == 0 then x * scale else math.floor(x / scale))
    end
    return loadLanes(laneR, size)
end

local function truncateLane(value: number, bits: number, signed: boolean, saturate: boolean): number
    local low, high = if signed then -2 ^ (bits - 1) else 0, if signed then 2 ^ (bits - 1) - 1 else 2 ^ bits - 1
    if value ~= value then return if saturate then 0 else 2 ^ (bits - 1) end
    local n = if value < 0 then math.ceil(value) else math.floor(value)
    if n < low or n > high then
        if not saturate then return 2 ^ (bits - 1) end
        n = math.clamp(n, low, high)
    end
    return n
end

-- LaneConversion order matches the IR enumeration.
local function vectorConvert(kind: number, element: number, upper: boolean, shift: number, size: number,
    d0: number, d1: number, d2: number, d3: number, s0: number, s1: number, s2: number, s3: number): (number, number, number, number)
    storeLanes(laneA, s0, s1, s2, s3)
    storeLanes(laneR, 0, 0, 0, 0)
    local half = if upper then 8 else 0
    if kind == 0 then
        for i = 0, 1 do buffer.writef64(laneR, i * 8, buffer.readf32(laneA, half + i * 4)) end
    elseif kind == 1 or kind == 2 then
        if upper then storeLanes(laneR, d0, d1, 0, 0) end
        for i = 0, 1 do
            local value = buffer.readf64(laneA, i * 8)
            if kind == 1 then
                buffer.writef32(laneR, half + i * 4, value)
            else
                buffer.writeu32(laneR, i * 4, truncateLane(value, 32, true, false) % 4294967296)
            end
        end
    elseif kind == 3 then
        for i = 0, 3 do buffer.writef32(laneR, i * 4, buffer.readi32(laneA, i * 4)) end
    elseif kind == 4 then
        for i = 0, 3 do buffer.writeu32(laneR, i * 4, truncateLane(buffer.readf32(laneA, i * 4), 32, true, false) % 4294967296) end
    elseif kind == 5 or kind == 6 then
        local scale = 2 ^ shift
        for at = 0, size - element, element do
            local value
            if element == 8 then
                local lo, hi = buffer.readu32(laneA, at), buffer.readu32(laneA, at + 4)
                if kind == 5 and hi >= 2147483648 then hi -= 4294967296 end
                value = hi * 4294967296 + lo
            else
                value = readLane(laneA, at, element, kind == 5)
            end
            writeFloatLane(laneR, at, element, value / scale)
        end
    elseif kind == 7 or kind == 8 then
        local scale = 2 ^ shift
        for at = 0, size - element, element do
            local value = truncateLane(readFloatLane(laneA, at, element) * scale, element * 8, kind == 7, true)
            if element == 8 then
                value %= 18446744073709551616
                buffer.writeu32(laneR, at, value % 4294967296)
                buffer.writeu32(laneR, at + 4, math.floor(value / 4294967296) % 4294967296)
            else
                writeLane(laneR, at, element, value)
            end
        end
    elseif kind == 9 or kind == 10 then
        local scale = 2 ^ shift
        for i = 0, 8 / element - 1 do
            local value = readLane(laneA, half + i * element, element, kind == 9) * scale
            if element == 4 then
                buffer.writeu32(laneR, i * 8, value % 4294967296)
                buffer.writeu32(laneR, i * 8 + 4, if value < 0 then 4294967295 else math.floor(value / 4294967296))
            else
                writeLane(laneR, i * element * 2, element * 2, value)
            end
        end
    elseif kind == 11 then
        if upper then storeLanes(laneR, d0, d1, 0, 0) end
        local target = element / 2
        for i = 0, 8 / target - 1 do
            local value = if element == 8 then buffer.readu32(laneA, i * 8) else readLane(laneA, i * element, element, false)
            writeLane(laneR, half + i * target, target, value)
        end
    elseif kind == 12 then
        for i = 0, 1 do buffer.writef64(laneR, i * 8, buffer.readi32(laneA, i * 4)) end
    else
        error("unsupported vector conversion " .. kind, 0)
    end
    return loadLanes(laneR, if kind == 1 or kind == 11 then (if upper then 16 else 8) else size)
end

local function roundEven(x: number): number
    if x ~= x or x == math.huge or x == -math.huge then return x end
    local floor = math.floor(x)
    local fraction = x - floor
    local result = if fraction > 0.5 or (fraction == 0.5 and floor % 2 ~= 0) then floor + 1 else floor
    return if result == 0 and (x < 0 or 1 / x < 0) then -0.0 else result
end

local function roundAway(x: number): number
    if x ~= x or x == math.huge or x == -math.huge then return x end
    local magnitude = math.abs(x)
    local floor = math.floor(magnitude)
    local result = if magnitude - floor >= 0.5 then floor + 1 else floor
    return if x < 0 or 1 / x < 0 then -result else result
end

local function roundTruncate(x: number): number
    return if x < 0 then math.ceil(x) else math.floor(x)
end

-- Kinds: 0 FMINNM, 1 FMAXNM, 2 FMIN, 3 FMAX.
local function scalarMinMax(kind: number, x: number, y: number): number
    if kind <= 1 then
        if x ~= x then return y end
        if y ~= y then return x end
    elseif x ~= x or y ~= y then
        return 0 / 0
    end
    if x == y then
        local negative = 1 / x < 0 or 1 / y < 0
        if kind % 2 == 0 then return if negative then -math.abs(x) else x end
        return if (1 / x > 0 or 1 / y > 0) then math.abs(x) else x
    end
    if kind % 2 == 0 then return math.min(x, y) end
    return math.max(x, y)
end

-- ReduceOp order matches the IR enumeration.
local function vectorReduce(op: number, element: number, size: number, s0: number, s1: number, s2: number, s3: number): (number, number)
    if op == 7 then
        local sum = s0 + s2
        return sum % 4294967296, (s1 + s3 + math.floor(sum / 4294967296)) % 4294967296
    end
    storeLanes(laneA, s0, s1, s2, s3)
    local signed = op == 4 or op == 5
    local result = readLane(laneA, 0, element, signed)
    if op == 6 then result = 0 end
    for at = (if op == 6 then 0 else element), size - element, element do
        local x = readLane(laneA, at, element, signed)
        if op == 0 or op == 1 then result += x
        elseif op == 2 or op == 4 then result = math.max(result, x)
        elseif op == 3 or op == 5 then result = math.min(result, x)
        else result += if x >= 2 ^ (element * 8 - 1) then 2 ^ (at / element) else 0 end
    end
    if op == 0 or op == 2 or op == 3 or op == 4 or op == 5 then
        result %= 2 ^ (element * 8)
    end
    return result % 4294967296, 0
end
)"};

// The x87 FPU: an eight-register stack of doubles (extended precision is not modeled), a status word for
// the condition codes, and the control word's rounding mode.
constexpr std::string_view X87Operators[] = {R"luau(
local fpu = {stack = table.create(8, 0), top = 0, status = 0, control = 0x037f}

local function fpuGet(i: number): number
    return fpu.stack[(fpu.top + i) % 8 + 1]
end

local function fpuSet(i: number, value: number)
    fpu.stack[(fpu.top + i) % 8 + 1] = value
end

local function fpuPush(value: number)
    fpu.top = (fpu.top + 7) % 8
    fpu.stack[fpu.top + 1] = value
end

local function fpuPop(): number
    local value = fpu.stack[fpu.top + 1]
    fpu.top = (fpu.top + 1) % 8
    return value
end

local function fpuRound(value: number): number
    local mode = bit32.extract(fpu.control, 10, 2)
    if mode == 0 then return roundEven(value) elseif mode == 1 then return math.floor(value)
    elseif mode == 2 then return math.ceil(value) end
    return roundTruncate(value)
end

local function fpuCompare(a: number, b: number)
    local bits = if a ~= a or b ~= b then 0x4500 elseif a > b then 0 elseif a < b then 0x0100 else 0x4000
    fpu.status = bit32.bor(bit32.band(fpu.status, bit32.bnot(0x4700)), bits)
end

local function decodeExtended(at: number): number
    local lo, hi = read(4, at), read(4, at + 4)
    local top = read(2, at + 8)
    local sign = if top >= 32768 then -1 else 1
    local exponent = top % 32768
    if exponent == 32767 then
        return if hi % 2147483648 == 0 and lo == 0 then sign * math.huge else 0 / 0
    end
    if exponent == 0 and hi == 0 and lo == 0 then return sign * 0 end
    return sign * math.ldexp(hi * 4294967296 + lo, exponent - 16383 - 63)
end

local function encodeExtended(at: number, value: number)
    local sign = if value < 0 or (value == 0 and 1 / value < 0) then 32768 else 0
    local magnitude = math.abs(value)
    if magnitude ~= magnitude then
        write(4, at, 0, 0)
        write(4, at + 4, 0xc0000000, 0)
        write(2, at + 8, 32767 + sign, 0)
    elseif magnitude == math.huge or magnitude == 0 then
        write(4, at, 0, 0)
        write(4, at + 4, if magnitude == 0 then 0 else 0x80000000, 0)
        write(2, at + 8, (if magnitude == 0 then 0 else 32767) + sign, 0)
    else
        local mantissa, exponent = math.frexp(magnitude)
        local scaled = mantissa * 2 ^ 64
        local hi = math.floor(scaled / 4294967296)
        write(4, at, scaled - hi * 4294967296, 0)
        write(4, at + 4, hi, 0)
        write(2, at + 8, exponent - 1 + 16383 + sign, 0)
    end
end

local function loadInteger(at: number, size: number): number
    if size == 8 then
        local lo, hi = read(8, at)
        return if hi >= 2147483648 then (hi - 4294967296) * 4294967296 + lo else hi * 4294967296 + lo
    end
    local value = read(size, at)
    local bound = 2 ^ (size * 8)
    return if value >= bound / 2 then value - bound else value
end

local function storeInteger(at: number, size: number, value: number)
    local bits = size * 8
    if value ~= value or value >= 2 ^ (bits - 1) or value < -2 ^ (bits - 1) then
        -- The integer indefinite value.
        if size == 8 then write(8, at, 0, 0x80000000) else write(size, at, 2 ^ (bits - 1), 0) end
    elseif size == 8 then
        local wrapped = value % 18446744073709551616
        local hi = math.floor(wrapped / 4294967296)
        write(8, at, wrapped - hi * 4294967296, hi)
    else
        write(size, at, value % 2 ^ bits, 0)
    end
end

-- Intel's operand order: op 0 add, 1 mul, 4 sub, 5 subr, 6 div, 7 divr on (a, b) = (destination, source).
local function fpuArithmetic(op: number, a: number, b: number): number
    if op == 0 then return a + b elseif op == 1 then return a * b elseif op == 4 then return a - b
    elseif op == 5 then return b - a elseif op == 6 then return a / b end
    return b / a
end

local function fpuStatus(): number
    return bit32.bor(bit32.band(fpu.status, 0xc7ff), fpu.top * 2048)
end

-- Executes an x87 instruction. Compares into EFLAGS return (zero, parity, carry); FNSTSW AX returns the status.
local function x87Execute(opcode: number, modrm: number, at: number): ...any
    local group = bit32.extract(modrm, 3, 3)
    if modrm < 0xc0 then
        if opcode == 0xd8 or opcode == 0xdc or opcode == 0xda or opcode == 0xde then
            local value
            if opcode == 0xd8 then value = decodeFloat(4, read(4, at), 0)
            elseif opcode == 0xdc then value = decodeFloat(8, read(8, at))
            elseif opcode == 0xda then value = loadInteger(at, 4)
            else value = loadInteger(at, 2) end
            if group == 2 or group == 3 then
                fpuCompare(fpuGet(0), value)
                if group == 3 then fpuPop() end
            else
                fpuSet(0, fpuArithmetic(group, fpuGet(0), value))
            end
        elseif opcode == 0xd9 then
            if group == 0 then fpuPush(decodeFloat(4, read(4, at), 0))
            elseif group == 2 or group == 3 then
                write(4, at, encodeFloat(4, fpuGet(0)))
                if group == 3 then fpuPop() end
            end
        elseif opcode == 0xdb then
            if group == 0 then fpuPush(loadInteger(at, 4))
            elseif group == 1 then storeInteger(at, 4, roundTruncate(fpuPop()))
            elseif group == 2 or group == 3 then
                storeInteger(at, 4, fpuRound(fpuGet(0)))
                if group == 3 then fpuPop() end
            elseif group == 5 then fpuPush(decodeExtended(at))
            elseif group == 7 then encodeExtended(at, fpuPop()) end
        elseif opcode == 0xdd then
            if group == 0 then fpuPush(decodeFloat(8, read(8, at)))
            elseif group == 1 then storeInteger(at, 8, roundTruncate(fpuPop()))
            elseif group == 2 or group == 3 then
                write(8, at, encodeFloat(8, fpuGet(0)))
                if group == 3 then fpuPop() end
            elseif group == 7 then write(2, at, fpuStatus(), 0) end
        elseif opcode == 0xdf then
            if group == 0 then fpuPush(loadInteger(at, 2))
            elseif group == 1 then storeInteger(at, 2, roundTruncate(fpuPop()))
            elseif group == 2 or group == 3 then
                storeInteger(at, 2, fpuRound(fpuGet(0)))
                if group == 3 then fpuPop() end
            elseif group == 5 then fpuPush(loadInteger(at, 8))
            elseif group == 7 then storeInteger(at, 8, fpuRound(fpuPop())) end
        end
        return nil
    end
    local i = modrm % 8
    if opcode == 0xd8 then
        if group == 2 or group == 3 then
            fpuCompare(fpuGet(0), fpuGet(i))
            if group == 3 then fpuPop() end
        else
            fpuSet(0, fpuArithmetic(group, fpuGet(0), fpuGet(i)))
        end
    elseif opcode == 0xdc or opcode == 0xde then
        if opcode == 0xde and modrm == 0xd9 then
            fpuCompare(fpuGet(0), fpuGet(1))
            fpuPop()
            fpuPop()
        elseif group == 2 or group == 3 then
            fpuCompare(fpuGet(0), fpuGet(i))
            if group == 3 then fpuPop() end
        else
            -- ST(i) is the destination; the SUB/SUBR and DIV/DIVR encodings swap relative to D8.
            local swapped = if group == 4 then 5 elseif group == 5 then 4 elseif group == 6 then 7 elseif group == 7 then 6 else group
            fpuSet(i, fpuArithmetic(swapped, fpuGet(i), fpuGet(0)))
            if opcode == 0xde then fpuPop() end
        end
    elseif opcode == 0xd9 then
        if group == 0 then
            fpuPush(fpuGet(i))
        elseif group == 1 then
            local a, b = fpuGet(0), fpuGet(i)
            fpuSet(0, b)
            fpuSet(i, a)
        elseif modrm == 0xe0 then fpuSet(0, -fpuGet(0))
        elseif modrm == 0xe1 then fpuSet(0, math.abs(fpuGet(0)))
        elseif modrm == 0xe4 then fpuCompare(fpuGet(0), 0)
        elseif modrm == 0xe5 then
            local v = fpuGet(0)
            local class = if v ~= v then 0x0100 elseif v == math.huge or v == -math.huge then 0x0500
                elseif v == 0 then 0x4000 else 0x0400
            local sign = if v < 0 or (v == 0 and 1 / v < 0) then 0x0200 else 0
            fpu.status = bit32.bor(bit32.band(fpu.status, bit32.bnot(0x4700)), class, sign)
        elseif modrm == 0xe8 then fpuPush(1)
        elseif modrm == 0xe9 then fpuPush(math.log(10, 2))
        elseif modrm == 0xea then fpuPush(1 / math.log(2))
        elseif modrm == 0xeb then fpuPush(math.pi)
        elseif modrm == 0xec then fpuPush(math.log10(2))
        elseif modrm == 0xed then fpuPush(math.log(2))
        elseif modrm == 0xee then fpuPush(0)
        elseif modrm == 0xf0 then fpuSet(0, 2 ^ fpuGet(0) - 1)
        elseif modrm == 0xf1 then
            local x = fpuPop()
            fpuSet(0, fpuGet(0) * math.log(x, 2))
        elseif modrm == 0xf2 then
            fpuSet(0, math.tan(fpuGet(0)))
            fpuPush(1)
        elseif modrm == 0xf3 then
            local x = fpuPop()
            fpuSet(0, math.atan2(fpuGet(0), x))
        elseif modrm == 0xf5 or modrm == 0xf8 then
            local a, b = fpuGet(0), fpuGet(1)
            fpuSet(0, if modrm == 0xf8 then math.fmod(a, b) else a - roundEven(a / b) * b)
            fpu.status = bit32.band(fpu.status, bit32.bnot(0x0400))
        elseif modrm == 0xf6 then fpu.top = (fpu.top + 7) % 8
        elseif modrm == 0xf7 then fpu.top = (fpu.top + 1) % 8
        elseif modrm == 0xf9 then
            local x = fpuPop()
            fpuSet(0, fpuGet(0) * math.log(x + 1, 2))
        elseif modrm == 0xfa then fpuSet(0, math.sqrt(fpuGet(0)))
        elseif modrm == 0xfb then
            local v = fpuGet(0)
            fpuSet(0, math.sin(v))
            fpuPush(math.cos(v))
        elseif modrm == 0xfc then fpuSet(0, fpuRound(fpuGet(0)))
        elseif modrm == 0xfd then fpuSet(0, fpuGet(0) * 2 ^ roundTruncate(fpuGet(1)))
        elseif modrm == 0xfe then fpuSet(0, math.sin(fpuGet(0)))
        elseif modrm == 0xff then fpuSet(0, math.cos(fpuGet(0))) end
    elseif opcode == 0xdd then
        if group == 2 or group == 3 then
            fpuSet(i, fpuGet(0))
            if group == 3 then fpuPop() end
        elseif group == 4 or group == 5 then
            fpuCompare(fpuGet(0), fpuGet(i))
            if group == 5 then fpuPop() end
        end
    elseif opcode == 0xda then
        if modrm == 0xe9 then
            fpuCompare(fpuGet(0), fpuGet(1))
            fpuPop()
            fpuPop()
        else
            fpuSet(0, fpuGet(i))
        end
    elseif opcode == 0xdb then
        if modrm == 0xe2 then
            fpu.status = bit32.band(fpu.status, 0x7f00)
        elseif modrm == 0xe3 then
            fpu.top, fpu.status, fpu.control = 0, 0, 0x037f
        elseif group == 5 or group == 6 then
            local a, b = fpuGet(0), fpuGet(i)
            local unordered = a ~= a or b ~= b
            return unordered or a == b, unordered, unordered or a < b
        else
            fpuSet(0, fpuGet(i))
        end
    elseif opcode == 0xdf then
        if modrm == 0xe0 then return fpuStatus() end
        if group == 5 or group == 6 then
            local a, b = fpuGet(0), fpuGet(i)
            fpuPop()
            local unordered = a ~= a or b ~= b
            return unordered or a == b, unordered, unordered or a < b
        end
    end
    return nil
end
)luau"};

constexpr std::string_view PrimeOperators[] = {R"(
local function addMod(alo: number, ahi: number, blo: number, bhi: number,
    mlo: number, mhi: number): (number, number)
    local total = alo + blo
    local lo = total % 4294967296
    local hi = ahi + bhi + math.floor(total / 4294967296)
    if hi > mhi or (hi == mhi and lo >= mlo) then
        local rest = lo - mlo
        lo, hi = rest % 4294967296, hi - mhi + math.floor(rest / 4294967296)
    end
    return lo, hi
end

local function halfWord(lo: number, hi: number): (number, number)
    return math.floor(lo / 2) + (hi % 2) * 2147483648, math.floor(hi / 2)
end

local function multiplyMod(alo: number, ahi: number, blo: number, bhi: number,
    mlo: number, mhi: number): (number, number)
    local lo, hi = 0, 0
    while blo ~= 0 or bhi ~= 0 do
        if blo % 2 ~= 0 then
            lo, hi = addMod(lo, hi, alo, ahi, mlo, mhi)
        end
        blo, bhi = halfWord(blo, bhi)
        if blo ~= 0 or bhi ~= 0 then
            alo, ahi = addMod(alo, ahi, alo, ahi, mlo, mhi)
        end
    end
    return lo, hi
end

local function powerMod(base: number, elo: number, ehi: number, mlo: number, mhi: number): (number, number)
    local lo, hi, alo, ahi = 1, 0, base, 0
    while elo ~= 0 or ehi ~= 0 do
        if elo % 2 ~= 0 then
            lo, hi = multiplyMod(lo, hi, alo, ahi, mlo, mhi)
        end
        elo, ehi = halfWord(elo, ehi)
        if elo ~= 0 or ehi ~= 0 then
            alo, ahi = multiplyMod(alo, ahi, alo, ahi, mlo, mhi)
        end
    end
    return lo, hi
end

local primeWitnesses = {2, 325, 9375, 28178, 450775, 9780504, 1795265022}
local function isLargePrime(lo: number, hi: number): boolean
    local exponentLo, exponentHi, twos = lo - 1, hi, 0
    while exponentLo % 2 == 0 do
        exponentLo, exponentHi = halfWord(exponentLo, exponentHi)
        twos += 1
    end
    for _, witness in primeWitnesses do
        local a, b = powerMod(witness, exponentLo, exponentHi, lo, hi)
        if a == 1 and b == 0 then continue end
        for _ = 1, twos - 1 do
            if a == lo - 1 and b == hi then break end
            a, b = multiplyMod(a, b, a, b, lo, hi)
        end
        if a ~= lo - 1 or b ~= hi then return false end
    end
    return true
end

local function nextPrime(lo: number, hi: number): (number, number)
    if hi == 0 and lo <= 2 then return if lo == 0 then 0 else 2, 0 end
    if hi == 4294967295 and lo > 4294967237 then error("guest prime search overflow", 0) end
    if lo % 2 == 0 then lo += 1 end
    while true do
        if hi == 0 then
            local prime = true
            for divisor = 3, math.floor(math.sqrt(lo)), 2 do
                if lo % divisor == 0 then
                    prime = false
                    break
                end
            end
            if prime then return lo, 0 end
        elseif isLargePrime(lo, hi) then
            return lo, hi
        end
        lo += 2
        if lo >= 4294967296 then
            lo -= 4294967296
            hi += 1
        end
    end
end
)"};

constexpr std::string_view DivisionOperators[] = {R"(
local function unsignedDivide(size: number, alo: number, ahi: number, dlo: number, dhi: number,
    blo: number, bhi: number): (number, number, number, number)
    local word = 4294967296
    if blo == 0 and bhi == 0 then
        error("guest division by zero", 0)
    end
    local dividendLo = alo
    local dividendHi = if size == 4 then dlo else ahi
    local remLo = dlo
    local remHi = if size == 4 then 0 else dhi
    if remHi > bhi or (remHi == bhi and remLo >= blo) then
        error("guest division overflow", 0)
    end
    if (size == 4 or (dlo == 0 and dhi == 0)) and dividendHi < 2097152 then
        local dividend = dividendLo + dividendHi * word
        if bhi >= 2097152 then
            return 0, 0, dividendLo, dividendHi
        end
        local divisor = blo + bhi * word
        local remainder = dividend % divisor
        local quotient = (dividend - remainder) / divisor
        return quotient % word, math.floor(quotient / word), remainder % word, math.floor(remainder / word)
    end
    local quotientLo, quotientHi = 0, 0
    for bit = size * 8 - 1, 0, -1 do
        local incoming = if bit < 32 then bit32.extract(alo, bit) else bit32.extract(ahi, bit - 32)
        local lo = remLo * 2 + incoming
        local hi = remHi * 2 + math.floor(lo / word)
        remLo, remHi = lo % word, hi % word
        if hi >= word or remHi > bhi or (remHi == bhi and remLo >= blo) then
            local difference = remLo - blo
            remLo = difference % word
            remHi = (remHi - bhi + math.floor(difference / word)) % word
            if bit < 32 then
                quotientLo += 2 ^ bit
            else
                quotientHi += 2 ^ (bit - 32)
            end
        end
    end
    return quotientLo, quotientHi, remLo, remHi
end

local function negateWords(a: number, b: number, c: number, d: number): (number, number, number, number)
    a, b, c, d = bit32.bnot(a) + 1, bit32.bnot(b), bit32.bnot(c), bit32.bnot(d)
    if a == 4294967296 then
        a, b = 0, b + 1
        if b == 4294967296 then
            b, c = 0, c + 1
            if c == 4294967296 then c, d = 0, (d + 1) % 4294967296 end
        end
    end
    return a, b, c, d
end

-- IDIV divides RDX:RAX (EDX:EAX for 32-bit operands) by a signed divisor.
local function signedDivide(size: number, alo: number, ahi: number, dlo: number, dhi: number,
    blo: number, bhi: number): (number, number, number, number)
    local wide = size == 8
    if not wide then ahi, dhi, bhi = 0, 0, 0 end
    -- The dividend's words from low to high, and the divisor's.
    local w0, w1, w2, w3 = alo, if wide then ahi else dlo, if wide then dlo else 0, if wide then dhi else 0
    local negativeDividend = (if wide then w3 else w1) >= 2147483648
    local negativeDivisor = (if wide then bhi else blo) >= 2147483648
    if negativeDividend then
        w0, w1, w2, w3 = negateWords(w0, w1, w2, w3)
        if not wide then w2, w3 = 0, 0 end
    end
    if negativeDivisor then
        blo, bhi = (-blo) % 4294967296, (-bhi - (if blo == 0 then 0 else 1)) % 4294967296
        if not wide then bhi = 0 end
    end
    if blo == 0 and bhi == 0 then
        error("guest division by zero", 0)
    end
    local qlo, qhi, rlo, rhi
    if wide then
        qlo, qhi, rlo, rhi = unsignedDivide(8, w0, w1, w2, w3, blo, bhi)
    else
        qlo, qhi, rlo, rhi = unsignedDivide(4, w0, 0, w1, 0, blo, 0)
    end
    local top = if wide then qhi else qlo
    local negativeQuotient = negativeDividend ~= negativeDivisor
    if top > 2147483648 or (top == 2147483648 and (not negativeQuotient or (if wide then qlo ~= 0 else false))) then
        error("guest division overflow", 0)
    end
    if negativeQuotient then
        qlo, qhi = (-qlo) % 4294967296, (-qhi - (if qlo == 0 then 0 else 1)) % 4294967296
    end
    if negativeDividend then
        rlo, rhi = (-rlo) % 4294967296, (-rhi - (if rlo == 0 then 0 else 1)) % 4294967296
    end
    if not wide then qhi, rhi = 0, 0 end
    return qlo, qhi, rlo, rhi
end

-- 128-bit division for the compiler runtime helpers (__udivti3 and friends).
local function divide128(signed: boolean, wantRemainder: boolean, a0: number, a1: number, a2: number, a3: number,
    b0: number, b1: number, b2: number, b3: number): (number, number, number, number)
    local negativeA = signed and a3 >= 2147483648
    local negativeB = signed and b3 >= 2147483648
    if negativeA then a0, a1, a2, a3 = negateWords(a0, a1, a2, a3) end
    if negativeB then b0, b1, b2, b3 = negateWords(b0, b1, b2, b3) end
    if b0 == 0 and b1 == 0 and b2 == 0 and b3 == 0 then
        error("guest division by zero", 0)
    end
    local dividend = {a0, a1, a2, a3}
    local quotient = {0, 0, 0, 0}
    local r0, r1, r2, r3 = 0, 0, 0, 0
    for bit = 127, 0, -1 do
        local overflow = r3 >= 2147483648
        r3 = bit32.bor(bit32.lshift(r3, 1), bit32.rshift(r2, 31))
        r2 = bit32.bor(bit32.lshift(r2, 1), bit32.rshift(r1, 31))
        r1 = bit32.bor(bit32.lshift(r1, 1), bit32.rshift(r0, 31))
        r0 = bit32.bor(bit32.lshift(r0, 1), bit32.extract(dividend[bit // 32 + 1], bit % 32))
        if overflow or r3 > b3 or (r3 == b3 and (r2 > b2 or (r2 == b2 and (r1 > b1 or (r1 == b1 and r0 >= b0))))) then
            local d0 = r0 - b0
            local d1 = r1 - b1 - (if d0 < 0 then 1 else 0)
            local d2 = r2 - b2 - (if d1 < 0 then 1 else 0)
            local d3 = r3 - b3 - (if d2 < 0 then 1 else 0)
            r0, r1, r2, r3 = d0 % 4294967296, d1 % 4294967296, d2 % 4294967296, d3 % 4294967296
            local word = bit // 32 + 1
            quotient[word] += 2 ^ (bit % 32)
        end
    end
    if wantRemainder then
        if negativeA then r0, r1, r2, r3 = negateWords(r0, r1, r2, r3) end
        return r0, r1, r2, r3
    end
    local q0, q1, q2, q3 = quotient[1], quotient[2], quotient[3], quotient[4]
    if negativeA ~= negativeB then q0, q1, q2, q3 = negateWords(q0, q1, q2, q3) end
    return q0, q1, q2, q3
end

local function divideWord(size: number, signed: boolean, alo: number, ahi: number,
    blo: number, bhi: number): (number, number)
    local an = signed and (if size == 8 then ahi else alo) >= 2147483648
    local bn = signed and (if size == 8 then bhi else blo) >= 2147483648
    if an then
        alo, ahi = (-alo) % 4294967296, (-ahi - (if alo == 0 then 0 else 1)) % 4294967296
    end
    if bn then
        blo, bhi = (-blo) % 4294967296, (-bhi - (if blo == 0 then 0 else 1)) % 4294967296
    end
    if size == 4 then
        ahi, bhi = 0, 0
    end
    if blo == 0 and bhi == 0 then return 0, 0 end
    local lo, hi = unsignedDivide(size, alo, ahi, 0, 0, blo, bhi)
    if an ~= bn then
        lo, hi = (-lo) % 4294967296, (-hi - (if lo == 0 then 0 else 1)) % 4294967296
    end
    return lo, if size == 8 then hi else 0
end
)"};

constexpr std::string_view DecimalOperators[] = {R"luau(
local function formatDouble(value: number, lo: number, hi: number): string
    local sign = if hi >= 2147483648 then "-" else ""
    if value ~= value then
        if bit32.band(hi, 0x00080000) == 0 then return sign .. "nan(snan)" end
        if hi == 0xfff80000 and lo == 0 then return "-nan(ind)" end
        return sign .. "nan"
    end
    value = math.abs(value)
    if value == math.huge then return sign .. "inf" end
    if value == 0 then return sign .. "0" end

    local text = string.format("%.16e", value)
    for precision = 0, 15 do
        local trial = string.format("%." .. tostring(precision) .. "e", value)
        if tonumber(trial) == value then
            text = trial
            break
        end
    end
    local mantissa, power = string.match(text, "^([^e]+)e([+-]%d+)$")
    local digits = string.gsub(mantissa, "%.", "")
    local exponent = tonumber(power) :: number
    local point = exponent + 1
    local fixedSize = if point <= 0 then 2 - point + #digits else math.max(point, #digits + (if point < #digits then 1 else 0))
    if fixedSize > #text then return sign .. text end
    if point <= 0 then
        return sign .. "0." .. string.rep("0", -point) .. digits
    elseif point >= #digits then
        return sign .. string.format("%.0f", value)
    else
        return sign .. string.sub(digits, 1, point) .. "." .. string.sub(digits, point + 1)
    end
end
)luau"};

constexpr std::string_view MultiplyOperators[] = {R"(
local function multiply32(a: number, b: number): (number, number)
    local al, ah = a % 65536, math.floor(a / 65536)
    local bl, bh = b % 65536, math.floor(b / 65536)
    local lower = al * bl + (al * bh + ah * bl) * 65536
    return lower % 4294967296, ah * bh + math.floor(lower / 4294967296)
end

local function multiplyLow(alo: number, ahi: number, blo: number, bhi: number): (number, number)
    local lo, carry = multiply32(alo, blo)
    local crossA = multiply32(alo, bhi)
    local crossB = multiply32(ahi, blo)
    return lo, (carry + crossA + crossB) % 4294967296
end

local function signedMultiply(size: number, alo: number, ahi: number, blo: number, bhi: number, unsigned: boolean?):
    (number, number, boolean, number, number)
    local word = 4294967296
    if size == 4 then
        local low, upper = multiply32(alo, blo)
        if unsigned then return low, 0, upper ~= 0, upper, 0 end
        upper = (upper - (if alo >= 2147483648 then blo else 0) - (if blo >= 2147483648 then alo else 0)) % word
        return low, 0, upper ~= (if low >= 2147483648 then word - 1 else 0), upper, 0
    end
    local lo, carry = multiply32(alo, blo)
    local crossALo, crossAHi = multiply32(alo, bhi)
    local crossBLo, crossBHi = multiply32(ahi, blo)
    local upperLo, upperHi = multiply32(ahi, bhi)
    local middle = carry + crossALo + crossBLo
    local hi = middle % word
    local upper = upperLo + crossAHi + crossBHi + math.floor(middle / word)
    upperLo = upper % word
    upperHi += math.floor(upper / word)
    if unsigned then return lo, hi, upperLo ~= 0 or upperHi ~= 0, upperLo, upperHi end

    -- Each negative operand subtracts the other operand from the upper word.
    local negativeA, negativeB = ahi >= 2147483648, bhi >= 2147483648
    upper = upperLo - (if negativeA then blo else 0) - (if negativeB then alo else 0)
    upperLo = upper % word
    upperHi = (upperHi - (if negativeA then bhi else 0) - (if negativeB then ahi else 0) + math.floor(upper / word)) % word
    local sign = if hi >= 2147483648 then word - 1 else 0
    return lo, hi, upperLo ~= sign or upperHi ~= sign, upperLo, upperHi
end
)"};

constexpr std::string_view MemoryOperators[] = {R"(
local function address(lo: number, hi: number): number
    if hi ~= 0 then
        error("guest address is out of range", 0)
    end
    return lo
end

-- Luau inlines this; a constant displacement folds the range tests, leaving an add and one compare when the
-- low word does not carry or borrow.
local function offset(lo: number, hi: number, displacement: number): (number, number)
    local sum = lo + displacement
    if displacement >= 0 and displacement < 4294967296 then
        if sum < 4294967296 then return sum, hi end
        return sum - 4294967296, (hi + 1) % 4294967296
    elseif displacement < 0 and displacement > -4294967296 then
        if sum >= 0 then return sum, hi end
        return sum + 4294967296, (hi + 4294967295) % 4294967296
    end
    return sum % 4294967296, (hi + math.floor(sum / 4294967296)) % 4294967296
end

-- The address a memory access uses for a register plus a displacement. With a zero high word the sum is the
-- address: one that leaves the low 32 bits fails the access's bounds check like any unmapped address. Luau
-- inlines addressAt at every access; the rare wrapped case calls through `process`, which Luau never inlines,
-- keeping the inlined code and the compiler's work small (and adding no local to a module near the limit).
process.wrappedAddress = function(lo: number, hi: number, displacement: number): number
    return address(offset(lo, hi, displacement))
end
local function addressAt(lo: number, hi: number, displacement: number): number
    if hi ~= 0 then
        return (process.wrappedAddress :: any)(lo, hi, displacement)
    end
    return lo + displacement
end

local function indexedOffset(lo: number, hi: number, indexLo: number, indexHi: number,
    scale: number, displacement: number): (number, number)
    local sum = lo + indexLo * scale + displacement
    return sum % 4294967296, (hi + indexHi * scale + math.floor(sum / 4294967296)) % 4294967296
end

type DataRange = {first: number, last: number, bytes: string, mode: number}

local function makeMemory(imageSize: number, data: {DataRange}, heapEnabled: boolean, mapped: boolean, stackSize: number)
    local heapLimit = if mapped then 67108864 else 16777216
    local stackBottom = math.ceil(imageSize / 16) * 16
    local stackTop = stackBottom + stackSize
    local heapStart = stackTop + 16
    -- Guest memory is one buffer from the lowest image address up: the image, the stack, then the heap, so an
    -- access only subtracts the base. The heap part grows by copying into a larger buffer.
    local memoryBase = if #data > 0 then math.min(data[1].first, stackBottom) else stackBottom
    local memoryEnd = heapStart + (if heapEnabled then math.min(heapLimit, 1048576) else 0)
    local memory = buffer.create(memoryEnd - memoryBase)
    for _, range in data do
        buffer.writestring(memory, range.first - memoryBase, range.bytes)
    end
    -- Translations without mapped images embed only the data they reference: reading elsewhere is a bug.
    local strictImage = not mapped
    -- Translated programs access memory through inlined copies of read and write that keep their own reference
    -- to the buffer; this callback hands them the new one when the heap grows.
    local memoryMoved: ((buffer) -> ())? = nil
    process.watchMemory = function(moved: (buffer) -> ()): (number, number)
        memoryMoved = moved
        moved(memory)
        return memoryBase, stackBottom
    end
    -- Heap blocks are 16-byte rounded (word-at-a-time string routines read past the requested size), and
    -- freed blocks are reused by later allocations of the same rounded length.
    local heapSizes: {[number]: number} = {}
    local heapLengths: {[number]: number} = {}
    local freeBlocks: {[number]: {number}} = {}
    local nextAllocation = heapStart
    local criticalSections: {[number]: number} = {}
    -- Each held pthread mutex's owning thread and how many times it holds it.
    local pthreadLocks: {[number]: {owner: number, count: number}} = {}
    local srwLocks: {[number]: number} = {}
    local pageProtection: {[number]: number} = {}
    local classicLocale = 0
    local useGlobalLocale = true
    -- Guest memory belongs to the module: data, heap, and locks persist across export calls.
    local function reset(stack: boolean)
    end
    -- Where the native program would take a segmentation fault (null or wild pointers, stack overflow).
    local function fault(at: number): never
        error(string.format("guest accessed unmapped memory at 0x%x", at), 0)
    end
    -- Checks an access below the stack against the image's ranges and their write protection.
    local function checkImage(at: number, limit: number, write: boolean)
        local first, last = 1, #data
        while first <= last do
            local index = math.floor((first + last) / 2)
            local range = data[index]
            if at < range.first then
                last = index - 1
            elseif at >= range.last then
                first = index + 1
            elseif limit <= range.last then
                if write then
                    if range.mode == 0 then error("write to read-only guest image", 0) end
                    if range.mode >= 2 then
                        for page = math.floor(at / 4096), math.floor((limit - 1) / 4096) do
                            if (pageProtection[page] or (if range.mode == 3 then 4 else 2)) ~= 4 then
                                error("write to protected guest page", 0)
                            end
                        end
                    end
                end
                return
            else
                break
            end
        end
        if not strictImage then
            fault(at)
        end
        error("guest memory range was not resolved during translation: " .. at, 0)
    end
    local function locate(at: number, size: number, write: boolean): (buffer, number)
        if at < stackBottom then
            if write or strictImage or at < memoryBase then checkImage(at, at + size, write) end
        elseif at + size > memoryEnd then
            fault(at)
        end
        return memory, at - memoryBase
    end
    local function read(size: number, at: number): (number, number)
        if at < stackBottom then
            if strictImage or at < memoryBase then checkImage(at, at + size, false) end
        elseif at + size > memoryEnd then
            fault(at)
        end
        local index = at - memoryBase
        if size == 8 then
            return buffer.readu32(memory, index), buffer.readu32(memory, index + 4)
        elseif size == 4 then
            return buffer.readu32(memory, index), 0
        elseif size == 1 then
            return buffer.readu8(memory, index), 0
        end
        return buffer.readu16(memory, index), 0
    end
    local function write(size: number, at: number, lo: number, hi: number)
        if at < stackBottom then
            checkImage(at, at + size, true)
        elseif at + size > memoryEnd then
            fault(at)
        end
        local index = at - memoryBase
        if size == 8 then
            buffer.writeu32(memory, index, lo)
            buffer.writeu32(memory, index + 4, hi)
        elseif size == 4 then
            buffer.writeu32(memory, index, lo)
        elseif size == 1 then
            buffer.writeu8(memory, index, bit32.band(lo, 255))
        else
            buffer.writeu16(memory, index, bit32.band(lo, 65535))
        end
    end
    local function readString(at: number, count: number): string
        if count <= 0 then return "" end
        local bytes, index = locate(at, count, false)
        return buffer.readstring(bytes, index, count)
    end
    local function writeString(at: number, text: string)
        if #text == 0 then return end
        local bytes, index = locate(at, #text, true)
        buffer.writestring(bytes, index, text)
    end
    local function locateXmm(at: number, aligned: boolean, writeAccess: boolean): (buffer, number)
        if aligned and at % 16 ~= 0 then
            error("unaligned XMM memory operand", 0)
        end
        return locate(at, 16, writeAccess)
    end
    local function readXmm(at: number, aligned: boolean): (number, number, number, number)
        local bytes, index = locateXmm(at, aligned, false)
        return buffer.readu32(bytes, index), buffer.readu32(bytes, index + 4),
            buffer.readu32(bytes, index + 8), buffer.readu32(bytes, index + 12)
    end
    local function writeXmm(at: number, aligned: boolean, a: number, b: number, c: number, d: number)
        local bytes, index = locateXmm(at, aligned, true)
        buffer.writeu32(bytes, index, a)
        buffer.writeu32(bytes, index + 4, b)
        buffer.writeu32(bytes, index + 8, c)
        buffer.writeu32(bytes, index + 12, d)
    end
    local function release(at: number)
        local length = heapLengths[at]
        heapLengths[at] = nil
        heapSizes[at] = nil
        local list = freeBlocks[length]
        if list then
            table.insert(list, at)
        else
            freeBlocks[length] = {at}
        end
    end
    -- An allocation's usable size, which malloc_size and malloc_usable_size report.
    process.heapLength = function(at: number): number? return heapLengths[at] end
    local function resize(lo: number, hi: number, size: number, sizeHi: number): (number, number)
        local at = address(lo, hi)
        local length = heapLengths[at]
        if at ~= 0 and length == nil then
            error("invalid guest allocation pointer", 0)
        end
        if sizeHi ~= 0 then
            return 0, 0
        end
        if size == 0 then
            if length then release(at) end
            return 0, 0
        end
        if length and size <= length and size * 2 > length then
            -- Shrinking or growing within the rounded block keeps the allocation, and every byte of it: malloc_size
            -- reports the whole block as usable.
            heapSizes[at] = size
            return at, 0
        end
        local needed = math.ceil(size / 16) * 16
        local start
        local list = freeBlocks[needed]
        if list and #list > 0 then
            start = table.remove(list) :: number
            buffer.fill(memory, start - memoryBase, 0, needed)
        else
            if nextAllocation + needed - heapStart > heapLimit then
                return 0, 0
            end
            start = nextAllocation
            nextAllocation += needed
            if nextAllocation > memoryEnd then
                local capacity = math.max(memoryEnd - heapStart, 65536)
                while heapStart + capacity < nextAllocation do
                    capacity *= 2
                end
                local larger = buffer.create(heapStart + math.min(capacity, heapLimit) - memoryBase)
                buffer.copy(larger, 0, memory, 0, start - memoryBase)
                memory = larger
                memoryEnd = heapStart + math.min(capacity, heapLimit)
                if memoryMoved then memoryMoved(memory) end
            end
        end
        heapSizes[start] = size
        heapLengths[start] = needed
        if length then
            buffer.copy(memory, start - memoryBase, memory, at - memoryBase, math.min(size, length))
            release(at)
        end
        return start, 0
    end
)", R"(
    local function allocateCpp(size: number, sizeHi: number, throwing: boolean): (number, number)
        local pointer = resize(0, 0, math.max(size, 1), sizeHi)
        if pointer == 0 and throwing then
            error("guest C++ allocation failed", 0)
        end
        return pointer, 0
    end
    local errnoCell = 0
    local function errnoAddress(): number
        -- Each guest thread has its own errno.
        if process.threadErrno then return process.threadErrno end
        if errnoCell == 0 then
            errnoCell = resize(0, 0, 8, 0)
            write(8, errnoCell, 0, 0)
        end
        return errnoCell
    end
    local function cLocale(): (number, number)
        if classicLocale ~= 0 then return classicLocale, 0 end
        local base = allocateCpp(4074, 0, true)
        local bytes, at = locate(base, 4074, true)
        local classes, lower, upper = at + 232, at + 1000, at + 2536
        buffer.writeu32(bytes, at + 104, base + 232 + 128 * 2)
        buffer.writeu32(bytes, at + 112, base + 1000 + 128 * 4)
        buffer.writeu32(bytes, at + 120, base + 2536 + 128 * 4)
        buffer.writeu8(bytes, at + 4072, 67)
        for category = 0, 12 do
            buffer.writeu32(bytes, at + 128 + category * 8, base + 4072)
        end
        for ch = -128, 255 do
            local n = ch % 256
            local capital, small = n >= 65 and n <= 90, n >= 97 and n <= 122
            local digit = n >= 48 and n <= 57
            local alpha = capital or small
            local printable = n >= 32 and n <= 126
            local space = n == 32 or (n >= 9 and n <= 13)
            local flags = (if capital then 0x0100 else 0) + (if small then 0x0200 else 0) +
                (if alpha then 0x0400 else 0) + (if digit then 0x0800 else 0) +
                (if digit or (n >= 65 and n <= 70) or (n >= 97 and n <= 102) then 0x1000 else 0) +
                (if space then 0x2000 else 0) + (if printable then 0x4000 else 0) +
                (if printable and n ~= 32 then 0x8000 else 0) + (if n == 9 or n == 32 then 1 else 0) +
                (if n < 32 or n == 127 then 2 else 0) +
                (if printable and not (alpha or digit or space) then 4 else 0) + (if alpha or digit then 8 else 0)
            local index = ch + 128
            buffer.writeu16(bytes, classes + 2 * index, flags)
            buffer.writei32(bytes, lower + 4 * index, if ch == -1 then -1 elseif capital then n + 32 else n)
            buffer.writei32(bytes, upper + 4 * index, if ch == -1 then -1 elseif small then n - 32 else n)
        end
        classicLocale = base
        return base, 0
    end
    local function useCLocale(lo: number, hi: number): (number, number)
        local previousGlobal = useGlobalLocale
        if lo == 4294967295 and hi == 4294967295 then
            useGlobalLocale = true
        elseif lo ~= 0 or hi ~= 0 then
            if lo ~= cLocale() or hi ~= 0 then error("unsupported guest locale object", 0) end
            useGlobalLocale = false
        end
        if previousGlobal then return 4294967295, 4294967295 end
        return cLocale()
    end
    local wideClasses: {[string]: number} = {
        upper = 0x0100, lower = 0x0200, alpha = 0x0400, digit = 0x0800, xdigit = 0x1000,
        space = 0x2000, print = 0x4000, graph = 0x8000, blank = 1, cntrl = 2, punct = 4, alnum = 8,
    }
    local function wideClass(lo: number, hi: number): (number, number)
        local at = address(lo, hi)
        local letters = {}
        for i = 0, 6 do
            local byte = read(1, at + i)
            if byte == 0 then
                return wideClasses[table.concat(letters)] or 0, 0
            end
            letters[i + 1] = string.char(byte)
        end
        return 0, 0
    end
    local function testWideClass(character: number, mask: number): number
        if character >= 128 then return 0 end
        local locale = cLocale()
        local tableAt = read(8, locale + 104)
        return if bit32.band(read(2, tableAt + character * 2), mask) ~= 0 then 1 else 0
    end
    local function processHeap(op: string, handle: number, handleHi: number, flags: number,
        pointer: number, pointerHi: number, size: number?, sizeHi: number?): (number, number)
        if handle ~= 0xffeeffe0 or handleHi ~= 0 then
            error("invalid Windows process heap handle", 0)
        end
        local previous = if pointerHi == 0 then heapLengths[pointer] else nil
        if op == "HeapFree" then
            if not previous then return 0, 0 end
            release(pointer)
            return 1, 0
        elseif op == "HeapSize" then
            if previous then return heapSizes[pointer], 0 end
            return 4294967295, 4294967295
        end
        local result = 0
        if op == "HeapAlloc" then
            result = resize(0, 0, math.max(pointer, 1), pointerHi)
        elseif previous and size and sizeHi == 0 then
            if bit32.band(flags, 16) == 0 then
                result = resize(pointer, 0, math.max(size, 1), 0)
            elseif size <= previous then
                local used = heapSizes[pointer]
                if size > used then buffer.fill(memory, pointer - memoryBase + used, 0, size - used) end
                heapSizes[pointer] = math.max(size, 1)
                result = pointer
            end
        end
        if result == 0 and bit32.band(flags, 4) ~= 0 then
            error("Windows process heap allocation failed", 0)
        end
        return result, 0
    end
    local function criticalSection(op: string, lo: number, hi: number, flags: number): (number, number)
        local at = address(lo, hi)
        local depth = criticalSections[at]
        if op == "initialize" then
            if flags ~= 0 and flags ~= 0x01000000 then return 0, 0 end
            locate(at, 40, true)
            if depth then error("guest critical section is already initialized", 0) end
            criticalSections[at] = 0
        elseif depth == nil and op == "leave" then
            error("cannot release an unowned guest critical section", 0)
        elseif depth == nil then
            -- Zero-filled critical sections inside runtime structures work without explicit initialization.
            criticalSections[at] = if op == "delete" then nil else 1
        elseif op == "delete" then
            if depth ~= 0 then error("cannot delete an owned guest critical section", 0) end
            criticalSections[at] = nil
        elseif op == "leave" then
            if depth == 0 then error("cannot release an unowned guest critical section", 0) end
            criticalSections[at] = depth - 1
        else
            criticalSections[at] = depth + 1
        end
        return 1, 0
    end
    local function compareStrings(alo: number, ahi: number, blo: number, bhi: number): (number, number)
        local a, b = address(alo, ahi), address(blo, bhi)
        while true do
            local left = read(1, a)
            local right = read(1, b)
            if left ~= right or left == 0 then
                return (left - right) % 4294967296, 0
            end
            a += 1
            b += 1
        end
    end
    local function compareMemory(alo: number, ahi: number, blo: number, bhi: number,
        size: number, sizeHi: number): (number, number)
        if sizeHi ~= 0 then error("guest memory comparison exceeds the address space", 0) end
        if size == 0 then return 0, 0 end
        local a, first = locate(address(alo, ahi), size, false)
        local b, second = locate(address(blo, bhi), size, false)
        for index = 0, size - 1 do
            local lhs, rhs = buffer.readu8(a, first + index), buffer.readu8(b, second + index)
            if lhs ~= rhs then return (lhs - rhs) % 4294967296, 0 end
        end
        return 0, 0
    end
    local function stringLength(lo: number, hi: number): (number, number)
        local start = address(lo, hi)
        local cursor = start
        while read(1, cursor) ~= 0 do
            cursor += 1
        end
        return cursor - start, 0
    end
    local function copyMemory(dstLo: number, dstHi: number, srcLo: number, srcHi: number,
        size: number, sizeHi: number): (number, number)
        if sizeHi ~= 0 then
            error("guest memory copy exceeds the address space", 0)
        end
        if size ~= 0 then
            local src, srcIndex = locate(address(srcLo, srcHi), size, false)
            local dst, dstIndex = locate(address(dstLo, dstHi), size, true)
            buffer.copy(dst, dstIndex, src, srcIndex, size)
        end
        return dstLo, dstHi
    end
    local function fillMemory(lo: number, hi: number, value: number, size: number, sizeHi: number): (number, number)
        if sizeHi ~= 0 then
            error("guest memory fill exceeds the address space", 0)
        end
        if size ~= 0 then
            local bytes, index = locate(address(lo, hi), size, true)
            buffer.fill(bytes, index, bit32.band(value, 255), size)
        end
        return lo, hi
    end
    local function protectMemory(lo: number, hi: number, size: number, sizeHi: number, protection: number,
        oldLo: number, oldHi: number): number
        if hi ~= 0 or sizeHi ~= 0 or size == 0 or (protection ~= 2 and protection ~= 4) then return 0 end
        for _, range in data do
            if range.mode >= 2 and lo >= range.first and lo + size <= range.last then
                local firstPage = math.floor(lo / 4096)
                local previous = pageProtection[firstPage] or (if range.mode == 3 then 4 else 2)
                write(4, address(oldLo, oldHi), previous, 0)
                for page = firstPage, math.floor((lo + size - 1) / 4096) do
                    pageProtection[page] = protection
                end
                return 1
            end
        end
        return 0
    end
    -- Mutexes count their owner's locks, as recursive ones do (relocking any other kind is undefined). Locking one
    -- that another guest thread holds waits for it, through process.blockUntil once threads exist.
    local function pthreadMutex(op: string, lo: number, hi: number): number
        local at = address(lo, hi)
        if at == 0 then return 22 end
        locate(at, 1, false)
        local me = if process.threadId then process.threadId() else 0
        local held = pthreadLocks[at]
        if op == "pthread_mutex_unlock" then
            if not held or held.owner ~= me then return 1 end
            held.count -= 1
            if held.count == 0 then pthreadLocks[at] = nil end
            return 0
        end
        if held and held.owner == me then
            held.count += 1
            return 0
        end
        if held then
            if op == "pthread_mutex_trylock" then return 16 end
            if not process.blockUntil then error("guest locks a mutex that nothing can release", 0) end
            process.blockUntil(function() return pthreadLocks[at] == nil end)
        end
        pthreadLocks[at] = {owner = me, count = 1}
        return 0
    end
    local function srwLock(op: string, shared: boolean, lo: number, hi: number): number
        local at = address(lo, hi)
        locate(at, 8, false)
        local held = srwLocks[at] or 0
        if op == "initialize" then
            write(8, at, 0, 0)
            srwLocks[at] = nil
        elseif op == "release" then
            if (shared and held <= 0) or (not shared and held ~= -1) then
                error("guest released an unowned SRW lock", 0)
            end
            srwLocks[at] = if held > 1 then held - 1 else nil
        elseif held == 0 or (shared and held > 0) then
            srwLocks[at] = if shared then held + 1 else -1
            return 1
        elseif op ~= "try" then
            error("recursive exclusive guest SRW lock", 0)
        end
        return 0
    end
    return read, write, stackTop, reset, resize, readXmm, writeXmm, compareStrings, stringLength, copyMemory,
        fillMemory, processHeap, allocateCpp, compareMemory, criticalSection, protectMemory, cLocale, useCLocale,
        wideClass, testWideClass, pthreadMutex, srwLock, errnoAddress, readString, writeString
end
)"};

constexpr std::string_view SehOperators[] = {R"luau(
-- Windows x64 structured exception handling: what ntdll does for RaiseException and RtlUnwindEx, after
-- Wine and ReactOS. Frames are found through the image's .pdata table and unwound by interpreting
-- UNWIND_INFO. Language handlers such as __CxxFrameHandler4 are guest code that `call` runs.
-- CONTEXT keeps registers at 0x78 + 8 * index, Rip at 0xf8, and Xmm registers at 0x1a0.
-- The image's base and end, and its .pdata table, which holds RVAs. `active` records the calls into guest
-- handler code in progress, innermost last: exception handlers, termination handlers, and consolidation
-- callbacks. A frame walk that returns past one continues as Windows does: in the context of the raise, of
-- the frame being unwound, or of the frame being resumed, with the activities in `outer` still around it.
type SehActivity = {kind: string, context: number, outer: number}
local seh = {base = 0, stop = 0, table = 0, count = 0, active = {} :: {SehActivity}}
local SehContextSize = 1232
-- Return addresses of guest code the runtime calls: walks end at handler calls, and a consolidation
-- callback's caller is the frame being resumed.
local SehHandlerReturn = 4294967295
local SehConsolidateReturn = 4294967280
type GuestCall = (number, number, number, number, number, number) -> (number, any)

local function sehNew(size: number): number
    local at = resize(0, 0, size, 0)
    fillMemory(at, 0, 0, size, 0)
    return at
end

local function sehCopy(target: number, source: number)
    writeString(target, readString(source, SehContextSize))
end

local function sehRegister(context: number, index: number): number
    return (read(8, context + 0x78 + index * 8))
end

local function sehSetRegister(context: number, index: number, lo: number, hi: number?)
    write(8, context + 0x78 + index * 8, lo, hi or 0)
end

-- RtlLookupFunctionEntry: the RUNTIME_FUNCTION covering `pc`, or zero for a leaf function.
local function sehLookup(pc: number): number
    pc -= seh.base
    local low, high = 0, seh.count - 1
    while low <= high do
        local middle = (low + high) // 2
        local entry = seh.table + middle * 12
        if pc < read(4, entry) then
            high = middle - 1
        elseif pc >= read(4, entry + 4) then
            low = middle + 1
        else
            return entry
        end
    end
    return 0
end

-- RtlVirtualUnwind: turns the context of the frame running `pc` in the function of `entry` into its
-- caller's. Returns the frame's handler of `handlerType` (1 exception, 2 termination), its data, and the
-- establisher frame.
local function sehVirtualUnwind(handlerType: number, pc: number, entry: number, context: number): (number, number, number)
    local frame = sehRegister(context, 4)
    local establisher = frame
    local machineFrame = false
    local inPrologue = false
    local info = 0
    for depth = 1, 32 do
        local begin = seh.base + read(4, entry)
        info = seh.base + read(4, entry + 8)
        local codes = read(1, info + 2)
        local frameByte = read(1, info + 3)
        if bit32.band(frameByte, 15) ~= 0 then
            frame = sehRegister(context, bit32.band(frameByte, 15)) - bit32.rshift(frameByte, 4) * 16
        end
        if depth == 1 then
            establisher = frame
        end
        -- In a prologue, only the codes for instructions that already ran apply.
        local executed = math.huge
        if pc >= begin and pc < begin + read(1, info + 1) then
            executed = pc - begin
        end
        inPrologue = executed ~= math.huge
        local i = 0
        while i < codes do
            local code = info + 4 + i * 2
            local op = bit32.band(read(1, code + 1), 15)
            local opInfo = bit32.rshift(read(1, code + 1), 4)
            local slots = if op == 1 then (if opInfo == 0 then 2 else 3)
                elseif op == 4 or op == 6 or op == 8 then 2 elseif op == 5 or op == 9 then 3 else 1
            if executed >= read(1, code) then
                local rsp = sehRegister(context, 4)
                if op == 0 then
                    sehSetRegister(context, opInfo, read(8, rsp))
                    sehSetRegister(context, 4, rsp + 8)
                elseif op == 1 then
                    sehSetRegister(context, 4, rsp + (if opInfo == 0 then read(2, code + 2) * 8 else read(4, code + 2)))
                elseif op == 2 then
                    sehSetRegister(context, 4, rsp + opInfo * 8 + 8)
                elseif op == 3 then
                    sehSetRegister(context, 4, frame)
                elseif op == 4 or op == 5 then
                    sehSetRegister(context, opInfo, read(8, frame + (if op == 4 then read(2, code + 2) * 8 else read(4, code + 2))))
                elseif op == 8 or op == 9 then
                    local at = frame + (if op == 8 then read(2, code + 2) * 16 else read(4, code + 2))
                    writeString(context + 0x1a0 + opInfo * 16, readString(at, 16))
                elseif op == 10 then
                    local base = rsp + (if opInfo == 1 then 8 else 0)
                    write(8, context + 0xf8, read(8, base))
                    sehSetRegister(context, 4, read(8, base + 24))
                    machineFrame = true
                end
            end
            i += slots
        end
        -- UNW_FLAG_CHAININFO: the codes continue in the function entry that follows.
        if bit32.band(read(1, info), 0x20) == 0 then
            break
        end
        entry = info + 4 + (codes + codes % 2) * 2
    end
    if not machineFrame then
        local rsp = sehRegister(context, 4)
        write(8, context + 0xf8, read(8, rsp))
        sehSetRegister(context, 4, rsp + 8)
    end
    local flags = bit32.rshift(read(1, info), 3)
    if bit32.band(flags, handlerType) == 0 or inPrologue then
        return 0, 0, establisher
    end
    local codes = read(1, info + 2)
    local handlerAt = info + 4 + (codes + codes % 2) * 2
    return seh.base + read(4, handlerAt), handlerAt + 4, establisher
end

-- Unwinds `context` one frame, through leaf functions too. Returns the frame's handler and its data, the
-- establisher frame, and the pc and function entry the frame was running.
local function sehStep(handlerType: number, context: number): (number, number, number, number, number)
    local pc = (read(8, context + 0xf8))
    local entry = sehLookup(pc)
    if entry == 0 then
        local rsp = sehRegister(context, 4)
        write(8, context + 0xf8, read(8, rsp))
        sehSetRegister(context, 4, rsp + 8)
        return 0, 0, rsp, pc, 0
    end
    local handler, data, establisher = sehVirtualUnwind(handlerType, pc, entry, context)
    return handler, data, establisher, pc, entry
end

-- Whether `context` is a guest frame to unwind. `cursor` counts the activities around the walk's position;
-- returning into one continues in the context it records.
local function sehNextFrame(context: number, cursor: number): (boolean, number)
    local pc = (read(8, context + 0xf8))
    while (pc == SehHandlerReturn or pc == SehConsolidateReturn) and cursor >= 1 do
        local activity = seh.active[cursor]
        sehCopy(context, activity.context)
        cursor = activity.outer
        pc = (read(8, context + 0xf8))
    end
    return pc ~= 0 and pc < SehConsolidateReturn, cursor
end

local function sehCallWith(kind: string, context: number, outer: number, call: GuestCall, target: number, a: number,
    b: number, c: number, d: number, marker: number): (number, any)
    table.insert(seh.active, {kind = kind, context = context, outer = outer})
    local result, escaped = call(target, a, b, c, d, marker)
    table.remove(seh.active)
    return result, escaped
end

-- Where an unwind requested now starts, as a copy, and the activities around it. One from an exception
-- handler unwinds the frames from the raise; one from a termination handler collides with the unwind running
-- that handler and continues at its frame. Zero means the unwind starts at its caller.
local function sehUnwindStart(): (number, number)
    local top = seh.active[#seh.active]
    if top == nil or top.kind == "consolidate" then
        return 0, #seh.active
    end
    local start = sehNew(SehContextSize)
    sehCopy(start, top.context)
    return start, top.outer
end

-- DISPATCHER_CONTEXT.
local function sehDispatcher(pc: number, entry: number, establisher: number, context: number, handler: number,
    data: number, target: number): number
    local dispatcher = sehNew(80)
    write(8, dispatcher, pc, 0)
    write(8, dispatcher + 8, seh.base, 0)
    write(8, dispatcher + 16, entry, 0)
    write(8, dispatcher + 24, establisher, 0)
    write(8, dispatcher + 32, target, 0)
    write(8, dispatcher + 40, context, 0)
    write(8, dispatcher + 48, handler, 0)
    write(8, dispatcher + 56, data, 0)
    return dispatcher
end

-- RtlDispatchException. Returns nil when a handler continues execution, or what an unwind that left
-- the handler returned with: the address a frame resumes at.
local function sehRaise(record: number, context: number, call: GuestCall): any
    local work = sehNew(SehContextSize)
    sehCopy(work, context)
    local around = #seh.active
    local cursor = around
    for _ = 1, 100000 do
        local valid
        valid, cursor = sehNextFrame(work, cursor)
        if not valid then
            break
        end
        local handler, data, establisher, pc, entry = sehStep(1, work)
        if handler ~= 0 then
            local dispatcher = sehDispatcher(pc, entry, establisher, work, handler, data, 0)
            local disposition, escaped = sehCallWith("dispatch", context, around, call, handler, record, establisher,
                context, dispatcher, SehHandlerReturn)
            if escaped ~= nil or disposition == 0 then
                return escaped
            end
        end
    end
    -- No frame handled it: the filter from SetUnhandledExceptionFilter decides. MinGW's continues GCC
    -- exceptions, so the C++ runtime terminates; MSVC's terminates for C++ exceptions.
    if process.exceptionFilterLo ~= 0 then
        local pointers = sehNew(16)
        write(8, pointers, record, 0)
        write(8, pointers + 8, context, 0)
        local result, escaped = sehCallWith("dispatch", context, around, call, process.exceptionFilterLo, pointers, 0,
            0, 0, SehHandlerReturn)
        if escaped ~= nil then
            return escaped
        elseif result == 0xffffffff then
            return nil
        elseif result == 1 then
            exitProcess(read(4, record), false)
        end
    end
    error(string.format("unhandled guest exception 0x%08x", read(4, record)), 0)
end

-- RtlUnwindEx. Calls the termination handlers of the frames from `start` (or `final`, the caller's context)
-- to `targetFrame`, and leaves the target frame's context in `final`. An unwind consolidation runs its
-- callback, such as a C++ catch block, which returns where to continue. Returns that address, or what an
-- unwind that escaped returned with as the second value.
local function sehUnwind(targetFrame: number, targetIp: number, record: number, returnValue: number,
    call: GuestCall, final: number, start: number, cursor: number): (number?, any)
    local frame = sehNew(SehContextSize)
    sehCopy(frame, if start ~= 0 then start else final)
    if record == 0 then
        record = sehNew(152)
        write(4, record, 0xc0000027, 0)
        write(8, record + 16, targetIp, 0)
    end
    write(4, record + 4, bit32.bor(read(4, record + 4), if targetFrame == 0 then 6 else 2), 0)
    local caller = sehNew(SehContextSize)
    local reached = false
    for _ = 1, 100000 do
        local valid
        valid, cursor = sehNextFrame(frame, cursor)
        if not valid then
            break
        end
        sehCopy(caller, frame)
        local handler, data, establisher, pc, entry = sehStep(2, caller)
        reached = establisher == targetFrame
        if reached then
            write(4, record + 4, bit32.bor(read(4, record + 4), 0x20), 0)
        end
        if handler ~= 0 then
            -- As in Wine, the dispatcher context of an unwind holds the frame's own context, which is the one
            -- restored at the target: GCC's handler stores the landing pad's selector there.
            local dispatcher = sehDispatcher(pc, entry, establisher, frame, handler, data, targetIp)
            local _, escaped = sehCallWith("unwind", frame, cursor, call, handler, record, establisher, frame, dispatcher,
                SehHandlerReturn)
            if escaped ~= nil then
                return nil, escaped
            end
        end
        if reached then
            break
        end
        sehCopy(frame, caller)
    end
    if not reached then
        error(string.format("guest unwind did not reach frame 0x%x", targetFrame), 0)
    end
    sehCopy(final, frame)
    sehSetRegister(final, 0, returnValue)
    local resume = targetIp
    if read(4, record) == 0x80000026 and read(4, record + 24) >= 1 then
        -- STATUS_LONGJUMP: ExceptionInformation[0] is the _JUMP_BUFFER whose nonvolatile registers setjmp saved.
        local buffer = (read(8, record + 32))
        for index, offset in {[3] = 8, [4] = 16, [5] = 24, [6] = 32, [7] = 40, [12] = 48, [13] = 56, [14] = 64, [15] = 72} do
            writeString(final + 0x78 + index * 8, readString(buffer + offset, 8))
        end
        writeString(final + 0x1a0 + 6 * 16, readString(buffer + 0x60, 160))
        write(4, final + 0x34, read(4, buffer + 0x58), 0)
        write(4, final + 0x118, read(4, buffer + 0x58), 0)
    elseif read(4, record) == 0x80000029 then
        -- STATUS_UNWIND_CONSOLIDATE: ExceptionInformation[0] is the callback.
        local continuation, escaped = sehCallWith("consolidate", final, cursor, call, (read(8, record + 32)), record, 0,
            0, 0, SehConsolidateReturn)
        if escaped ~= nil then
            return nil, escaped
        end
        resume = continuation
    end
    write(8, final + 0xf8, resume, 0)
    return resume, nil
end
)luau"};

// How unwinders find frame data: glibc's _dl_find_object and dyld's _dyld_find_unwind_sections.
constexpr std::string_view UnwindLookups[] = {R"luau(
local function findUnwindObject(pcLo: number, pcHi: number): any
    if pcHi ~= 0 then
        return nil
    end
    for _, object in unwindObjects do
        if pcLo >= object.start and pcLo < object.stop then
            return object
        end
    end
    return nil
end

-- struct dl_find_object: flags, map start and end, link map, then PT_GNU_EH_FRAME.
function libc.dl_find_object(pcLo: number, pcHi: number, resultLo: number, resultHi: number): (number, number)
    local object = findUnwindObject(pcLo, pcHi)
    if object == nil or object.frameHeader == 0 then
        return 4294967295, 4294967295
    end
    local result = address(resultLo, resultHi)
    fillMemory(result, 0, 0, 96, 0)
    write(8, result + 8, object.start, 0)
    write(8, result + 16, object.stop, 0)
    write(8, result + 32, object.frameHeader, 0)
    return 0, 0
end

-- struct dyld_unwind_sections: header, __eh_frame and its size, __unwind_info and its size.
function libc.dyld_find_unwind_sections(pcLo: number, pcHi: number, infoLo: number, infoHi: number): (number, number)
    local object = findUnwindObject(pcLo, pcHi)
    if object == nil then
        return 0, 0
    end
    local info = address(infoLo, infoHi)
    write(8, info, object.header, 0)
    write(8, info + 8, object.frames, 0)
    write(8, info + 16, object.framesSize, 0)
    write(8, info + 24, object.compact, 0)
    write(8, info + 32, object.compactSize, 0)
    return 1, 0
end
)luau"};

// Host services for translated programs: arguments, standard streams, a file system, and C library I/O.
// Each libc entry takes and returns guest words as (lo, hi) pairs.
constexpr std::string_view ProcessOperators[] = {R"luau(
type FileContents = {data: buffer, size: number, inode: number, links: number}
type HostFile = {path: string, contents: FileContents, at: number, writable: boolean, readable: boolean,
    append: boolean?, directory: boolean?}

local host = {
    args = {"program"} :: {string},
    env = {} :: {string},
    stdin = "",
    stdinAt = 1,
    output = {{}, {}} :: {{string}},
    writers = {} :: {[number]: ((string) -> ())?},
    files = {} :: {[string]: FileContents},
    nextInode = 4,
    descriptors = {} :: {[number]: HostFile?},
    nextDescriptor = 3,
    streams = {} :: {[number]: number},
    eof = {} :: {[number]: boolean},
    pushback = {} :: {[number]: number},
    environment = 0,
    strings = {} :: {[string]: number},
    -- The guest sees a POSIX file system: the run's files, by absolute path, under a working directory; the
    -- directories that hold them; and the directories the guest makes. `names` keeps how the run named its files.
    cwd = "/work",
    directories = {} :: {[string]: boolean},
    names = {} :: {[string]: string},
    directoryStreams = {} :: {[number]: {path: string, entries: {{name: string, directory: boolean}}, at: number, fd: number?}},
    -- Guest threads besides the main one, which runs them while it waits (see host.block).
    threads = {} :: {any},
    current = nil :: any,
    mainThread = nil :: any,
}
host.mainThread = {id = 0x1000, main = true, keys = {}, finished = false}
host.current = host.mainThread
process.threadId = function() return host.current.id end

-- An absolute path without "." or ".." components, repeated slashes, or a trailing slash. The empty path names
-- nothing (ENOENT), so it stays empty.
function host.canonical(path: string): string
    if path == "" then return "" end
    if string.sub(path, 1, 1) ~= "/" then path = host.cwd .. "/" .. path end
    local parts = {}
    for part in string.gmatch(path, "[^/]+") do
        if part == ".." then
            if #parts > 0 then table.remove(parts) end
        elseif part ~= "." then
            table.insert(parts, part)
        end
    end
    return "/" .. table.concat(parts, "/")
end

function host.parent(path: string): string
    local parent = string.match(path, "^(.*)/[^/]*$") or ""
    return if parent == "" then "/" else parent
end

function host.isDirectory(path: string): boolean
    if path == "" then return false end
    if path == "/" or host.directories[path] then return true end
    if host.files[path] then return false end
    local prefix = path .. "/"
    for name in host.files do
        if string.sub(name, 1, #prefix) == prefix then return true end
    end
    return false
end

-- A directory's entries, sorted by name: its files, and the directories below it.
function host.children(path: string): {{name: string, directory: boolean}}
    local prefix = if path == "/" then "/" else path .. "/"
    local found: {[string]: boolean} = {}
    local function visit(name: string, directory: boolean)
        if string.sub(name, 1, #prefix) ~= prefix or #name == #prefix then return end
        local rest = string.sub(name, #prefix + 1)
        local first = string.match(rest, "^[^/]+") :: string
        found[first] = found[first] or directory or #first < #rest
    end
    for name in host.files do visit(name, false) end
    for name in host.directories do visit(name, true) end
    local entries = {}
    for name, directory in found do table.insert(entries, {name = name, directory = directory}) end
    table.sort(entries, function(a, b) return a.name < b.name end)
    return entries
end

function host.newFile(text: string): FileContents
    local inode = host.nextInode
    host.nextInode += 1
    return {data = buffer.fromstring(text), size = #text, inode = inode, links = 1}
end

-- The run's files enter under their canonical paths; the result names them as the run did, or relative to the
-- working directory.
function host.load(files: {[string]: string}?, cwd: string?)
    host.cwd = "/"
    host.cwd = host.canonical(cwd or "/work")
    host.files, host.names, host.directories = {}, {}, {}
    -- Directories exist apart from the files in them: they stay when emptied, until removed.
    local function hold(path: string)
        while path ~= "/" and not host.directories[path] do
            host.directories[path] = true
            path = host.parent(path)
        end
    end
    for name, text in files or {} do
        local path = host.canonical(name)
        host.files[path] = host.newFile(text)
        host.names[path] = name
        hold(host.parent(path))
    end
    hold(host.cwd)
    -- Every POSIX system has a directory for temporary files, as tmpfile, tmpnam, and mkstemp callers expect.
    hold("/tmp")
end

function host.results(): {[string]: string}
    local results = {}
    local prefix = if host.cwd == "/" then "/" else host.cwd .. "/"
    for path, contents in host.files do
        local name = host.names[path]
        if not name then
            name = if string.sub(path, 1, #prefix) == prefix then string.sub(path, #prefix + 1) else path
        end
        results[name] = buffer.readstring(contents.data, 0, contents.size)
    end
    return results
end

local function exitProcess(status: number, callbacks: boolean)
    if callbacks then
        while #process.exitCallbacks > 0 do
            local callback = table.remove(process.exitCallbacks)
            if callback then callback() end
        end
    end
    error({luftExit = status % 256}, 0)
end

local function hostWrite(fd: number, text: string): boolean
    if fd == 1 or fd == 2 then
        local writer = host.writers[fd]
        if writer then writer(text) else table.insert(host.output[fd], text) end
        return true
    end
    local file = host.descriptors[fd]
    if not file or not file.writable then return false end
    if #text == 0 then return true end
    local contents = file.contents
    local at = if file.append then contents.size else file.at
    local finish = at + #text
    if finish > buffer.len(contents.data) then
        local grown = buffer.create(math.max(finish, buffer.len(contents.data) * 2, 64))
        buffer.copy(grown, 0, contents.data, 0, contents.size)
        contents.data = grown
    end
    buffer.writestring(contents.data, at, text)
    file.at = finish
    contents.size = math.max(contents.size, finish)
    return true
end

local function hostRead(fd: number, count: number): string?
    if fd == 0 then
        local text = string.sub(host.stdin, host.stdinAt, host.stdinAt + count - 1)
        host.stdinAt += #text
        return text
    end
    local file = host.descriptors[fd]
    if not file or not file.readable then return nil end
    local contents = file.contents
    if file.at >= contents.size then return "" end
    local available = math.min(count, contents.size - file.at)
    local text = buffer.readstring(contents.data, file.at, available)
    file.at += available
    return text
end

-- A descriptor for `path`, or nil and the errno value (ENOENT, EEXIST, EISDIR, or ENOTDIR).
local function hostOpen(path: string, readable: boolean, writable: boolean, create: boolean, truncate: boolean,
    append: boolean, exclusive: boolean?): (number?, number)
    path = host.canonical(path)
    if path == "" then return nil, 2 end
    local existing = host.files[path]
    if not existing and host.isDirectory(path) then
        if writable then return nil, 21 end
        local fd = host.nextDescriptor
        host.nextDescriptor += 1
        -- A directory's descriptor seeks over its size (stat's) but cannot be read (EISDIR).
        host.descriptors[fd] = {path = path,
            contents = {data = buffer.create(0), size = 4096, inode = host.inode(path), links = 1}, at = 0, writable = false,
            readable = false, directory = true}
        return fd, 0
    end
    if existing and create and exclusive then return nil, 17 end
    if not existing then
        if not create then return nil, 2 end
        local parent = host.parent(path)
        if not host.isDirectory(parent) then return nil, if host.files[parent] then 20 else 2 end
        existing = host.newFile("")
        host.files[path] = existing
    elseif truncate then
        existing.data = buffer.create(0)
        existing.size = 0
    end
    local fd = host.nextDescriptor
    host.nextDescriptor += 1
    host.descriptors[fd] = {path = path, contents = existing, at = if append then existing.size else 0,
        writable = writable, readable = readable, append = append}
    return fd, 0
end

local function hostClose(fd: number): boolean
    local file = host.descriptors[fd]
    if not file then return fd >= 0 and fd <= 2 end
    host.descriptors[fd] = nil
    return true
end

local function hostSeek(fd: number, offset: number, whence: number): number?
    local file = host.descriptors[fd]
    if not file then return nil end
    local base = if whence == 0 then 0 elseif whence == 1 then file.at else file.contents.size
    local position = base + offset
    if position < 0 then return nil end
    file.at = position
    return position
end

local function signed32(lo: number): number
    return if lo >= 2147483648 then lo - 4294967296 else lo
end

local function signed64(lo: number, hi: number): number
    return if hi >= 2147483648 then (hi - 4294967296) * 4294967296 + lo else hi * 4294967296 + lo
end

-- A NUL-terminated guest string, or at most `limit` bytes of one: printf's %.*s and strncpy take arrays that need
-- no terminator, so a bounded read never looks past the limit.
local function guestString(at: number, limit: number?): string
    if limit then
        local length = 0
        while length < limit and read(1, at + length) ~= 0 do
            length += 1
        end
        return readString(at, length)
    end
    return readString(at, stringLength(at, 0))
end

local function newGuestString(text: string): number
    local at = resize(0, 0, #text + 1, 0)
    if at == 0 then error("guest heap exhausted", 0) end
    writeString(at, text)
    write(1, at + #text, 0, 0)
    return at
end

local function cachedString(text: string): number
    local at = host.strings[text]
    if not at then
        at = newGuestString(text)
        host.strings[text] = at
    end
    return at
end

local function digitsOf(lo: number, hi: number, base: number, upper: boolean): string
    if hi == 0 then
        if base == 10 then return string.format("%d", lo) end
        if base == 16 then return string.format(if upper then "%X" else "%x", lo) end
        if base == 8 then return string.format("%o", lo) end
    end
    local alphabet = if upper then "0123456789ABCDEF" else "0123456789abcdef"
    local digits = {}
    while hi ~= 0 or lo ~= 0 do
        local high = hi % base
        hi = (hi - high) / base
        local value = high * 4294967296 + lo
        local digit = value % base
        lo = (value - digit) / base
        table.insert(digits, string.sub(alphabet, digit + 1, digit + 1))
    end
    if #digits == 0 then return "0" end
    local text = table.concat(digits)
    return string.reverse(text)
end

local function padded(text: string, width: number?, left: boolean, zero: boolean, prefix: string): string
    width = width or 0
    local length = #text + #prefix
    if length >= width then return prefix .. text end
    if left then return prefix .. text .. string.rep(" ", width - length) end
    if zero then return prefix .. string.rep("0", width - length) .. text end
    return string.rep(" ", width - length) .. prefix .. text
end

)luau", R"luau(
-- The exact decimal expansion of a finite, positive double, which every double has: its digits, without leading
-- zeros, and where the decimal point lies relative to them. Limbs hold seven digits each, least significant first.
local function exactDecimal(value: number): (string, number)
    local mantissa, exponent = math.frexp(value)
    mantissa *= 2 ^ 53
    exponent -= 53
    local limbs = {}
    while mantissa > 0 do
        local limb = mantissa % 10000000
        table.insert(limbs, limb)
        mantissa = (mantissa - limb) / 10000000
    end
    local function scale(factor: number)
        local carry = 0
        for i = 1, #limbs do
            local product = limbs[i] * factor + carry
            local limb = product % 10000000
            limbs[i] = limb
            carry = (product - limb) / 10000000
        end
        while carry > 0 do
            local limb = carry % 10000000
            table.insert(limbs, limb)
            carry = (carry - limb) / 10000000
        end
    end
    -- value = mantissa * 2^exponent; a negative exponent makes it mantissa * 5^-exponent / 10^-exponent.
    -- Factors stay below 2^26 (or 5^12) so that each product is exact.
    local remaining = math.abs(exponent)
    while remaining > 0 do
        local step = math.min(remaining, if exponent > 0 then 26 else 12)
        scale(if exponent > 0 then 2 ^ step else 5 ^ step)
        remaining -= step
    end
    local parts = {tostring(limbs[#limbs])}
    for i = #limbs - 1, 1, -1 do
        table.insert(parts, string.format("%07d", limbs[i]))
    end
    local digits = table.concat(parts)
    return digits, #digits + math.min(exponent, 0)
end

-- Keeps the first `count` digits, rounded to nearest with ties to even; `count` may be negative or exceed the
-- digits. Returns exactly max(count, 0) digits, or one more when rounding carries, and the new point.
local function roundDigits(digits: string, point: number, count: number): (string, number)
    if count >= #digits then
        return digits .. string.rep("0", count - #digits), point
    elseif count < 0 then
        return "", point
    end
    local kept = string.sub(digits, 1, count)
    local following = string.byte(digits, count + 1) - 48
    local odd = count > 0 and (string.byte(digits, count) - 48) % 2 == 1
    if following < 5 or (following == 5 and not odd and not string.find(digits, "[1-9]", count + 2)) then
        return kept, point
    end
    local last = count
    while last > 0 and string.byte(kept, last) == 57 do
        last -= 1
    end
    if last == 0 then
        return "1" .. string.rep("0", count), point + 1
    end
    return string.sub(kept, 1, last - 1) .. string.char(string.byte(kept, last) + 1) .. string.rep("0", count - last), point
end

-- printf's %f, %e, and %g of a finite, non-negative value, digit by digit: Luau's string.format takes precisions
-- of at most two digits.
local function exactFloat(value: number, conversion: string, precision: number, alternate: boolean): string
    local digits, point = "", 1
    if value > 0 then
        digits, point = exactDecimal(value)
    end
    local function fixed(places: number): string
        local kept, at = roundDigits(digits, point, point + places)
        local whole, fraction
        if at > 0 then
            whole, fraction = string.sub(kept, 1, at), string.sub(kept, at + 1)
        else
            whole, fraction = "0", string.sub(string.rep("0", -at) .. kept, 1, places)
        end
        if whole == "" then whole = "0" end
        fraction ..= string.rep("0", places - #fraction)
        return whole .. (if places > 0 or alternate then "." else "") .. fraction
    end
    local function scientific(places: number): (string, number)
        if value == 0 then
            return "0" .. (if places > 0 or alternate then "." else "") .. string.rep("0", places), 0
        end
        local kept, at = roundDigits(digits, point, places + 1)
        local mantissa = string.sub(kept, 1, 1) .. (if places > 0 or alternate then "." else "") ..
            string.sub(kept, 2, places + 1)
        return mantissa, at - 1
    end
    local function exponentText(exponent: number): string
        return string.format("e%s%02d", if exponent < 0 then "-" else "+", math.abs(exponent))
    end
    if conversion == "f" then
        return fixed(precision)
    elseif conversion == "e" then
        local mantissa, exponent = scientific(precision)
        return mantissa .. exponentText(exponent)
    end
    local significant = if precision == 0 then 1 else precision
    local _, exponent = scientific(significant - 1)
    local text
    if exponent < significant and exponent >= -4 then
        text = fixed(significant - 1 - exponent)
    else
        local mantissa
        mantissa, exponent = scientific(significant - 1)
        text = mantissa
    end
    if not alternate and string.find(text, ".", 1, true) then
        text = string.gsub(string.gsub(text, "0+$", ""), "%.$", "")
    end
    if exponent < significant and exponent >= -4 then
        return text
    end
    return text .. exponentText(exponent)
end

-- printf's %a of a finite, non-negative value as glibc writes it: a leading 1 (0 for zero and subnormals), the
-- fraction's hex digits without trailing zeros unless a precision rounds or pads them, and a binary exponent.
-- %a's digits after "0x". glibc writes a subnormal as 0x0.<fraction>p-1022; Darwin (`normalize`) shifts its
-- leading one bit into the integer digit, as for normal numbers.
local function hexFloat(value: number, precision: number?, alternate: boolean, normalize: boolean): string
    local lo, hi = encodeFloat(8, value)
    local biased = bit32.extract(hi, 20, 11)
    local fraction = bit32.band(hi, 0xfffff) * 4294967296 + lo
    local leading = if biased == 0 then 0 else 1
    local exponent = if value == 0 then 0 elseif biased == 0 then -1022 else biased - 1023
    if normalize and biased == 0 and fraction ~= 0 then
        while fraction < 2 ^ 52 do
            fraction *= 2
            exponent -= 1
        end
        fraction -= 2 ^ 52
        leading = 1
    end
    local digits = string.format("%05x%08x", fraction // 4294967296, fraction % 4294967296)
    if precision and precision < 13 then
        local dropped = 2 ^ (4 * (13 - precision))
        local kept = fraction // dropped
        local rest = fraction - kept * dropped
        if rest > dropped / 2 or (rest == dropped / 2 and kept % 2 == 1) then
            kept += 1
        end
        if kept >= 2 ^ (4 * precision) then
            leading += 1
            kept = 0
        end
        digits = if precision > 0 then string.format("%0" .. precision .. "x", kept) else ""
    elseif precision then
        digits ..= string.rep("0", precision - 13)
    else
        digits = string.gsub(digits, "0+$", "")
    end
    return string.format("%d%s%sp%s%d", leading, if digits ~= "" or alternate then "." else "", digits,
        if exponent < 0 then "-" else "+", math.abs(exponent))
end

-- printf's long double arguments as doubles: x86-64 System V passes the x87 80-bit format (a 64-bit mantissa
-- with an explicit integer bit, then sign and exponent), AArch64 Linux IEEE quad precision (`quad`; words least
-- significant first). Digits beyond a double's precision, and magnitudes beyond its range, are lost.
local function decodeLongDouble(quad: boolean, w0: number, w1: number, w2: number, w3: number): number
    local top = if quad then bit32.rshift(w3, 16) else bit32.band(w2, 0xffff)
    local sign = if top >= 32768 then -1 else 1
    local exponent = top % 32768
    local mantissa, bits
    if quad then
        mantissa = (bit32.band(w3, 0xffff) * 4294967296 + w2) * 4294967296 + w1
        bits = 80
        if exponent == 32767 then
            if mantissa == 0 and w0 == 0 then return sign * math.huge end
            return decodeFloat(8, 0, if sign < 0 then 0xfff80000 else 0x7ff80000)
        end
        if exponent ~= 0 then mantissa += 2 ^ 80 end
    else
        mantissa = w1 * 4294967296 + w0
        bits = 63
        if exponent == 32767 then
            if w1 % 2147483648 == 0 and w0 == 0 then return sign * math.huge end
            return decodeFloat(8, 0, if sign < 0 then 0xfff80000 else 0x7ff80000)
        end
    end
    return sign * math.ldexp(mantissa, math.max(exponent, 1) - 16383 - bits)
end

-- nextLong reads a long double, which is a double on Darwin arm64 and Windows.
type Arguments = {nextInt: () -> (number, number), nextFloat: () -> number, nextLong: () -> number}
)luau", R"luau(
-- Formats a C format string for a platform: 0 glibc, 1 Windows (where `long` is 32 bits wide), 2 Darwin.
local function formatGuest(format: string, arguments: Arguments, platform: number): string
    local out = {}
    local i, n = 1, #format
    local written = 0
    while i <= n do
        local percent = string.find(format, "%", i, true)
        if not percent then
            table.insert(out, string.sub(format, i))
            break
        end
        if percent > i then
            table.insert(out, string.sub(format, i, percent - 1))
            written += percent - i
        end
        local j = percent + 1
        local flags = ""
        while j <= n do
            local c = string.sub(format, j, j)
            if c == "-" or c == "+" or c == " " or c == "#" or c == "0" or c == "'" then
                flags ..= c
                j += 1
            else
                break
            end
        end
        local width: number? = nil
        if string.sub(format, j, j) == "*" then
            local w = signed32((arguments.nextInt()))
            if w < 0 then flags ..= "-"; w = -w end
            width = w
            j += 1
        else
            local digits = string.match(format, "^%d+", j)
            if digits then width = tonumber(digits); j += #digits end
        end
        local precision: number? = nil
        if string.sub(format, j, j) == "." then
            j += 1
            if string.sub(format, j, j) == "*" then
                local p = signed32((arguments.nextInt()))
                precision = if p >= 0 then p else nil
                j += 1
            else
                local digits = string.match(format, "^%d+", j) or ""
                precision = tonumber(digits) or 0
                j += #digits
            end
        end
        local length = ""
        if string.sub(format, j, j + 2) == "I64" then length = "ll"; j += 3
        elseif string.sub(format, j, j + 2) == "I32" then j += 3
        else
            length = string.match(format, "^hh", j) or string.match(format, "^ll", j) or string.match(format, "^[hljztLqI]", j) or ""
            j += #length
        end
        local conversion = string.sub(format, j, j)
        j += 1
        local left = string.find(flags, "-", 1, true) ~= nil
        local zero = string.find(flags, "0", 1, true) ~= nil and not left
        local text = ""
        if conversion == "%" then
            text = "%"
        elseif conversion == "d" or conversion == "i" or conversion == "u" or conversion == "x" or conversion == "X" or
            conversion == "o" then
            local lo, hi = arguments.nextInt()
            local wide = length == "ll" or length == "j" or length == "z" or length == "t" or length == "q" or
                (length == "l" and platform ~= 1) or length == "I"
            local signed = conversion == "d" or conversion == "i"
            if not wide then
                if length == "hh" then lo = lo % 256 elseif length == "h" then lo = lo % 65536 end
                local bits = if length == "hh" then 8 elseif length == "h" then 16 else 32
                hi = 0
                if signed and lo >= 2 ^ (bits - 1) then
                    lo = (lo - 2 ^ bits) % 4294967296
                    hi = 4294967295
                end
            end
            local negative = signed and hi >= 2147483648
            if negative then
                lo, hi = (-lo) % 4294967296, (-hi - (if lo == 0 then 0 else 1)) % 4294967296
            end
            local base = if conversion == "x" or conversion == "X" then 16 elseif conversion == "o" then 8 else 10
            local digits = digitsOf(lo, hi, base, conversion == "X")
            if precision then
                if precision == 0 and digits == "0" then digits = "" end
                if #digits < precision then digits = string.rep("0", precision - #digits) .. digits end
                zero = false
            end
            local prefix = if negative then "-" elseif signed and string.find(flags, "+", 1, true) then "+"
                elseif signed and string.find(flags, " ", 1, true) then " " else ""
            if string.find(flags, "#", 1, true) and (lo ~= 0 or hi ~= 0) then
                if base == 16 then prefix = if conversion == "X" then "0X" else "0x"
                elseif base == 8 and string.sub(digits, 1, 1) ~= "0" then digits = "0" .. digits end
            end
            text = padded(digits, width, left, zero, prefix)
        elseif conversion == "c" then
            local lo = arguments.nextInt()
            text = padded(string.char(lo % 256), width, left, false, "")
        elseif conversion == "s" then
            local lo, hi = arguments.nextInt()
            local value = if lo == 0 and hi == 0 then "(null)" else guestString(address(lo, hi), precision)
            text = padded(value, width, left, false, "")
        elseif conversion == "p" then
            -- glibc writes a null pointer as (nil); msvcrt writes sixteen uppercase digits without 0x.
            local lo, hi = arguments.nextInt()
            if platform == 1 then
                text = padded(string.format("%08X%08X", hi, lo), width, left, false, "")
            elseif platform == 0 and lo == 0 and hi == 0 then
                text = padded("(nil)", width, left, false, "")
            else
                text = padded(digitsOf(lo, hi, 16, false), width, left, false, "0x")
            end
        elseif conversion == "n" then
            local lo, hi = arguments.nextInt()
            write(4, address(lo, hi), written % 4294967296, 0)
        elseif string.find("fFeEgGaA", conversion, 1, true) then
            local value = if length == "L" then arguments.nextLong() else arguments.nextFloat()
            local upper = string.find("FEGA", conversion, 1, true) ~= nil
            local _, signWord = encodeFloat(8, value)
            local prefix = if signWord >= 2147483648 then "-" elseif string.find(flags, "+", 1, true) then "+"
                elseif string.find(flags, " ", 1, true) then " " else ""
            local alternate = string.find(flags, "#", 1, true) ~= nil
            local magnitude = math.abs(value)
            if value ~= value or magnitude == math.huge then
                -- Darwin's printf writes no sign for a NaN.
                if value ~= value and platform == 2 then prefix = "" end
                text = padded(if value ~= value then "nan" else "inf", width, left, false, prefix)
            elseif conversion == "a" or conversion == "A" then
                -- Zero padding goes after the 0x.
                text = padded(hexFloat(magnitude, precision, alternate, platform == 2), width, left, zero, prefix .. "0x")
            elseif (precision or 6) <= 99 then
                -- The sign and the field width are added here: Luau's string.format takes at most two digits of width.
                local spec = "%" .. (if alternate then "#" else "") .. (if precision then "." .. precision else "") ..
                    (if conversion == "F" then "f" else conversion)
                text = padded(string.format(spec, magnitude), width, left, zero, prefix)
            else
                text = padded(exactFloat(magnitude, string.lower(conversion), precision :: number, alternate), width,
                    left, zero, prefix)
            end
            if upper then text = string.upper(text) end
        else
            text = string.sub(format, percent, j - 1)
        end
        table.insert(out, text)
        written += #text
        i = j
    end
    return table.concat(out)
end
)luau", R"luau(
-- Variadic arguments. Kinds: 0 System V x86-64, 1 AAPCS64, 2 Darwin arm64, 3 Windows x64.
local function registerArguments(kind: number, sp: number, ints: {number}, intIndex: number, floats: {number},
    floatIndex: number): Arguments
    local stack = sp
    local function fromStack(): (number, number)
        local lo, hi = read(8, stack)
        stack += 8
        return lo, hi
    end
    local function nextInt(): (number, number)
        if kind == 2 then return fromStack() end
        if kind == 3 then
            local index = intIndex
            intIndex += 1
            if index < 4 then return ints[index * 2 + 1], ints[index * 2 + 2] end
            local lo, hi = read(8, sp + 32 + (index - 4) * 8)
            return lo, hi
        end
        if intIndex * 2 < #ints then
            local index = intIndex
            intIndex += 1
            return ints[index * 2 + 1], ints[index * 2 + 2]
        end
        return fromStack()
    end
    local function nextFloat(): number
        if kind == 2 then return decodeFloat(8, fromStack()) end
        if kind == 3 then return decodeFloat(8, nextInt()) end
        if floatIndex < 8 then
            local index = floatIndex
            floatIndex += 1
            return decodeFloat(8, floats[index * 4 + 1], floats[index * 4 + 2])
        end
        return decodeFloat(8, fromStack())
    end
    local function nextLong(): number
        if kind == 0 or kind == 1 then
            if kind == 1 and floatIndex < 8 then
                local index = floatIndex
                floatIndex += 1
                return decodeLongDouble(true, floats[index * 4 + 1], floats[index * 4 + 2], floats[index * 4 + 3],
                    floats[index * 4 + 4])
            end
            -- In memory, 16-byte aligned.
            stack = (stack + 15) // 16 * 16
            local w0, w1 = read(8, stack)
            local w2, w3 = read(8, stack + 8)
            stack += 16
            return decodeLongDouble(kind == 1, w0, w1, w2, w3)
        end
        return nextFloat()
    end
    return {nextInt = nextInt, nextFloat = nextFloat, nextLong = nextLong}
end

-- A va_list argument for the same ABI kinds.
local function listArguments(kind: number, lo: number, hi: number): Arguments
    local at = address(lo, hi)
    if kind == 0 then
        local gp, fp = read(4, at), read(4, at + 4)
        local overflow = address(read(8, at + 8))
        local save = address(read(8, at + 16))
        local function nextInt(): (number, number)
            if gp < 48 then
                local a, b = read(8, save + gp)
                gp += 8
                return a, b
            end
            local a, b = read(8, overflow)
            overflow += 8
            return a, b
        end
        local function nextFloat(): number
            if fp < 176 then
                local a, b = read(8, save + fp)
                fp += 16
                return decodeFloat(8, a, b)
            end
            local a, b = read(8, overflow)
            overflow += 8
            return decodeFloat(8, a, b)
        end
        local function nextLong(): number
            overflow = (overflow + 15) // 16 * 16
            local w0, w1 = read(8, overflow)
            local w2 = read(4, overflow + 8)
            overflow += 16
            return decodeLongDouble(false, w0, w1, w2, 0)
        end
        return {nextInt = nextInt, nextFloat = nextFloat, nextLong = nextLong}
    elseif kind == 1 then
        local stack = address(read(8, at))
        local grTop, vrTop = address(read(8, at + 8)), address(read(8, at + 16))
        local grOffs, vrOffs = signed32((read(4, at + 24))), signed32((read(4, at + 28)))
        local function nextInt(): (number, number)
            if grOffs < 0 then
                local a, b = read(8, grTop + grOffs)
                grOffs += 8
                return a, b
            end
            local a, b = read(8, stack)
            stack += 8
            return a, b
        end
        local function nextFloat(): number
            if vrOffs < 0 then
                local a, b = read(8, vrTop + vrOffs)
                vrOffs += 16
                return decodeFloat(8, a, b)
            end
            local a, b = read(8, stack)
            stack += 8
            return decodeFloat(8, a, b)
        end
        local function nextLong(): number
            local at = 0
            if vrOffs < 0 then
                at = vrTop + vrOffs
                vrOffs += 16
            else
                stack = (stack + 15) // 16 * 16
                at = stack
                stack += 16
            end
            local w0, w1 = read(8, at)
            local w2, w3 = read(8, at + 8)
            return decodeLongDouble(true, w0, w1, w2, w3)
        end
        return {nextInt = nextInt, nextFloat = nextFloat, nextLong = nextLong}
    end
    local cursor = at
    local function nextInt(): (number, number)
        local a, b = read(8, cursor)
        cursor += 8
        return a, b
    end
    local function nextFloat(): number return decodeFloat(8, nextInt()) end
    return {nextInt = nextInt, nextFloat = nextFloat, nextLong = nextFloat}
end

-- Places the program's arguments and environment in guest memory.
local function processArguments(): (number, number, number)
    local function vector(strings: {string}): number
        local at = resize(0, 0, (#strings + 1) * 8, 0)
        for i, text in strings do
            write(8, at + (i - 1) * 8, newGuestString(text), 0)
        end
        write(8, at + #strings * 8, 0, 0)
        return at
    end
    local argv = vector(host.args)
    host.environment = vector(host.env)
    return #host.args, argv, host.environment
end

-- Builds the System V initial stack below `top`: argc, argv, NULL, envp, NULL, and an empty auxiliary vector.
local function processStack(top: number, argc: number, argv: number, envp: number): number
    local words = 1 + (argc + 1) + (#host.env + 1) + 2
    local sp = top - 256 - words * 8
    sp -= sp % 16
    local at = sp
    write(8, at, argc, 0)
    at += 8
    for i = 0, argc do
        write(8, at, read(8, argv + i * 8))
        at += 8
    end
    for i = 0, #host.env do
        write(8, at, read(8, envp + i * 8))
        at += 8
    end
    write(8, at, 0, 0)
    write(8, at + 8, 0, 0)
    return sp
end

local libc = {}
-- Platform details: Darwin and Linux differ in open() flags and struct stat.
libc.darwin = false
libc.windows = false
libc.arm = false

local function streamDescriptor(lo: number, hi: number): number
    local fd = host.streams[address(lo, hi)]
    if fd == nil then error("unknown guest FILE stream", 0) end
    return fd
end

local function result(value: number): (number, number)
    if value < 0 then return value % 4294967296, 4294967295 end
    return value % 4294967296, math.floor(value / 4294967296)
end

local function setErrno(code: number)
    write(4, errnoAddress(), code, 0)
end

function libc.write(fdLo, fdHi, bufLo, bufHi, countLo, countHi)
    local text = readString(address(bufLo, bufHi), address(countLo, countHi))
    if not hostWrite(signed32(fdLo), text) then setErrno(9); return result(-1) end
    return result(#text)
end

function libc.read(fdLo, fdHi, bufLo, bufHi, countLo, countHi)
    local text = hostRead(signed32(fdLo), address(countLo, countHi))
    if not text then
        local file = host.descriptors[signed32(fdLo)]
        setErrno(if file and file.directory then 21 else 9)
        return result(-1)
    end
    writeString(address(bufLo, bufHi), text)
    return result(#text)
end

-- open()'s access mode and flags, which Darwin and Linux (whose ARM64 O_DIRECTORY differs) number differently.
local function openFlags(flags: number): (boolean, boolean, boolean, boolean, boolean, boolean, boolean)
    local access = flags % 4
    local create = bit32.btest(flags, if libc.darwin then 0x200 else 0x40)
    local truncate = bit32.btest(flags, if libc.darwin then 0x400 else 0x200)
    local append = bit32.btest(flags, if libc.darwin then 0x8 else 0x400)
    local exclusive = bit32.btest(flags, if libc.darwin then 0x800 else 0x80)
    local directory = bit32.btest(flags, if libc.darwin then 0x100000 elseif libc.arm then 0x4000 else 0x10000)
    return access ~= 1, access ~= 0, create, truncate, append, exclusive, directory
end

-- errno values that Darwin and Linux number differently.
function host.errno(name: string): number
    local darwin = libc.darwin
    if name == "ENOTEMPTY" then return if darwin then 66 else 39 end
    if name == "ENOSYS" then return if darwin then 78 else 38 end
    if name == "EAGAIN" then return if darwin then 35 else 11 end
    if name == "ETIMEDOUT" then return if darwin then 60 else 110 end
    if name == "ENOTSUP" then return if darwin then 45 else 95 end
    if name == "ELOOP" then return if darwin then 62 else 40 end
    error("unknown errno " .. name, 0)
end

-- Why a canonical path that does not exist is missing: ENOTDIR when a component leading to it is a file.
function host.missing(path: string): number
    local parent = host.parent(path)
    while parent ~= "/" do
        if host.files[parent] then return 20 end
        parent = host.parent(parent)
    end
    return 2
end

-- A path relative to a directory descriptor, or to the working directory for AT_FDCWD.
function host.at(dirfd: number, path: string): string?
    if string.sub(path, 1, 1) == "/" or dirfd == (if libc.darwin then -2 else -100) then return host.canonical(path) end
    local file = host.descriptors[dirfd]
    if not file or not file.directory then return nil end
    return host.canonical(file.path .. "/" .. path)
end

function host.openPath(path: string, flags: number): (number, number)
    local readable, writable, create, truncate, append, exclusive, directory = openFlags(flags)
    if directory and not host.isDirectory(host.canonical(path)) then
        setErrno(if host.files[host.canonical(path)] then 20 else 2)
        return result(-1)
    end
    local fd, failure = hostOpen(path, readable, writable, create, truncate, append, exclusive)
    if not fd then setErrno(failure); return result(-1) end
    return result(fd)
end

function libc.open(pathLo, pathHi, flagsLo, flagsHi)
    return host.openPath(guestString(address(pathLo, pathHi)), flagsLo)
end

function libc.openat(dirLo, dirHi, pathLo, pathHi, flagsLo, flagsHi)
    local path = host.at(signed32(dirLo), guestString(address(pathLo, pathHi)))
    if not path then setErrno(9); return result(-1) end
    return host.openPath(path, flagsLo)
end

function libc.close(fdLo, fdHi)
    local fd = signed32(fdLo)
    if hostClose(fd) then return result(0) end
    setErrno(9)
    return result(-1)
end

function libc.lseek(fdLo, fdHi, offsetLo, offsetHi, whenceLo, whenceHi)
    local position = hostSeek(signed32(fdLo), signed64(offsetLo, offsetHi), whenceLo)
    if not position then setErrno(29); return result(-1) end
    return result(position)
end

-- struct stat for a regular file, a directory, or a character device (the standard streams), in the layout of
-- Darwin's 64-bit inode stat or Linux's on x86-64 or ARM64.
local function writeStat(at: number, kind: string, size: number, inode: number, links: number?)
    local mode = if kind == "file" then 0x81a4 elseif kind == "directory" then 0x41ed else 0x2190
    local blocks = math.ceil(size / 512)
    if libc.darwin then
        fillMemory(at, 0, 0, 144, 0)
        write(4, at, 1, 0)
        write(2, at + 4, mode, 0)
        write(2, at + 6, links or 1, 0)
        write(8, at + 8, inode, 0)
        write(8, at + 96, result(size))
        write(8, at + 104, result(blocks))
        write(4, at + 112, 4096, 0)
    elseif libc.arm then
        fillMemory(at, 0, 0, 128, 0)
        write(8, at, 1, 0)
        write(8, at + 8, inode, 0)
        write(4, at + 16, mode, 0)
        write(4, at + 20, links or 1, 0)
        write(8, at + 48, result(size))
        write(4, at + 56, 4096, 0)
        write(8, at + 64, result(blocks))
    else
        fillMemory(at, 0, 0, 144, 0)
        write(8, at, 1, 0)
        write(8, at + 8, inode, 0)
        write(8, at + 16, links or 1, 0)
        write(4, at + 24, mode, 0)
        write(8, at + 48, result(size))
        write(8, at + 56, 4096, 0)
        write(8, at + 64, result(blocks))
    end
end

function host.inode(path: string): number
    local contents = host.files[path]
    if contents then return contents.inode end
    host.inodes = host.inodes or {}
    local inodes = host.inodes :: {[string]: number}
    if not inodes[path] then
        inodes[path] = host.nextInode
        host.nextInode += 1
    end
    return inodes[path]
end

-- Fills `at` for an existing path and returns 0, or sets errno and returns -1.
function host.statPath(path: string, at: number): (number, number)
    local contents = host.files[path]
    if contents then
        writeStat(at, "file", contents.size, contents.inode, contents.links)
    elseif host.isDirectory(path) then
        writeStat(at, "directory", 4096, host.inode(path))
    else
        setErrno(host.missing(path))
        return result(-1)
    end
    return result(0)
end

function libc.fstat(fdLo, fdHi, statLo, statHi)
    local fd = signed32(fdLo)
    local file = host.descriptors[fd]
    if fd >= 0 and fd <= 2 and not file then
        writeStat(address(statLo, statHi), "device", 0, fd + 1)
        return result(0)
    end
    if not file then setErrno(9); return result(-1) end
    writeStat(address(statLo, statHi), if file.directory then "directory" else "file",
        file.contents.size, file.contents.inode, file.contents.links)
    return result(0)
end

function libc.stat(pathLo, pathHi, statLo, statHi)
    return host.statPath(host.canonical(guestString(address(pathLo, pathHi))), address(statLo, statHi))
end

function libc.fstatat(dirLo, dirHi, pathLo, pathHi, statLo, statHi)
    local name = guestString(address(pathLo, pathHi))
    -- AT_EMPTY_PATH: the descriptor itself.
    if name == "" then return libc.fstat(dirLo, dirHi, statLo, statHi) end
    local path = host.at(signed32(dirLo), name)
    if not path then setErrno(9); return result(-1) end
    return host.statPath(path, address(statLo, statHi))
end

function host.exists(path: string): boolean
    return host.files[path] ~= nil or host.isDirectory(path)
end

function libc.access(pathLo, pathHi)
    if host.exists(host.canonical(guestString(address(pathLo, pathHi)))) then return result(0) end
    setErrno(2)
    return result(-1)
end

function libc.faccessat(dirLo, dirHi, pathLo, pathHi)
    local path = host.at(signed32(dirLo), guestString(address(pathLo, pathHi)))
    if not path then setErrno(9); return result(-1) end
    if host.exists(path) then return result(0) end
    setErrno(2)
    return result(-1)
end

-- Removes a file, or with `directory` an empty directory.
function host.removePath(path: string, directory: boolean): (number, number)
    if host.files[path] then
        if directory then setErrno(20); return result(-1) end
        host.files[path].links -= 1
        host.files[path] = nil
        host.names[path] = nil
        return result(0)
    end
    if not host.isDirectory(path) then setErrno(2); return result(-1) end
    if not directory then setErrno(if libc.darwin then 1 else 21); return result(-1) end
    if #host.children(path) > 0 then setErrno(host.errno("ENOTEMPTY")); return result(-1) end
    host.directories[path] = nil
    return result(0)
end

function libc.unlink(pathLo, pathHi)
    return host.removePath(host.canonical(guestString(address(pathLo, pathHi))), false)
end

function libc.rmdir(pathLo, pathHi)
    return host.removePath(host.canonical(guestString(address(pathLo, pathHi))), true)
end

function libc.remove(pathLo, pathHi)
    local path = host.canonical(guestString(address(pathLo, pathHi)))
    return host.removePath(path, host.files[path] == nil)
end
)luau", R"luau(
function libc.unlinkat(dirLo, dirHi, pathLo, pathHi, flagsLo)
    local path = host.at(signed32(dirLo), guestString(address(pathLo, pathHi)))
    if not path then setErrno(9); return result(-1) end
    return host.removePath(path, bit32.btest(flagsLo, if libc.darwin then 0x80 else 0x200))
end
)luau", R"luau(
function host.makeDirectory(path: string): (number, number)
    if path == "" then setErrno(2); return result(-1) end
    if host.exists(path) then setErrno(17); return result(-1) end
    if not host.isDirectory(host.parent(path)) then setErrno(host.missing(path)); return result(-1) end
    host.directories[path] = true
    return result(0)
end

function libc.mkdir(pathLo, pathHi)
    return host.makeDirectory(host.canonical(guestString(address(pathLo, pathHi))))
end

function libc.mkdirat(dirLo, dirHi, pathLo, pathHi)
    local path = host.at(signed32(dirLo), guestString(address(pathLo, pathHi)))
    if not path then setErrno(9); return result(-1) end
    return host.makeDirectory(path)
end

-- Moves a file, or a directory with everything below it.
function host.renamePath(from: string, to: string): (number, number)
    if from == "" or to == "" then setErrno(2); return result(-1) end
    if from == to then
        if host.exists(from) then return result(0) end
        setErrno(2)
        return result(-1)
    end
    if host.files[from] then
        if host.isDirectory(to) then setErrno(21); return result(-1) end
        if not host.isDirectory(host.parent(to)) then setErrno(2); return result(-1) end
        local target = host.files[to]
        if target == host.files[from] then return result(0) end
        if target then target.links -= 1 end
        host.files[to], host.files[from] = host.files[from], nil
        host.names[from] = nil
        return result(0)
    end
    if not host.isDirectory(from) then setErrno(2); return result(-1) end
    if host.files[to] then setErrno(20); return result(-1) end
    if string.sub(to, 1, #from + 1) == from .. "/" then setErrno(22); return result(-1) end
    if host.isDirectory(to) and #host.children(to) > 0 then setErrno(host.errno("ENOTEMPTY")); return result(-1) end
    if not host.isDirectory(host.parent(to)) then setErrno(host.missing(to)); return result(-1) end
    local moved: {[string]: FileContents} = {}
    for path, contents in host.files do
        if string.sub(path, 1, #from + 1) == from .. "/" then moved[path] = contents end
    end
    for path, contents in moved do
        host.files[path], host.names[path] = nil, nil
        host.files[to .. string.sub(path, #from + 1)] = contents
        host.directories[host.parent(to .. string.sub(path, #from + 1))] = true
    end
    local directories: {string} = {}
    for path in host.directories do
        if path == from or string.sub(path, 1, #from + 1) == from .. "/" then table.insert(directories, path) end
    end
    for _, path in directories do
        host.directories[path] = nil
        host.directories[to .. string.sub(path, #from + 1)] = true
    end
    host.directories[to] = true
    return result(0)
end

function libc.rename(fromLo, fromHi, toLo, toHi)
    return host.renamePath(host.canonical(guestString(address(fromLo, fromHi))), host.canonical(guestString(address(toLo, toHi))))
end

function libc.renameat(fromDirLo, fromDirHi, fromLo, fromHi, toDirLo, toDirHi, toLo, toHi)
    local from = host.at(signed32(fromDirLo), guestString(address(fromLo, fromHi)))
    local to = host.at(signed32(toDirLo), guestString(address(toLo, toHi)))
    if not from or not to then setErrno(9); return result(-1) end
    return host.renamePath(from, to)
end

)luau", R"luau(
-- Copies `text` and its terminator into a caller's buffer of `size` bytes, or into new memory when the buffer
-- is null, as getcwd and realpath do.
function host.returnPath(text: string, bufLo: number, bufHi: number, size: number?): (number, number)
    local at = address(bufLo, bufHi)
    if at == 0 then return newGuestString(text), 0 end
    if size and #text + 1 > size then setErrno(34); return 0, 0 end
    writeString(at, text)
    write(1, at + #text, 0, 0)
    return at, 0
end

function libc.getcwd(bufLo, bufHi, sizeLo, sizeHi)
    local size = address(sizeLo, sizeHi)
    return host.returnPath(host.cwd, bufLo, bufHi, if address(bufLo, bufHi) ~= 0 or size ~= 0 then size else nil)
end

function libc.chdir(pathLo, pathHi)
    local path = host.canonical(guestString(address(pathLo, pathHi)))
    if not host.isDirectory(path) then setErrno(if host.files[path] then 20 else 2); return result(-1) end
    host.cwd = path
    return result(0)
end

function libc.fchdir(fdLo)
    local file = host.descriptors[signed32(fdLo)]
    if not file or not file.directory then setErrno(if file then 20 else 9); return result(-1) end
    host.cwd = file.path
    return result(0)
end

function libc.realpath(pathLo, pathHi, bufLo, bufHi)
    local path = host.canonical(guestString(address(pathLo, pathHi)))
    if not host.exists(path) then setErrno(2); return 0, 0 end
    return host.returnPath(path, bufLo, bufHi, nil)
end

-- There are no symbolic links: readlink finds none, and making one is not permitted.
function libc.readlink(pathLo, pathHi)
    setErrno(if host.exists(host.canonical(guestString(address(pathLo, pathHi)))) then 22 else 2)
    return result(-1)
end

function libc.readlinkat(dirLo, dirHi, pathLo, pathHi)
    local path = host.at(signed32(dirLo), guestString(address(pathLo, pathHi)))
    setErrno(if not path then 9 elseif host.exists(path) then 22 else 2)
    return result(-1)
end

function libc.symlink()
    setErrno(1)
    return result(-1)
end

function libc.link(fromLo, fromHi, toLo, toHi)
    local from = host.canonical(guestString(address(fromLo, fromHi)))
    local to = host.canonical(guestString(address(toLo, toHi)))
    if not host.files[from] then setErrno(if host.isDirectory(from) then 1 else 2); return result(-1) end
    if to == "" then setErrno(2); return result(-1) end
    if host.exists(to) then setErrno(17); return result(-1) end
    if not host.isDirectory(host.parent(to)) then setErrno(2); return result(-1) end
    host.files[from].links += 1
    host.files[to] = host.files[from]
    return result(0)
end

-- Permissions, owners, and times are not kept: these succeed for paths that exist.
function libc.touchPath(pathLo, pathHi)
    if host.exists(host.canonical(guestString(address(pathLo, pathHi)))) then return result(0) end
    setErrno(2)
    return result(-1)
end

function libc.touchPathAt(dirLo, dirHi, pathLo, pathHi)
    local path = host.at(signed32(dirLo), guestString(address(pathLo, pathHi)))
    if not path then setErrno(9); return result(-1) end
    if host.exists(path) then return result(0) end
    setErrno(2)
    return result(-1)
end

function libc.touchDescriptor(fdLo)
    local fd = signed32(fdLo)
    if host.descriptors[fd] or (fd >= 0 and fd <= 2) then return result(0) end
    setErrno(9)
    return result(-1)
end

function host.truncateFile(file: FileContents, size: number)
    if size > buffer.len(file.data) then
        local grown = buffer.create(size)
        buffer.copy(grown, 0, file.data, 0, file.size)
        file.data = grown
    elseif size < file.size then
        buffer.fill(file.data, size, 0, file.size - size)
    end
    file.size = size
end

function libc.ftruncate(fdLo, fdHi, sizeLo, sizeHi)
    local file = host.descriptors[signed32(fdLo)]
    if not file or not file.writable then setErrno(if file then 22 else 9); return result(-1) end
    local size = signed64(sizeLo, sizeHi)
    if size < 0 then setErrno(22); return result(-1) end
    host.truncateFile(file.contents, size)
    return result(0)
end

function libc.truncate(pathLo, pathHi, sizeLo, sizeHi)
    local fd, failure = hostOpen(guestString(address(pathLo, pathHi)), false, true, false, false, false)
    if not fd then setErrno(failure); return result(-1) end
    local lo, hi = libc.ftruncate(fd, 0, sizeLo, sizeHi)
    hostClose(fd)
    return lo, hi
end

-- DIR streams: a guest allocation holds the struct dirent that readdir fills, in Darwin's 64-bit inode layout
-- (name at 21, its length at 18, type at 20) or glibc's (name at 19, type at 18).
function host.openDirectory(path: string, fd: number?): number
    local entries = {{name = ".", directory = true}, {name = "..", directory = true}}
    for _, entry in host.children(path) do table.insert(entries, entry) end
    local handle = resize(0, 0, 1088, 0)
    if handle == 0 then error("guest heap exhausted", 0) end
    host.directoryStreams[handle] = {path = path, entries = entries, at = 1, fd = fd}
    return handle
end

function libc.opendir(pathLo, pathHi)
    local path = host.canonical(guestString(address(pathLo, pathHi)))
    if not host.isDirectory(path) then setErrno(if host.files[path] then 20 else 2); return 0, 0 end
    return host.openDirectory(path, nil), 0
end

function libc.fdopendir(fdLo)
    local fd = signed32(fdLo)
    local file = host.descriptors[fd]
    if not file or not file.directory then setErrno(if file then 20 else 9); return 0, 0 end
    return host.openDirectory(file.path, fd), 0
end

function libc.readdir(dirLo, dirHi)
    local handle = address(dirLo, dirHi)
    local stream = host.directoryStreams[handle]
    if not stream then setErrno(9); return 0, 0 end
    local entry = stream.entries[stream.at]
    if not entry then return 0, 0 end
    stream.at += 1
    local at = handle + 32
    local name = entry.name
    local inode = host.inode(host.canonical(stream.path .. "/" .. name))
    local kind = if entry.directory then 4 else 8
    if libc.darwin then
        fillMemory(at, 0, 0, 24, 0)
        write(8, at, inode, 0)
        write(8, at + 8, stream.at - 1, 0)
        write(2, at + 16, 24 + #name, 0)
        write(2, at + 18, #name, 0)
        write(1, at + 20, kind, 0)
        writeString(at + 21, name)
        write(1, at + 21 + #name, 0, 0)
    else
        fillMemory(at, 0, 0, 20, 0)
        write(8, at, inode, 0)
        write(8, at + 8, stream.at - 1, 0)
        write(2, at + 16, 20 + #name, 0)
        write(1, at + 18, kind, 0)
        writeString(at + 19, name)
        write(1, at + 19 + #name, 0, 0)
    end
    return at, 0
end

function libc.closedir(dirLo, dirHi)
    local handle = address(dirLo, dirHi)
    local stream = host.directoryStreams[handle]
    if not stream then setErrno(9); return result(-1) end
    if stream.fd then hostClose(stream.fd) end
    host.directoryStreams[handle] = nil
    resize(handle, 0, 0, 0)
    return result(0)
end

function libc.rewinddir(dirLo, dirHi)
    local stream = host.directoryStreams[address(dirLo, dirHi)]
    if stream then
        stream.entries = {{name = ".", directory = true}, {name = "..", directory = true}}
        for _, entry in host.children(stream.path) do table.insert(stream.entries, entry) end
        stream.at = 1
    end
    return 0, 0
end

function libc.dirfd(dirLo, dirHi)
    local stream = host.directoryStreams[address(dirLo, dirHi)]
    if not stream then setErrno(9); return result(-1) end
    if not stream.fd then stream.fd = hostOpen(stream.path, true, false, false, false, false) end
    return result(stream.fd :: number)
end

-- tmpnam names a file that does not exist yet, as msvcrt (\\s<n>. at the drive's root) or POSIX systems (in
-- /tmp) do; tmpfile opens a new file that no path names, which goes away when it closes.
function host.temporaryName(): string
    for attempt = 1, 100000 do
        host.nextTemporary = (host.nextTemporary or 0) + 1
        local n = host.nextTemporary :: number
        local name = if libc.windows then string.format("\\s%x.", n) else string.format("/tmp/file%06d", n)
        if not host.exists(if libc.windows then host.windowsPath(name) else name) then return name end
    end
    error("guest temporary file names are exhausted", 0)
end

function libc.tmpnam(bufLo, bufHi)
    local name = host.temporaryName()
    if bufLo == 0 and bufHi == 0 then return cachedString(name), 0 end
    local at = address(bufLo, bufHi)
    writeString(at, name)
    write(1, at + #name, 0, 0)
    return at, 0
end

-- mkstemp and its relatives replace the template's trailing XXXXXX with characters that name a new file.
function libc.mkstemp(templateLo, templateHi)
    local at = address(templateLo, templateHi)
    local template = guestString(at)
    if string.sub(template, -6) ~= "XXXXXX" then setErrno(22); return result(-1) end
    for attempt = 1, 1000 do
        host.nextTemporary = (host.nextTemporary or 0) + 1
        local suffix = string.format("%06d", host.nextTemporary :: number)
        local path = string.sub(template, 1, -7) .. suffix
        if not host.exists(host.canonical(path)) then
            local fd, failure = hostOpen(path, true, true, true, false, false, true)
            if not fd then setErrno(failure); return result(-1) end
            writeString(at + #template - 6, suffix)
            return result(fd)
        end
    end
    setErrno(17)
    return result(-1)
end

function libc.mkdtemp(templateLo, templateHi)
    local at = address(templateLo, templateHi)
    local template = guestString(at)
    if string.sub(template, -6) ~= "XXXXXX" then setErrno(22); return 0, 0 end
    for attempt = 1, 1000 do
        host.nextTemporary = (host.nextTemporary or 0) + 1
        local suffix = string.format("%06d", host.nextTemporary :: number)
        local path = host.canonical(string.sub(template, 1, -7) .. suffix)
        if not host.exists(path) and host.isDirectory(host.parent(path)) then
            host.directories[path] = true
            writeString(at + #template - 6, suffix)
            return at, 0
        end
    end
    setErrno(17)
    return 0, 0
end

function libc.isatty()
    return result(0)
end

local function streamMode(mode: string): (boolean, boolean, boolean, boolean, boolean)
    local first = string.sub(mode, 1, 1)
    local plus = string.find(mode, "+", 1, true) ~= nil
    return first == "r" or plus, first ~= "r" or plus, first ~= "r", first == "w", first == "a"
end

local function newStream(fd: number): number
    local at = resize(0, 0, 256, 0)
    fillMemory(at, 0, 0, 256, 0)
    host.streams[at] = fd
    return at
end

function libc.fopen(pathLo, pathHi, modeLo, modeHi)
    local readable, writable, create, truncate, append = streamMode(guestString(address(modeLo, modeHi)))
    local exclusive = string.find(guestString(address(modeLo, modeHi)), "x", 1, true) ~= nil
    local fd, failure = hostOpen(guestString(address(pathLo, pathHi)), readable, writable, create, truncate, append, exclusive)
    if not fd then setErrno(failure); return 0, 0 end
    return newStream(fd), 0
end

function libc.fdopen(fdLo, fdHi)
    return newStream(signed32(fdLo)), 0
end

function libc.tmpfile()
    local name = host.temporaryName()
    local path = if libc.windows then host.windowsPath(name) else name
    local fd, failure = hostOpen(path, true, true, true, true, false, true)
    if not fd then setErrno(failure); return 0, 0 end
    local contents = host.files[path]
    if contents then contents.links -= 1 end
    host.files[path], host.names[path] = nil, nil
    return newStream(fd), 0
end

function libc.fclose(lo, hi)
    local fd = streamDescriptor(lo, hi)
    host.streams[address(lo, hi)] = nil
    return result(if hostClose(fd) then 0 else -1)
end

function libc.fileno(lo, hi)
    return result(streamDescriptor(lo, hi))
end

function libc.fwrite(ptrLo, ptrHi, sizeLo, sizeHi, countLo, countHi, streamLo, streamHi)
    local size, count = address(sizeLo, sizeHi), address(countLo, countHi)
    if size == 0 or count == 0 then return 0, 0 end
    local text = readString(address(ptrLo, ptrHi), size * count)
    if not hostWrite(streamDescriptor(streamLo, streamHi), text) then return 0, 0 end
    return result(count)
end

function libc.fread(ptrLo, ptrHi, sizeLo, sizeHi, countLo, countHi, streamLo, streamHi)
    local size, count = address(sizeLo, sizeHi), address(countLo, countHi)
    if size == 0 or count == 0 then return 0, 0 end
    local fd = streamDescriptor(streamLo, streamHi)
    local text = hostRead(fd, size * count)
    if not text then
        local file = host.descriptors[fd]
        setErrno(if file and file.directory then 21 else 9)
        host.errors = host.errors or {}
        ;(host.errors :: any)[fd] = true
        return 0, 0
    end
    if #text < size * count then host.eof[fd] = true end
    writeString(address(ptrLo, ptrHi), text)
    return result(#text // size)
end

function libc.fputc(c, cHi, streamLo, streamHi)
    hostWrite(streamDescriptor(streamLo, streamHi), string.char(c % 256))
    return result(c % 256)
end

function libc.fputs(sLo, sHi, streamLo, streamHi)
    hostWrite(streamDescriptor(streamLo, streamHi), guestString(address(sLo, sHi)))
    return result(1)
end

function libc.puts(sLo, sHi)
    hostWrite(1, guestString(address(sLo, sHi)) .. "\n")
    return result(1)
end

function libc.putchar(c)
    hostWrite(1, string.char(c % 256))
    return result(c % 256)
end

local function getByte(fd: number): number
    local pushed = host.pushback[fd]
    if pushed then
        host.pushback[fd] = nil
        return pushed
    end
    local text = hostRead(fd, 1)
    if not text or #text == 0 then
        host.eof[fd] = true
        return -1
    end
    return string.byte(text)
end

function libc.fgetc(lo, hi)
    return result(getByte(streamDescriptor(lo, hi)))
end

function libc.getchar()
    return result(getByte(0))
end

function libc.ungetc(c, cHi, lo, hi)
    if signed32(c) == -1 then return result(-1) end
    local fd = streamDescriptor(lo, hi)
    host.pushback[fd] = c % 256
    host.eof[fd] = nil
    return result(c % 256)
end

function libc.fgets(bufLo, bufHi, countLo, countHi, lo, hi)
    local fd = streamDescriptor(lo, hi)
    local limit = signed32(countLo) - 1
    local bytes = {}
    while #bytes < limit do
        local byte = getByte(fd)
        if byte < 0 then break end
        table.insert(bytes, string.char(byte))
        if byte == 10 then break end
    end
    if #bytes == 0 and limit > 0 then return 0, 0 end
    local text = table.concat(bytes)
    writeString(address(bufLo, bufHi), text)
    write(1, address(bufLo, bufHi) + #text, 0, 0)
    return bufLo, bufHi
end

function libc.fflush()
    return 0, 0
end

function libc.setvbuf()
    return 0, 0
end

function libc.fseek(lo, hi, offsetLo, offsetHi, whenceLo, whenceHi)
    local fd = streamDescriptor(lo, hi)
    host.pushback[fd] = nil
    host.eof[fd] = nil
    return result(if hostSeek(fd, signed64(offsetLo, offsetHi), whenceLo) then 0 else -1)
end

function libc.ftell(lo, hi)
    local file = host.descriptors[streamDescriptor(lo, hi)]
    return result(if file then file.at else -1)
end

function libc.rewind(lo, hi)
    libc.fseek(lo, hi, 0, 0, 0, 0)
    return 0, 0
end

function libc.feof(lo, hi)
    return result(if host.eof[streamDescriptor(lo, hi)] then 1 else 0)
end

-- A stream's error indicator: set by a read or write that fails.
function libc.ferror(lo, hi)
    return if ((host.errors or {}) :: any)[streamDescriptor(lo, hi)] then 1 else 0, 0
end

function libc.clearerr(lo, hi)
    local fd = streamDescriptor(lo, hi)
    host.eof[fd] = nil
    if host.errors then (host.errors :: any)[fd] = nil end
    return 0, 0
end
)luau", R"luau(
-- glibc's getc/putc macros fall back to these when the FILE buffers are empty.
function libc.__uflow(lo, hi)
    return libc.fgetc(lo, hi)
end

function libc.__overflow(lo, hi, c, cHi)
    return libc.fputc(c, cHi, lo, hi)
end

-- Darwin's __sgetc/__sputc macros refill through these; keep the buffer counts at zero.
function libc.__srget(lo, hi)
    write(4, address(lo, hi) + 8, 0, 0)
    return libc.fgetc(lo, hi)
end

function libc.__swbuf(c, cHi, lo, hi)
    write(4, address(lo, hi) + 12, 0, 0)
    return libc.fputc(c, cHi, lo, hi)
end

function libc.getenv(nameLo, nameHi)
    local name = guestString(address(nameLo, nameHi))
    for _, entry in host.env do
        local key, value = string.match(entry, "^([^=]*)=(.*)$")
        if key == name then return cachedString(value :: string), 0 end
    end
    return 0, 0
end

-- strtol and strtoul for a 64-bit result, or a 32-bit one (`narrow`) for Windows, where long is 32 bits wide.
local function parseInteger(textLo: number, textHi: number, endLo: number, endHi: number, base: number,
    unsigned: boolean, narrow: boolean?): (number, number)
    local start = address(textLo, textHi)
    local at = start
    local byte = read(1, at)
    while byte == 32 or (byte >= 9 and byte <= 13) do at += 1; byte = read(1, at) end
    local negative = false
    if byte == 43 or byte == 45 then negative = byte == 45; at += 1; byte = read(1, at) end
    if (base == 0 or base == 16) and byte == 48 and (read(1, at + 1) == 120 or read(1, at + 1) == 88) then
        local next = read(1, at + 2)
        if (next >= 48 and next <= 57) or (next >= 97 and next <= 102) or (next >= 65 and next <= 70) then
            at += 2
            base = 16
        end
    elseif base == 0 then
        base = if byte == 48 then 8 else 10
    end
    local lo, hi, any = 0, 0, false
    local overflow = false
    while true do
        byte = read(1, at)
        local digit = if byte >= 48 and byte <= 57 then byte - 48 elseif byte >= 97 and byte <= 122 then byte - 87
            elseif byte >= 65 and byte <= 90 then byte - 55 else 99
        if digit >= base then break end
        any = true
        local low = lo * base + digit
        local high = hi * base + math.floor(low / 4294967296)
        lo, hi = low % 4294967296, high
        if hi >= 4294967296 then overflow = true; hi %= 4294967296 end
        at += 1
    end
    if endLo ~= 0 or endHi ~= 0 then
        write(8, address(endLo, endHi), if any then at else start, 0)
    end
    -- Darwin reports a string without digits as EINVAL.
    if not any and libc.darwin then setErrno(22) end
    if narrow then
        local limit = if unsigned then 4294967295 elseif negative then 2147483648 else 2147483647
        if overflow or hi ~= 0 or lo > limit then
            setErrno(34)
            return if unsigned then 4294967295 elseif negative then 2147483648 else 2147483647, 0
        end
        return if negative then (-lo) % 4294967296 else lo, 0
    end
    if overflow then
        setErrno(34)
        if unsigned then return 4294967295, 4294967295 end
        return if negative then 0 else 4294967295, if negative then 2147483648 else 2147483647
    end
    if not unsigned and not negative and hi >= 2147483648 then setErrno(34); return 4294967295, 2147483647 end
    if not unsigned and negative and (hi > 2147483648 or (hi == 2147483648 and lo > 0)) then
        setErrno(34)
        return 0, 2147483648
    end
    if negative then
        lo, hi = (-lo) % 4294967296, (-hi - (if lo == 0 then 0 else 1)) % 4294967296
    end
    return lo, hi
end

function libc.strtol(sLo, sHi, endLo, endHi, baseLo)
    return parseInteger(sLo, sHi, endLo, endHi, baseLo, false)
end

function libc.strtoul(sLo, sHi, endLo, endHi, baseLo)
    return parseInteger(sLo, sHi, endLo, endHi, baseLo, true)
end

function libc.strtolNarrow(sLo, sHi, endLo, endHi, baseLo)
    return parseInteger(sLo, sHi, endLo, endHi, baseLo, false, true)
end

function libc.strtoulNarrow(sLo, sHi, endLo, endHi, baseLo)
    return parseInteger(sLo, sHi, endLo, endHi, baseLo, true, true)
end

function libc.atoi(sLo, sHi)
    local lo = parseInteger(sLo, sHi, 0, 0, 10, false)
    return lo, 0
end

function libc.atol(sLo, sHi)
    return parseInteger(sLo, sHi, 0, 0, 10, false)
end

-- Returns the double and the number of bytes parsed.
local function parseDouble(text: string): (number, number)
    local leading = #(string.match(text, "^%s*") :: string)
    local rest = string.sub(text, leading + 1)
    local lowered = string.lower(rest)
    local sign = 1
    local signLength = 0
    if string.sub(lowered, 1, 1) == "-" or string.sub(lowered, 1, 1) == "+" then
        if string.sub(lowered, 1, 1) == "-" then sign = -1 end
        signLength = 1
        lowered = string.sub(lowered, 2)
    end
    if string.sub(lowered, 1, 8) == "infinity" then return sign * math.huge, leading + signLength + 8 end
    if string.sub(lowered, 1, 3) == "inf" then return sign * math.huge, leading + signLength + 3 end
    if string.sub(lowered, 1, 3) == "nan" then
        -- A quiet NaN with the sign given, as glibc returns, and an optional (n-char-sequence).
        local payload = string.match(lowered, "^%([%w_]*%)", 4)
        return decodeFloat(8, 0, if sign < 0 then 0xfff80000 else 0x7ff80000),
            leading + signLength + 3 + (if payload then #payload else 0)
    end
    local hexMantissa = string.match(lowered, "^0x(%x*%.?%x*)")
    if hexMantissa and string.find(hexMantissa, "%x") then
        local whole, fraction = string.match(hexMantissa, "^(%x*)%.?(%x*)$")
        local used = 2 + #hexMantissa
        -- The binary exponent needs digits; a bare p is not part of the number.
        local exponentText = string.match(lowered, "^p[+-]?%d+", used + 1)
        local exponent = if exponentText then tonumber(string.sub(exponentText, 2)) :: number else 0
        if exponentText then used += #exponentText end
        local digits = string.gsub((whole :: string) .. (fraction :: string), "^0+", "")
        local scale = exponent - 4 * #(fraction :: string)
        -- tonumber converts at most 16 hex digits exactly; later digits only scale the value.
        if #digits > 16 then
            scale += 4 * (#digits - 16)
            digits = string.sub(digits, 1, 16)
        end
        local value = if digits == "" then 0 else math.ldexp(tonumber(digits, 16) :: number, scale)
        return sign * value, leading + signLength + used
    end
    local number = string.match(lowered, "^%d*%.?%d*")
    if not number or number == "" or number == "." then return 0, 0 end
    local exponent = string.match(lowered, "^e[+-]?%d+", #number + 1)
    local literal = number .. (exponent or "")
    local value = tonumber(literal) or 0
    -- Out of range: glibc returns infinity or zero and sets ERANGE.
    if value == math.huge or (value == 0 and string.find(number, "[1-9]")) then setErrno(34) end
    return sign * value, leading + signLength + #literal
end

function libc.strtod(sLo, sHi, endLo, endHi)
    local start = address(sLo, sHi)
    local value, used = parseDouble(guestString(start, 512))
    if endLo ~= 0 or endHi ~= 0 then write(8, address(endLo, endHi), start + used, 0) end
    return value
end

function libc.time(lo, hi)
    local now = os.time()
    if lo ~= 0 or hi ~= 0 then write(8, address(lo, hi), now, 0) end
    return now, 0
end

function libc.clock()
    return result(math.floor(os.clock() * 1000000))
end

function libc.clock_gettime(clockLo, clockHi, lo, hi)
    local now = os.clock()
    local at = address(lo, hi)
    write(8, at, math.floor(now), 0)
    write(8, at + 8, math.floor((now % 1) * 1e9), 0)
    return 0, 0
end

function libc.gettimeofday(lo, hi)
    local now = os.time()
    local at = address(lo, hi)
    write(8, at, now, 0)
    write(8, at + 8, 0, 0)
    return 0, 0
end

function libc.setlocale()
    return cachedString("C"), 0
end

function libc.getpid()
    return 4096, 0
end

-- The process runs as an ordinary user: Darwin's first account (staff), or Linux's.
function libc.getuid()
    return if libc.darwin then 501 else 1000, 0
end

function libc.getgid()
    return if libc.darwin then 20 else 1000, 0
end

-- No account database is available.
function libc.getpwuid()
    return 0, 0
end

-- Pseudo-random numbers as each C library makes them. random() is the BSD additive generator in glibc and on
-- Darwin, and glibc's rand() is random(); Darwin's rand() is Park and Miller's minimal standard, msvcrt's an LCG.
function host.parkMiller(x: number): number
    if x == 0 then x = 123459876 end
    local hi, lo = x // 127773, x % 127773
    x = 16807 * lo - 2836 * hi
    if x < 0 then x += 2147483647 end
    return x
end

function host.seedRandom(seed: number)
    seed %= 4294967296
    if not libc.darwin and seed == 0 then seed = 1 end
    local state = table.create(31, 0)
    state[1] = seed
    for i = 2, 31 do state[i] = host.parkMiller(state[i - 1]) end
    host.randomState = {state = state, front = 4, rear = 1}
    for _ = 1, 310 do host.nextRandom() end
end

function host.nextRandom(): number
    if not host.randomState then host.seedRandom(1) end
    local generator = host.randomState :: any
    local state, front, rear = generator.state, generator.front, generator.rear
    state[front] = (state[front] + state[rear]) % 4294967296
    local value = bit32.rshift(state[front], 1)
    generator.front, generator.rear = front % 31 + 1, rear % 31 + 1
    return value
end

function libc.random()
    return host.nextRandom(), 0
end

function libc.srandom(seedLo)
    host.seedRandom(seedLo)
    return 0, 0
end

function libc.srandomdev()
    host.seedRandom(math.floor(os.time() + os.clock() * 1000000) % 4294967296)
    return 0, 0
end

function libc.rand()
    if libc.windows then
        host.randSeed = ((host.randSeed or 1) * 214013 + 2531011) % 4294967296
        return bit32.band(bit32.rshift(host.randSeed :: number, 16), 0x7fff), 0
    elseif libc.darwin then
        host.randSeed = host.parkMiller(host.randSeed or 1)
        return host.randSeed :: number, 0
    end
    return host.nextRandom(), 0
end

function libc.srand(seedLo)
    if libc.windows or libc.darwin then host.randSeed = seedLo else host.seedRandom(seedLo) end
    return 0, 0
end

-- Resource usage: the user time is the run's processor time so far.
function libc.getrusage(whoLo, whoHi, usageLo, usageHi)
    local at = address(usageLo, usageHi)
    for offset = 0, 136, 8 do write(8, at + offset, 0, 0) end
    local seconds = os.clock()
    write(8, at, math.floor(seconds), 0)
    write(8, at + 8, math.floor(seconds % 1 * 1000000), 0)
    return 0, 0
end

-- confstr's values: the standard utility path, and on Darwin the user's temporary and cache directories.
function libc.confstr(nameLo, nameHi, bufLo, bufHi, lengthLo, lengthHi)
    local name = signed32(nameLo)
    local value = if name == (if libc.darwin then 1 else 0) then
            (if libc.darwin then "/usr/bin:/bin:/usr/sbin:/sbin" else "/bin:/usr/bin")
        elseif libc.darwin and (name == 65537 or name == 65538) then "/tmp/"
        else nil
    if not value then setErrno(22); return 0, 0 end
    local length = address(lengthLo, lengthHi)
    if length > 0 and (bufLo ~= 0 or bufHi ~= 0) then
        local text = string.sub(value, 1, length - 1)
        writeString(address(bufLo, bufHi), text .. "\0")
    end
    return result(#value + 1)
end

-- A signal raised with its default action: most end the process as the signal would; a few are ignored.
function libc.raise(signalLo)
    local signal = signed32(signalLo)
    local ignored = if libc.darwin then {[16] = true, [19] = true, [20] = true, [23] = true, [28] = true, [29] = true}
        else {[17] = true, [18] = true, [23] = true, [28] = true}
    if signal == 0 or ignored[signal] then return 0, 0 end
    exitProcess(128 + signal, false)
    return 0, 0
end

-- No command processor is available: system(NULL) says so, and commands cannot start.
function libc.system(commandLo, commandHi)
    if commandLo == 0 and commandHi == 0 then return 0, 0 end
    setErrno(host.errno("ENOSYS"))
    return result(-1)
end

function libc.popen()
    setErrno(host.errno("ENOSYS"))
    return 0, 0
end

function libc.pclose()
    setErrno(10)
    return result(-1)
end

-- File control. Locks always succeed, and no other process holds one; descriptors keep no flags of their own.
function libc.fcntl(fdLo, cmdLo, argLo, argHi)
    local fd, cmd = signed32(fdLo), signed32(cmdLo)
    local file = host.descriptors[fd]
    if not file and not (fd >= 0 and fd <= 2) then setErrno(9); return result(-1) end
    local darwin = libc.darwin
    if cmd == 1 or cmd == 2 or cmd == 4 then return 0, 0 end
    if cmd == 3 then
        local mode = if not file then (if fd == 0 then 0 else 1)
            elseif file.readable and file.writable then 2 elseif file.writable then 1 else 0
        if file and file.append then mode += if darwin then 8 else 0x400 end
        return mode, 0
    end
    if cmd == (if darwin then 7 else 5) or (not darwin and cmd == 36) then
        write(2, address(argLo, argHi) + (if darwin then 20 else 0), 2, 0)
        return 0, 0
    end
    if (darwin and (cmd == 8 or cmd == 9)) or (not darwin and (cmd == 6 or cmd == 7 or cmd == 37 or cmd == 38)) then
        return 0, 0
    end
    if darwin and (cmd == 51 or cmd == 85 or cmd == 48 or cmd == 68) then return 0, 0 end
    if darwin and cmd == 50 and file then
        writeString(address(argLo, argHi), file.path .. "\0")
        return 0, 0
    end
    setErrno(22)
    return result(-1)
end

-- One local file system holds every file: struct statfs in Darwin's layout (2168 bytes, an APFS volume at /) or
-- Linux's (120 bytes, ext4).
function host.writeStatfs(at: number)
    if libc.darwin then
        for offset = 0, 2160, 8 do write(8, at + offset, 0, 0) end
        write(4, at, 4096, 0)
        write(4, at + 4, 1048576, 0)
        write(8, at + 8, 262144, 0)
        write(8, at + 16, 131072, 0)
        write(8, at + 24, 131072, 0)
        write(8, at + 32, 1048576, 0)
        write(8, at + 40, 524288, 0)
        write(4, at + 56, libc.getuid(), 0)
        write(4, at + 60, 26, 0)
        write(4, at + 64, 0x1000, 0)
        writeString(at + 72, "apfs\0")
        writeString(at + 88, "/\0")
        writeString(at + 1112, "/dev/disk1s1\0")
    else
        for offset = 0, 112, 8 do write(8, at + offset, 0, 0) end
        write(8, at, 0xef53, 0)
        write(8, at + 8, 4096, 0)
        write(8, at + 16, 262144, 0)
        write(8, at + 24, 131072, 0)
        write(8, at + 32, 131072, 0)
        write(8, at + 40, 1048576, 0)
        write(8, at + 48, 524288, 0)
        write(8, at + 64, 255, 0)
        write(8, at + 72, 4096, 0)
        write(8, at + 80, 0x20, 0)
    end
end

function libc.statfs(pathLo, pathHi, bufLo, bufHi)
    local path = host.canonical(guestString(address(pathLo, pathHi)))
    if not host.exists(path) then setErrno(host.missing(path)); return result(-1) end
    host.writeStatfs(address(bufLo, bufHi))
    return 0, 0
end

function libc.fstatfs(fdLo, fdHi, bufLo, bufHi)
    local fd = signed32(fdLo)
    if not host.descriptors[fd] and not (fd >= 0 and fd <= 2) then setErrno(9); return result(-1) end
    host.writeStatfs(address(bufLo, bufHi))
    return 0, 0
end

-- Reads and writes at an offset, leaving the descriptor's position where it was.
function libc.pread(fdLo, fdHi, bufLo, bufHi, countLo, countHi, offsetLo, offsetHi)
    local fd = signed32(fdLo)
    local file = host.descriptors[fd]
    if not file or not file.readable then setErrno(if file and file.directory then 21 else 9); return result(-1) end
    local offset = signed64(offsetLo, offsetHi)
    if offset < 0 then setErrno(22); return result(-1) end
    local saved = file.at
    file.at = offset
    local text = hostRead(fd, address(countLo, countHi)) or ""
    file.at = saved
    writeString(address(bufLo, bufHi), text)
    return result(#text)
end
)luau", R"luau(
function libc.pwrite(fdLo, fdHi, bufLo, bufHi, countLo, countHi, offsetLo, offsetHi)
    local fd = signed32(fdLo)
    local file = host.descriptors[fd]
    if not file or not file.writable then setErrno(9); return result(-1) end
    local offset = signed64(offsetLo, offsetHi)
    if offset < 0 then setErrno(22); return result(-1) end
    local count = address(countLo, countHi)
    local saved, append = file.at, file.append
    file.at, file.append = offset, false
    local written = hostWrite(fd, readString(address(bufLo, bufHi), count))
    file.at, file.append = saved, append
    if not written then setErrno(28); return result(-1) end
    return result(count)
end

-- Darwin's memset_pattern4, 8, and 16 repeat a pattern of that many bytes.
function host.fillPattern(at: number, pattern: string, length: number)
    writeString(at, string.sub(string.rep(pattern, length // #pattern + 1), 1, length))
end

function libc.memset_pattern4(bLo, bHi, pLo, pHi, lengthLo, lengthHi)
    host.fillPattern(address(bLo, bHi), readString(address(pLo, pHi), 4), address(lengthLo, lengthHi))
    return 0, 0
end

function libc.memset_pattern8(bLo, bHi, pLo, pHi, lengthLo, lengthHi)
    host.fillPattern(address(bLo, bHi), readString(address(pLo, pHi), 8), address(lengthLo, lengthHi))
    return 0, 0
end

function libc.memset_pattern16(bLo, bHi, pLo, pHi, lengthLo, lengthHi)
    host.fillPattern(address(bLo, bHi), readString(address(pLo, pHi), 16), address(lengthLo, lengthHi))
    return 0, 0
end
)luau", R"luau(
-- abs and its wider forms, which compilers call when code takes their address; Windows' long is 32 bits.
function libc.abs(lo)
    local value = signed32(lo)
    return if value < 0 then (-value) % 4294967296 else value, 0
end

function libc.llabs(lo, hi)
    if hi < 2147483648 then return lo, hi end
    return (4294967296 - lo) % 4294967296, (4294967295 - hi + (if lo == 0 then 1 else 0)) % 4294967296
end

function libc.labs(lo, hi)
    if libc.windows then return libc.abs(lo) end
    return libc.llabs(lo, hi)
end

-- strlcpy and strlcat bound the whole destination and return the length they tried to make.
function libc.strlcpy(dstLo, dstHi, srcLo, srcHi, sizeLo, sizeHi)
    local text, size = guestString(address(srcLo, srcHi)), address(sizeLo, sizeHi)
    if size > 0 then writeString(address(dstLo, dstHi), string.sub(text, 1, size - 1) .. "\0") end
    return result(#text)
end

function libc.strlcat(dstLo, dstHi, srcLo, srcHi, sizeLo, sizeHi)
    local dst, size = address(dstLo, dstHi), address(sizeLo, sizeHi)
    local existing = guestString(dst, size)
    local text = guestString(address(srcLo, srcHi))
    if #existing >= size then return result(size + #text) end
    writeString(dst + #existing, string.sub(text, 1, size - #existing - 1) .. "\0")
    return result(#existing + #text)
end

function libc.sysconf(nameLo)
    -- _SC_PAGESIZE and _SC_NPROCESSORS_ONLN are the common queries.
    if nameLo == 30 or nameLo == 29 then return 4096, 0 end
    return 1, 0
end

function libc.signal()
    return 0, 0
end

function libc.success()
    return 0, 0
end

function libc.pthread_self()
    return host.current.id, 0
end

function libc.pthread_mach_thread_np()
    return 0x1003, 0
end

function libc.pthread_equal(alo, ahi, blo, bhi)
    return if alo == blo and ahi == bhi then 1 else 0, 0
end

local threadKeys: {[number]: {lo: number, hi: number}} = {}
local nextThreadKey = 1

function libc.pthread_key_create(keyLo, keyHi)
    write(4, address(keyLo, keyHi), nextThreadKey, 0)
    threadKeys[nextThreadKey] = {lo = 0, hi = 0}
    nextThreadKey += 1
    return 0, 0
end

-- Keys hold a value for each guest thread; the main thread's live in threadKeys.
function libc.pthread_getspecific(key)
    local slot = if host.current.main then threadKeys[key] else host.current.keys[key]
    if not slot then return 0, 0 end
    return slot.lo, slot.hi
end

function libc.pthread_setspecific(key, keyHi, lo, hi)
    if host.current.main then threadKeys[key] = {lo = lo, hi = hi} else host.current.keys[key] = {lo = lo, hi = hi} end
    return 0, 0
end
)luau", R"luau(
-- C locale character classes in Darwin's rune type bits.
local function runeType(c: number): number
    if c < 0 or c > 255 then return 0 end
    local upper, lower = c >= 65 and c <= 90, c >= 97 and c <= 122
    local digit = c >= 48 and c <= 57
    local hex = digit or (c >= 65 and c <= 70) or (c >= 97 and c <= 102)
    local space = c == 32 or (c >= 9 and c <= 13)
    local print = c >= 32 and c <= 126
    local graph = c >= 33 and c <= 126
    local bits = 0
    if upper or lower then bits += 0x100 end
    if c < 32 or c == 127 then bits += 0x200 end
    if digit then bits += 0x400 + (c - 48) end
    if graph then bits += 0x800 end
    if lower then bits += 0x1000 end
    if graph and not (upper or lower or digit) then bits += 0x2000 end
    if space then bits += 0x4000 end
    if upper then bits += 0x8000 end
    if hex then bits += 0x10000 end
    if c == 9 or c == 32 then bits += 0x20000 end
    if print then bits += 0x40000 end
    return bits
end

function libc.__maskrune(c, cHi, mask)
    return bit32.band(runeType(signed32(c)), mask), 0
end

function libc.__toupper(c)
    return if c >= 97 and c <= 122 then c - 32 else c, 0
end

function libc.__tolower(c)
    return if c >= 65 and c <= 90 then c + 32 else c, 0
end

function libc.__mb_cur_max_l()
    return 1, 0
end

function libc.wctob(c)
    return if c < 128 then c else 4294967295, 0
end

function libc.btowc(c)
    return if c < 128 then c else 4294967295, 0
end

function libc.mbtowc(pwcLo, pwcHi, sLo, sHi, nLo, nHi)
    if sLo == 0 and sHi == 0 then return 0, 0 end
    if nLo == 0 and nHi == 0 then return 4294967295, 4294967295 end
    local byte = read(1, address(sLo, sHi))
    if pwcLo ~= 0 or pwcHi ~= 0 then write(4, address(pwcLo, pwcHi), byte, 0) end
    return if byte == 0 then 0 else 1, 0
end

function libc.mbrtowc(pwcLo, pwcHi, sLo, sHi, nLo, nHi)
    return libc.mbtowc(pwcLo, pwcHi, sLo, sHi, nLo, nHi)
end

function libc.mbrlen(sLo, sHi, nLo, nHi)
    if nLo == 0 and nHi == 0 then return 4294967294, 4294967295 end
    return if read(1, address(sLo, sHi)) == 0 then 0 else 1, 0
end

function libc.wcrtomb(sLo, sHi, wc)
    if sLo == 0 and sHi == 0 then return 1, 0 end
    if wc > 255 then setErrno(92); return 4294967295, 4294967295 end
    write(1, address(sLo, sHi), wc, 0)
    return 1, 0
end

-- mbsrtowcs and mbsnrtowcs: `limit` bounds the source bytes for the n variant.
local function toWide(dstLo: number, dstHi: number, srcLo: number, srcHi: number, limit: number?, count: number): (number, number)
    local holder = address(srcLo, srcHi)
    local src = address(read(8, holder))
    local dst = address(dstLo, dstHi)
    local converted = 0
    while (dst == 0 or converted < count) and (limit == nil or converted < limit) do
        local byte = read(1, src + converted)
        if dst ~= 0 then write(4, dst + converted * 4, byte, 0) end
        if byte == 0 then
            if dst ~= 0 then write(8, holder, 0, 0) end
            return result(converted)
        end
        converted += 1
    end
    if dst ~= 0 then write(8, holder, src + converted, 0) end
    return result(converted)
end

function libc.mbsrtowcs(dstLo, dstHi, srcLo, srcHi, countLo, countHi)
    return toWide(dstLo, dstHi, srcLo, srcHi, nil, address(countLo, countHi))
end

function libc.mbsnrtowcs(dstLo, dstHi, srcLo, srcHi, limitLo, limitHi, countLo, countHi)
    return toWide(dstLo, dstHi, srcLo, srcHi, address(limitLo, limitHi), address(countLo, countHi))
end

function libc.wcsnrtombs(dstLo, dstHi, srcLo, srcHi, limitLo, limitHi, countLo, countHi)
    local holder = address(srcLo, srcHi)
    local src = address(read(8, holder))
    local dst = address(dstLo, dstHi)
    local limit, count = address(limitLo, limitHi), address(countLo, countHi)
    local converted = 0
    while (dst == 0 or converted < count) and converted < limit do
        local wc = read(4, src + converted * 4)
        if wc > 255 then setErrno(92); return 4294967295, 4294967295 end
        if dst ~= 0 then write(1, dst + converted, wc, 0) end
        if wc == 0 then
            if dst ~= 0 then write(8, holder, 0, 0) end
            return result(converted)
        end
        converted += 1
    end
    if dst ~= 0 then write(8, holder, src + converted * 4, 0) end
    return result(converted)
end

function libc.wcslen(lo, hi)
    local at = address(lo, hi)
    local count = 0
    while read(4, at + count * 4) ~= 0 do count += 1 end
    return result(count)
end

local localeHandle = 0
function libc.newlocale()
    if localeHandle == 0 then
        localeHandle = resize(0, 0, 16, 0)
        fillMemory(localeHandle, 0, 0, 16, 0)
    end
    return localeHandle, 0
end

function libc.uselocale()
    return 4294967295, 4294967295
end

local conventions = 0
function libc.localeconv()
    if conventions == 0 then
        conventions = resize(0, 0, 96, 0)
        fillMemory(conventions, 0, 127, 96, 0)
        local empty = cachedString("")
        for field = 0, 9 do write(8, conventions + field * 8, empty, 0) end
        write(8, conventions, cachedString("."), 0)
    end
    return conventions, 0
end

local function span(sLo: number, sHi: number, setLo: number, setHi: number, inside: boolean): number
    local text = guestString(address(sLo, sHi))
    local set = guestString(address(setLo, setHi))
    for i = 1, #text do
        local found = string.find(set, string.sub(text, i, i), 1, true) ~= nil
        if found ~= inside then return i - 1 end
    end
    return #text
end

function libc.strspn(sLo, sHi, setLo, setHi)
    return result(span(sLo, sHi, setLo, setHi, true))
end

function libc.strcspn(sLo, sHi, setLo, setHi)
    return result(span(sLo, sHi, setLo, setHi, false))
end

function libc.strpbrk(sLo, sHi, setLo, setHi)
    local length = span(sLo, sHi, setLo, setHi, false)
    local at = address(sLo, sHi) + length
    return if read(1, at) == 0 then 0 else at, 0
end

-- glibc's ctype tables for the C locale, which its ctype.h macros index from -128 to 255 (EOF is -1) through
-- __ctype_b_loc and the like: the class bits of each character, and its upper and lower case.
function libc.ctypeTable(kind: number): (number, number)
    local tables = libc.ctypeTables or {}
    libc.ctypeTables = tables
    if tables[kind] then return tables[kind], 0 end
    local width = if kind == 0 then 2 else 4
    local first = resize(0, 0, 384 * width, 0)
    for i = -128, 255 do
        local value = i
        if kind == 0 then
            value = 0
            if i >= 0 and i < 128 then
                local upper, lower, digit = i >= 65 and i <= 90, i >= 97 and i <= 122, i >= 48 and i <= 57
                local graph = i >= 33 and i <= 126
                local alnum = upper or lower or digit
                local bits = {upper, lower, upper or lower, digit,
                    digit or (i >= 65 and i <= 70) or (i >= 97 and i <= 102), (i >= 9 and i <= 13) or i == 32,
                    i >= 32 and i <= 126, graph, i == 9 or i == 32, i < 32 or i == 127, graph and not alnum, alnum}
                -- Bits 0 to 7 sit in the high byte of each little-endian entry, 8 to 11 in the low byte.
                for bit, set in bits do
                    if set then value += if bit <= 8 then 2 ^ (bit + 7) else 2 ^ (bit - 9) end
                end
            end
        elseif i >= 0 then
            if kind == 1 and i >= 97 and i <= 122 then value -= 32 end
            if kind == 2 and i >= 65 and i <= 90 then value += 32 end
        elseif i < -1 then
            -- A negative signed char maps to its unsigned value; EOF stays -1.
            value = i + 256
        end
        write(width, first + (i + 128) * width, value % 4294967296, 0)
    end
    local cell = resize(0, 0, 8, 0)
    write(8, cell, first + 128 * width, 0)
    tables[kind] = cell
    return cell, 0
end

function libc.ctype_b_loc() return libc.ctypeTable(0) end
function libc.ctype_toupper_loc() return libc.ctypeTable(1) end
function libc.ctype_tolower_loc() return libc.ctypeTable(2) end

function libc.strstr(hayLo, hayHi, needleLo, needleHi)
    local haystack = address(hayLo, hayHi)
    local found = string.find(guestString(haystack), guestString(address(needleLo, needleHi)), 1, true)
    return if found then haystack + found - 1 else 0, 0
end

-- strtok_r and strtok_s keep the position in the caller's pointer, strtok in a slot of its own.
function libc.strtok_r(sLo, sHi, setLo, setHi, saveLo, saveHi)
    local save = address(saveLo, saveHi)
    local at = if sLo ~= 0 or sHi ~= 0 then address(sLo, sHi) else address(read(8, save))
    if at == 0 then return 0, 0 end
    at += span(at, 0, setLo, setHi, true)
    if read(1, at) == 0 then
        write(8, save, at, 0)
        return 0, 0
    end
    local token = at
    at += span(at, 0, setLo, setHi, false)
    if read(1, at) ~= 0 then
        write(1, at, 0, 0)
        at += 1
    end
    write(8, save, at, 0)
    return token, 0
end

function libc.strtok(sLo, sHi, setLo, setHi)
    if not libc.strtokSlot then
        libc.strtokSlot = resize(0, 0, 8, 0)
        write(8, libc.strtokSlot, 0, 0)
    end
    return libc.strtok_r(sLo, sHi, setLo, setHi, libc.strtokSlot, 0)
end

function libc.strnlen(sLo, sHi, limitLo, limitHi)
    local at, limit = address(sLo, sHi), if limitHi ~= 0 then math.huge else limitLo
    local length = 0
    while length < limit and read(1, at + length) ~= 0 do
        length += 1
    end
    return length, 0
end

-- Compares at most `limit` bytes with ASCII letters folded to lower case.
function libc.strncasecmp(aLo, aHi, bLo, bHi, limitLo, limitHi)
    local a, b = address(aLo, aHi), address(bLo, bHi)
    local limit = if limitHi ~= 0 then math.huge else limitLo
    local i = 0
    while i < limit do
        local x, y = read(1, a + i), read(1, b + i)
        if x >= 65 and x <= 90 then x += 32 end
        if y >= 65 and y <= 90 then y += 32 end
        if x ~= y or x == 0 then return result(x - y) end
        i += 1
    end
    return 0, 0
end

function libc.strcasecmp(aLo, aHi, bLo, bHi)
    return libc.strncasecmp(aLo, aHi, bLo, bHi, 0, 1)
end

function libc.strncpy(dstLo, dstHi, srcLo, srcHi, countLo, countHi)
    local count = address(countLo, countHi)
    local text = guestString(address(srcLo, srcHi), count)
    writeString(address(dstLo, dstHi), text)
    if #text < count then fillMemory(address(dstLo, dstHi) + #text, 0, 0, count - #text, 0) end
    return dstLo, dstHi
end

function libc.strncat(dstLo, dstHi, srcLo, srcHi, countLo, countHi)
    local dst = address(dstLo, dstHi)
    local text = guestString(address(srcLo, srcHi), address(countLo, countHi))
    local at = dst + stringLength(dst, 0)
    writeString(at, text)
    write(1, at + #text, 0, 0)
    return dstLo, dstHi
end

function libc.strdup(sLo, sHi)
    return newGuestString(guestString(address(sLo, sHi))), 0
end

-- The C library's message for an errno value: glibc's, Darwin's, or msvcrt's.
function host.errorMessage(code: number): string
    local glibc = {"Operation not permitted", "No such file or directory", "No such process", "Interrupted system call",
        "Input/output error", "No such device or address", "Argument list too long", "Exec format error",
        "Bad file descriptor", "No child processes", "Resource temporarily unavailable", "Cannot allocate memory",
        "Permission denied", "Bad address", "Block device required", "Device or resource busy", "File exists",
        "Invalid cross-device link", "No such device", "Not a directory", "Is a directory", "Invalid argument",
        "Too many open files in system", "Too many open files", "Inappropriate ioctl for device", "Text file busy",
        "File too large", "No space left on device", "Illegal seek", "Read-only file system", "Too many links",
        "Broken pipe", "Numerical argument out of domain", "Numerical result out of range", "Resource deadlock avoided",
        "File name too long", "No locks available", "Function not implemented", "Directory not empty",
        "Too many levels of symbolic links", [75] = "Value too large for defined data type",
        [84] = "Invalid or incomplete multibyte or wide character", [95] = "Operation not supported",
        [110] = "Connection timed out"}
    local darwin = {"Operation not permitted", "No such file or directory", "No such process", "Interrupted system call",
        "Input/output error", "Device not configured", "Argument list too long", "Exec format error",
        "Bad file descriptor", "No child processes", "Resource deadlock avoided", "Cannot allocate memory",
        "Permission denied", "Bad address", "Block device required", "Resource busy", "File exists",
        "Cross-device link", "Operation not supported by device", "Not a directory", "Is a directory",
        "Invalid argument", "Too many open files in system", "Too many open files", "Inappropriate ioctl for device",
        "Text file busy", "File too large", "No space left on device", "Illegal seek", "Read-only file system",
        "Too many links", "Broken pipe", "Numerical argument out of domain", "Result too large",
        "Resource temporarily unavailable", [45] = "Operation not supported", [60] = "Operation timed out",
        [62] = "Too many levels of symbolic links", [63] = "File name too long", [66] = "Directory not empty",
        [78] = "Function not implemented", [84] = "Value too large to be stored in data type",
        [92] = "Illegal byte sequence"}
    local windows = {"Operation not permitted", "No such file or directory", "No such process", "Interrupted function call",
        "Input/output error", "No such device or address", "Arg list too long", "Exec format error",
        "Bad file descriptor", "No child processes", "Resource temporarily unavailable", "Not enough space",
        "Permission denied", "Bad address", "Unknown error", "Resource device", "File exists", "Improper link",
        "No such device", "Not a directory", "Is a directory", "Invalid argument", "Too many open files in system",
        "Too many open files", "Inappropriate I/O control operation", "Unknown error", "File too large",
        "No space left on device", "Invalid seek", "Read-only file system", "Too many links", "Broken pipe",
        "Domain error", "Result too large", "Unknown error", "Resource deadlock avoided", "Unknown error",
        "Filename too long", "No locks available", "Function not implemented", "Directory not empty",
        "Illegal byte sequence"}
    if code == 0 then
        return if libc.windows then "No error" elseif libc.darwin then "Undefined error: 0" else "Success"
    end
    local message = (if libc.windows then windows elseif libc.darwin then darwin else glibc)[code]
    if message then return message end
    return if libc.windows then "Unknown error" elseif libc.darwin then "Unknown error: " .. code
        else "Unknown error " .. code
end

function libc.strerror(code)
    return cachedString(host.errorMessage(signed32(code))), 0
end

-- XSI strerror_r (Darwin's, and glibc's __xpg_strerror_r) returns 0; glibc's GNU strerror_r, which C++ programs
-- get, returns the message.
function libc.strerror_r(code, codeHi, bufLo, bufHi, sizeLo, sizeHi)
    local text = string.sub(host.errorMessage(signed32(code)), 1, math.max(address(sizeLo, sizeHi) - 1, 0))
    writeString(address(bufLo, bufHi), text)
    write(1, address(bufLo, bufHi) + #text, 0, 0)
    return 0, 0
end

function libc.strerror_gnu(code, codeHi, bufLo, bufHi, sizeLo, sizeHi)
    libc.strerror_r(code, codeHi, bufLo, bufHi, sizeLo, sizeHi)
    return bufLo, bufHi
end

function libc.aligned_alloc(alignLo, alignHi, sizeLo, sizeHi)
    -- Heap allocations are 16-byte aligned; larger alignments are not available.
    if address(alignLo, alignHi) > 16 then return 0, 0 end
    return resize(0, 0, math.max(address(sizeLo, sizeHi), 1), 0), 0
end
)luau", R"luau(
-- Darwin's malloc zones all share the one heap: a zone's functions take the zone first and ignore it.
function libc.allocationSize(ptrLo, ptrHi)
    return (process.heapLength :: any)(address(ptrLo, ptrHi)) or 0, 0
end

function libc.zoneSize(zoneLo, zoneHi, ptrLo, ptrHi)
    return libc.allocationSize(ptrLo, ptrHi)
end

function libc.zoneMalloc(zoneLo, zoneHi, sizeLo, sizeHi)
    return resize(0, 0, math.max(address(sizeLo, sizeHi), 1), 0), 0
end

function libc.zoneCalloc(zoneLo, zoneHi, countLo, countHi, sizeLo, sizeHi)
    return resize(0, 0, math.max(address(countLo, countHi) * address(sizeLo, sizeHi), 1), 0), 0
end

function libc.zoneFree(zoneLo, zoneHi, ptrLo, ptrHi)
    resize(ptrLo, ptrHi, 0, 0)
    return 0, 0
end

function libc.zoneRealloc(zoneLo, zoneHi, ptrLo, ptrHi, sizeLo, sizeHi)
    return resize(ptrLo, ptrHi, sizeLo, sizeHi)
end

function libc.zoneMemalign(zoneLo, zoneHi, alignLo, alignHi, sizeLo, sizeHi)
    return libc.aligned_alloc(alignLo, alignHi, sizeLo, sizeHi)
end

-- Page-aligned allocations are not available, as aligned_alloc reports for alignments past 16.
function libc.zoneValloc(zoneLo, zoneHi, sizeLo, sizeHi)
    return 0, 0
end

function libc.zoneGoodSize(sizeLo, sizeHi)
    return result(math.max(math.ceil(address(sizeLo, sizeHi) / 16) * 16, 16))
end

function libc.posix_memalign(pointerLo, pointerHi, alignLo, alignHi, sizeLo, sizeHi)
    if address(alignLo, alignHi) > 16 then return 12, 0 end
    write(8, address(pointerLo, pointerHi), resize(0, 0, math.max(address(sizeLo, sizeHi), 1), 0), 0)
    return 0, 0
end

function libc.mach_absolute_time()
    return result(math.floor(os.clock() * 1e9))
end

function libc.mach_timebase_info(lo, hi)
    write(4, address(lo, hi), 1, 0)
    write(4, address(lo, hi) + 4, 1, 0)
    return 0, 0
end

function libc.failure()
    return 0, 0
end

-- No message catalogs are installed, so messages stay untranslated.
function libc.gettext(lo: number, hi: number): (number, number)
    return lo, hi
end

function libc.dgettext(domainLo: number, domainHi: number, lo: number, hi: number): (number, number)
    return lo, hi
end
)luau", R"luau(
-- KERNEL32 for programs built against the Windows CRT. Every entry receives the four register arguments as
-- (lo, hi) pairs followed by the stack pointer; later arguments live above the 32-byte shadow space.
local win32 = {}
local windowsHandles: {[number]: number} = {[0x10] = 0, [0x14] = 1, [0x18] = 2}
local nextWindowsHandle = 0x100
local windowsTls: {[number]: {lo: number, hi: number}} = {}
local nextWindowsTls = 1

local function stackArgument(sp: number, index: number): (number, number)
    return read(8, sp + 32 + (index - 4) * 8)
end

local function readWide(at: number, count: number?): string
    local chars = {}
    local i = 0
    while count == nil or i < count do
        local unit = read(2, at + i * 2)
        if count == nil and unit == 0 then break end
        table.insert(chars, if unit < 256 then string.char(unit) else "?")
        i += 1
    end
    return table.concat(chars)
end

local function writeWide(at: number, text: string, terminate: boolean)
    for i = 1, #text do write(2, at + (i - 1) * 2, string.byte(text, i), 0) end
    if terminate then write(2, at + #text * 2, 0, 0) end
end

local function newGuestWide(text: string): number
    local at = resize(0, 0, (#text + 1) * 2, 0)
    writeWide(at, text, true)
    return at
end

local function commandLine(): string
    local parts = {}
    for i, argument in host.args do
        if i == 1 or string.find(argument, "[ \t\"]") or argument == "" then
            table.insert(parts, '"' .. string.gsub(argument, '"', '\\"') .. '"')
        else
            table.insert(parts, argument)
        end
    end
    return table.concat(parts, " ")
end

local function handleDescriptor(lo: number, hi: number): number?
    return if hi == 0 then windowsHandles[lo] else nil
end

function win32.GetStdHandle(lo)
    local index = signed32(lo)
    if index == -10 then return 0x10, 0 elseif index == -11 then return 0x14, 0 elseif index == -12 then return 0x18, 0 end
    return 4294967295, 4294967295
end

function win32.GetFileType(lo, hi)
    local fd = handleDescriptor(lo, hi)
    if fd == nil then return 0, 0 end
    -- Standard handles report pipes so the CRT uses byte I/O rather than the console API.
    return if fd <= 2 then 3 else 1, 0
end

function win32.WriteFile(hLo, hHi, bufLo, bufHi, countLo, countHi, writtenLo, writtenHi)
    local fd = handleDescriptor(hLo, hHi)
    local text = readString(address(bufLo, bufHi), countLo)
    if fd == nil or not hostWrite(fd, text) then process.lastError = 6; return 0, 0 end
    if writtenLo ~= 0 or writtenHi ~= 0 then write(4, address(writtenLo, writtenHi), #text, 0) end
    return 1, 0
end

function win32.ReadFile(hLo, hHi, bufLo, bufHi, countLo, countHi, readLo, readHi)
    local fd = handleDescriptor(hLo, hHi)
    local text = if fd ~= nil then hostRead(fd, countLo) else nil
    if text == nil then process.lastError = 6; return 0, 0 end
    writeString(address(bufLo, bufHi), text)
    if readLo ~= 0 or readHi ~= 0 then write(4, address(readLo, readHi), #text, 0) end
    return 1, 0
end

function win32.WriteConsoleW(hLo, hHi, bufLo, bufHi, countLo, countHi, writtenLo, writtenHi)
    local fd = handleDescriptor(hLo, hHi)
    if fd == nil then return 0, 0 end
    hostWrite(fd, readWide(address(bufLo, bufHi), countLo))
    if writtenLo ~= 0 or writtenHi ~= 0 then write(4, address(writtenLo, writtenHi), countLo, 0) end
    return 1, 0
end

-- A Windows path in the guest's POSIX file system: separators become slashes, and a drive is the root.
function host.windowsPath(path: string): string
    path = string.gsub(path, "\\", "/")
    path = string.gsub(path, "^//%?/", "")
    path = string.gsub(path, "^%a:/", "/")
    return host.canonical(path)
end

function win32.CreateFileW(nameLo, nameHi, accessLo, accessHi, shareLo, shareHi, securityLo, securityHi, sp)
    local path = host.windowsPath(readWide(address(nameLo, nameHi)))
    local disposition = stackArgument(sp, 4)
    local readable = bit32.btest(accessLo, 0x80000000) or bit32.btest(accessLo, 0x10000000)
    local writable = bit32.btest(accessLo, 0x40000000) or bit32.btest(accessLo, 0x10000000)
    local exists = host.files[path] ~= nil
    if (disposition == 1 and exists) or ((disposition == 3 or disposition == 5) and not exists) then
        process.lastError = if exists then 80 else 2
        return 4294967295, 4294967295
    end
    local fd = hostOpen(path, readable, writable, disposition ~= 3 and disposition ~= 5,
        disposition == 2 or disposition == 5, false)
    if not fd then process.lastError = 2; return 4294967295, 4294967295 end
    local handle = nextWindowsHandle
    nextWindowsHandle += 4
    windowsHandles[handle] = fd
    process.lastError = if exists and (disposition == 2 or disposition == 4) then 183 else 0
    return handle, 0
end

function win32.CloseHandle(lo, hi)
    local fd = handleDescriptor(lo, hi)
    if fd and fd > 2 then
        hostClose(fd)
        windowsHandles[lo] = nil
    end
    return 1, 0
end

function win32.GetFileSizeEx(hLo, hHi, sizeLo, sizeHi)
    local fd = handleDescriptor(hLo, hHi)
    local file = if fd then host.descriptors[fd] else nil
    if not file then process.lastError = 6; return 0, 0 end
    write(8, address(sizeLo, sizeHi), result(file.contents.size))
    return 1, 0
end

function win32.SetFilePointerEx(hLo, hHi, distanceLo, distanceHi, newLo, newHi, methodLo)
    local fd = handleDescriptor(hLo, hHi)
    local position = if fd then hostSeek(fd, signed64(distanceLo, distanceHi), methodLo) else nil
    if not position then process.lastError = 131; return 0, 0 end
    if newLo ~= 0 or newHi ~= 0 then write(8, address(newLo, newHi), result(position)) end
    return 1, 0
end

function win32.SetEndOfFile(hLo, hHi)
    local fd = handleDescriptor(hLo, hHi)
    local file = if fd then host.descriptors[fd] else nil
    if not file or not file.writable then process.lastError = if file then 5 else 6; return 0, 0 end
    host.truncateFile(file.contents, file.at)
    return 1, 0
end

function win32.GetCommandLineW()
    if host.strings["\0commandW"] == nil then host.strings["\0commandW"] = newGuestWide(commandLine()) end
    return host.strings["\0commandW"], 0
end

function win32.GetCommandLineA()
    return cachedString(commandLine()), 0
end

-- The executable's full path, as Windows names it: the program's name resolved against the working directory,
-- with the drive that every absolute path is on.
function host.modulePath(): string
    local name = host.args[1] or "program.exe"
    if string.find(name, "^%a:[\\/]") or string.find(name, "^[\\/][\\/]") then
        return (string.gsub(name, "/", "\\"))
    end
    return "C:" .. string.gsub(host.windowsPath(name), "/", "\\")
end

function win32.GetModuleFileNameW(moduleLo, moduleHi, bufLo, bufHi, sizeLo)
    local name = string.sub(host.modulePath(), 1, math.max(sizeLo - 1, 0))
    writeWide(address(bufLo, bufHi), name, true)
    return #name, 0
end

function win32.GetModuleFileNameA(moduleLo, moduleHi, bufLo, bufHi, sizeLo)
    local name = string.sub(host.modulePath(), 1, math.max(sizeLo - 1, 0))
    writeString(address(bufLo, bufHi), name)
    write(1, address(bufLo, bufHi) + #name, 0, 0)
    return #name, 0
end

function win32.GetEnvironmentStringsW()
    local block = table.concat(host.env, "\0") .. "\0\0"
    local at = resize(0, 0, #block * 2 + 2, 0)
    writeWide(at, block, true)
    return at, 0
end

function win32.GetStartupInfoW(lo, hi)
    fillMemory(address(lo, hi), 0, 0, 104, 0)
    write(4, address(lo, hi), 104, 0)
    return 0, 0
end

function win32.GetCPInfo(codeLo, codeHi, infoLo, infoHi)
    local at = address(infoLo, infoHi)
    fillMemory(at, 0, 0, 20, 0)
    write(4, at, if codeLo == 65001 then 4 else 1, 0)
    write(1, at + 4, 63, 0)
    return 1, 0
end

function win32.GetACP()
    return 1252, 0
end

function win32.GetOEMCP()
    return 437, 0
end

function win32.MultiByteToWideChar(codeLo, codeHi, flagsLo, flagsHi, srcLo, srcHi, countLo, countHi, sp)
    local dst = address(stackArgument(sp, 4))
    local capacity = signed32((stackArgument(sp, 5)))
    local src = address(srcLo, srcHi)
    local count = signed32(countLo)
    local text = if count < 0 then guestString(src) .. "\0" else readString(src, count)
    if capacity == 0 then return #text, 0 end
    if #text > capacity then process.lastError = 122; return 0, 0 end
    writeWide(dst, text, false)
    return #text, 0
end

function win32.WideCharToMultiByte(codeLo, codeHi, flagsLo, flagsHi, srcLo, srcHi, countLo, countHi, sp)
    local dst = address(stackArgument(sp, 4))
    local capacity = signed32((stackArgument(sp, 5)))
    local src = address(srcLo, srcHi)
    local count = signed32(countLo)
    local text = if count < 0 then readWide(src) .. "\0" else readWide(src, count)
    if capacity == 0 then return #text, 0 end
    if #text > capacity then process.lastError = 122; return 0, 0 end
    writeString(dst, text)
    return #text, 0
end

local function mapCase(text: string, flags: number): string
    if bit32.btest(flags, 0x200) then return string.upper(text) end
    if bit32.btest(flags, 0x100) then return string.lower(text) end
    return text
end

-- LCMapStringW(locale, flags, src, count, dst, capacity); the Ex form adds a version and reserved words.
local function mapString(flags: number, src: number, count: number, dst: number, capacity: number): (number, number)
    local text = if count < 0 then readWide(src) .. "\0" else readWide(src, count)
    text = mapCase(text, flags)
    if capacity == 0 then return #text, 0 end
    if #text > capacity then process.lastError = 122; return 0, 0 end
    writeWide(dst, text, false)
    return #text, 0
end

function win32.LCMapStringW(localeLo, localeHi, flagsLo, flagsHi, srcLo, srcHi, countLo, countHi, sp)
    return mapString(flagsLo, address(srcLo, srcHi), signed32(countLo), address(stackArgument(sp, 4)),
        signed32((stackArgument(sp, 5))))
end

function win32.LCMapStringEx(localeLo, localeHi, flagsLo, flagsHi, srcLo, srcHi, countLo, countHi, sp)
    return mapString(flagsLo, address(srcLo, srcHi), signed32(countLo), address(stackArgument(sp, 4)),
        signed32((stackArgument(sp, 5))))
end

function win32.GetStringTypeW(typeLo, typeHi, srcLo, srcHi, countLo, countHi, typesLo, typesHi)
    local src, count = address(srcLo, srcHi), signed32(countLo)
    if count < 0 then count = #readWide(src) + 1 end
    for i = 0, count - 1 do
        local c = read(2, src + i * 2)
        local bits = 0
        if typeLo == 1 then
            local upper, lower = c >= 65 and c <= 90, c >= 97 and c <= 122
            local digit = c >= 48 and c <= 57
            if upper then bits += 0x1 end
            if lower then bits += 0x2 end
            if digit then bits += 0x4 end
            if c == 32 or (c >= 9 and c <= 13) then bits += 0x8 end
            if c >= 33 and c <= 126 and not (upper or lower or digit) then bits += 0x10 end
            if c < 32 or c == 127 then bits += 0x20 end
            if c == 32 or c == 9 then bits += 0x40 end
            if digit or (c >= 65 and c <= 70) or (c >= 97 and c <= 102) then bits += 0x80 end
            if upper or lower then bits += 0x100 end
            if c < 128 then bits += 0x200 end
        end
        write(2, address(typesLo, typesHi) + i * 2, bits, 0)
    end
    return 1, 0
end

function win32.CompareStringW(localeLo, localeHi, flagsLo, flagsHi, aLo, aHi, aCountLo, aCountHi, sp)
    local bLo, bHi = stackArgument(sp, 4)
    local bCount = signed32((stackArgument(sp, 5)))
    local aCount = signed32(aCountLo)
    local a = if aCount < 0 then readWide(address(aLo, aHi)) else readWide(address(aLo, aHi), aCount)
    local b = if bCount < 0 then readWide(address(bLo, bHi)) else readWide(address(bLo, bHi), bCount)
    if bit32.btest(flagsLo, 1) then a, b = string.lower(a), string.lower(b) end
    return if a < b then 1 elseif a == b then 2 else 3, 0
end

function win32.GetLocaleInfoW()
    process.lastError = 87
    return 0, 0
end

function win32.GetUserDefaultLCID()
    return 0x409, 0
end

function win32.QueryPerformanceCounter(lo, hi)
    write(8, address(lo, hi), result(math.floor(os.clock() * 1e7)))
    return 1, 0
end

function win32.QueryPerformanceFrequency(lo, hi)
    write(8, address(lo, hi), 10000000, 0)
    return 1, 0
end

function win32.GetSystemTimeAsFileTime(lo, hi)
    -- 100-nanosecond intervals since 1601.
    local ticks = (os.time() + 11644473600) * 10000000
    write(8, address(lo, hi), result(ticks))
    return 0, 0
end

function win32.GetCurrentProcessId()
    return 0x1000, 0
end

function win32.GetCurrentThreadId()
    return 0x1004, 0
end

function win32.GetCurrentProcess()
    return 4294967295, 4294967295
end

function win32.ExitProcess(code)
    exitProcess(code, false)
    return 0, 0
end

function win32.TerminateProcess(hLo, hHi, code)
    exitProcess(code, false)
    return 0, 0
end

function win32.IsProcessorFeaturePresent(feature)
    -- Report SSE2 (PF_XMMI64_INSTRUCTIONS_AVAILABLE) as the baseline and nothing else.
    return if feature == 10 then 1 else 0, 0
end

function win32.InitializeSListHead(lo, hi)
    fillMemory(address(lo, hi), 0, 0, 16, 0)
    return 0, 0
end

function win32.TlsAlloc()
    local index = nextWindowsTls
    nextWindowsTls += 1
    windowsTls[index] = {lo = 0, hi = 0}
    return index, 0
end

function win32.TlsGetValue(index)
    local slot = windowsTls[index]
    process.lastError = 0
    if not slot then return 0, 0 end
    return slot.lo, slot.hi
end

function win32.TlsSetValue(index, indexHi, lo, hi)
    windowsTls[index] = {lo = lo, hi = hi}
    return 1, 0
end

function win32.TlsFree(index)
    windowsTls[index] = nil
    return 1, 0
end

function win32.RaiseException(code)
    error(string.format("guest raised Windows exception 0x%08x", code), 0)
    return 0, 0
end

function win32.FindFirstFileExW()
    process.lastError = 2
    return 4294967295, 4294967295
end

function win32.GetTimeZoneInformation(sp, spHi, lo, hi)
    return 0, 0
end

function win32.VirtualQuery(lo, hi, infoLo, infoHi, sizeLo)
    -- Report every page as committed read-write memory.
    local at = address(infoLo, infoHi)
    local page = lo - lo % 4096
    fillMemory(at, 0, 0, 48, 0)
    write(8, at, page, 0)
    write(8, at + 8, page, 0)
    write(4, at + 16, 4, 0)
    write(8, at + 24, 4096, 0)
    write(4, at + 32, 0x1000, 0)
    write(4, at + 36, 4, 0)
    write(4, at + 40, 0x20000, 0)
    return 48, 0
end

function win32.yes()
    return 1, 0
end

function win32.no()
    return 0, 0
end

function libc.strcoll(aLo, aHi, bLo, bHi)
    return compareStrings(aLo, aHi, bLo, bHi)
end

function libc.isspace(c)
    return if c == 32 or (c >= 9 and c <= 13) then 1 else 0, 0
end

-- The other ctype.h classes in the C locale, where only ASCII characters belong to any.
for name, member in {
    isdigit = function(c: number) return c >= 48 and c <= 57 end,
    isupper = function(c: number) return c >= 65 and c <= 90 end,
    islower = function(c: number) return c >= 97 and c <= 122 end,
    isalpha = function(c: number) return (c >= 65 and c <= 90) or (c >= 97 and c <= 122) end,
    isalnum = function(c: number) return (c >= 48 and c <= 57) or (c >= 65 and c <= 90) or (c >= 97 and c <= 122) end,
    isxdigit = function(c: number) return (c >= 48 and c <= 57) or (c >= 65 and c <= 70) or (c >= 97 and c <= 102) end,
    isblank = function(c: number) return c == 32 or c == 9 end,
    iscntrl = function(c: number) return c < 32 or c == 127 end,
    isprint = function(c: number) return c >= 32 and c <= 126 end,
    isgraph = function(c: number) return c >= 33 and c <= 126 end,
    ispunct = function(c: number)
        return (c >= 33 and c <= 47) or (c >= 58 and c <= 64) or (c >= 91 and c <= 96) or (c >= 123 and c <= 126)
    end,
} :: {[string]: (number) -> boolean} do
    (libc :: any)[name] = function(c: number): (number, number)
        return if c < 128 and member(c) then 1 else 0, 0
    end
end
)luau", R"luau(
function libc.sigaction()
    return 0, 0
end
)luau", R"luau(
-- Signal sets: glibc's sigset_t holds 1024 bits, Darwin's 32; signal n is bit n - 1. No signal ever arrives, so
-- masks have nothing to block, and a mask's previous value is empty.
function host.signalBit(setLo, setHi, signalLo): (number?, number)
    local signal = signed32(signalLo)
    if signal < 1 or signal > (if libc.darwin then 32 else 64) then setErrno(22); return nil, 0 end
    return address(setLo, setHi) + (signal - 1) // 8, 2 ^ ((signal - 1) % 8)
end

function host.fillSignals(setLo, setHi, word: number)
    local at = address(setLo, setHi)
    for offset = 0, (if libc.darwin then 4 else 128) - 4, 4 do write(4, at + offset, word, 0) end
end

function libc.sigemptyset(setLo, setHi)
    host.fillSignals(setLo, setHi, 0)
    return 0, 0
end

function libc.sigfillset(setLo, setHi)
    host.fillSignals(setLo, setHi, 4294967295)
    return 0, 0
end

function libc.sigaddset(setLo, setHi, signalLo)
    local at, bit = host.signalBit(setLo, setHi, signalLo)
    if not at then return result(-1) end
    write(1, at, bit32.bor(read(1, at), bit), 0)
    return 0, 0
end

function libc.sigdelset(setLo, setHi, signalLo)
    local at, bit = host.signalBit(setLo, setHi, signalLo)
    if not at then return result(-1) end
    write(1, at, bit32.band(read(1, at), 255 - bit), 0)
    return 0, 0
end

function libc.sigismember(setLo, setHi, signalLo)
    local at, bit = host.signalBit(setLo, setHi, signalLo)
    if not at then return result(-1) end
    return if bit32.btest(read(1, at), bit) then 1 else 0, 0
end

function libc.sigprocmask(howLo, howHi, setLo, setHi, oldLo, oldHi)
    if oldLo ~= 0 or oldHi ~= 0 then host.fillSignals(oldLo, oldHi, 0) end
    return 0, 0
end
)luau", R"luau(
-- Calendar time. struct tm is nine ints; Linux and Darwin add tm_gmtoff and tm_zone after them, Windows does not.
-- Local time is the host's, as os.date reports it.
function host.writeCalendar(at: number, t: number, utc: boolean): boolean
    local ok, fields = pcall(os.date, if utc then "!*t" else "*t", t)
    if not ok or type(fields) ~= "table" then return false end
    local values = {fields.sec, fields.min, fields.hour, fields.day, fields.month - 1, fields.year - 1900,
        fields.wday - 1, fields.yday - 1, if fields.isdst then 1 else 0}
    for index, value in values do
        write(4, at + (index - 1) * 4, value % 4294967296, 0)
    end
    if not libc.windows then
        local offset = 0
        if not utc then
            local universal = os.date("!*t", t) :: any
            universal.isdst = fields.isdst
            offset = t - os.time(universal)
        end
        write(8, at + 40, result(offset))
        write(8, at + 48, cachedString(if utc then "UTC" else (os.date("%Z", t) :: string)), 0)
    end
    return true
end

function host.readCalendar(at: number): {[string]: number}
    local function field(index: number): number return signed32((read(4, at + index * 4))) end
    return {sec = field(0), min = field(1), hour = field(2), day = field(3), month = field(4) + 1,
        year = field(5) + 1900, isdst = field(8)}
end

-- Days from 1970-01-01 to a proleptic Gregorian date (Howard Hinnant's days_from_civil).
function host.civilDays(year: number, month: number, day: number): number
    year -= if month <= 2 then 1 else 0
    local era = (if year >= 0 then year else year - 399) // 400
    local yoe = year - era * 400
    local doy = (153 * (month + (if month > 2 then -3 else 9)) + 2) // 5 + day - 1
    local doe = yoe * 365 + yoe // 4 - yoe // 100 + doy
    return era * 146097 + doe - 719468
end

function host.calendarResult(timeLo: number, timeHi: number, at: number, utc: boolean): (number, number)
    local t = signed64(read(8, address(timeLo, timeHi)))
    if not host.writeCalendar(at, t, utc) then setErrno(75); return 0, 0 end
    return at, 0
end

function libc.gmtime_r(timeLo, timeHi, tmLo, tmHi)
    return host.calendarResult(timeLo, timeHi, address(tmLo, tmHi), true)
end

function libc.localtime_r(timeLo, timeHi, tmLo, tmHi)
    return host.calendarResult(timeLo, timeHi, address(tmLo, tmHi), false)
end

-- gmtime and localtime return one static struct tm.
function libc.gmtime(timeLo, timeHi)
    host.calendar = host.calendar or resize(0, 0, 64, 0)
    return host.calendarResult(timeLo, timeHi, host.calendar :: number, true)
end

function libc.localtime(timeLo, timeHi)
    host.calendar = host.calendar or resize(0, 0, 64, 0)
    return host.calendarResult(timeLo, timeHi, host.calendar :: number, false)
end

-- Windows' _gmtime64_s and _localtime64_s take the struct first and return an errno value.
function libc.gmtime_s(tmLo, tmHi, timeLo, timeHi)
    local at = host.calendarResult(timeLo, timeHi, address(tmLo, tmHi), true)
    return if at == 0 then 22 else 0, 0
end

function libc.localtime_s(tmLo, tmHi, timeLo, timeHi)
    local at = host.calendarResult(timeLo, timeHi, address(tmLo, tmHi), false)
    return if at == 0 then 22 else 0, 0
end

function libc.mktime(tmLo, tmHi)
    local at = address(tmLo, tmHi)
    local fields = host.readCalendar(at) :: any
    if fields.isdst < 0 then fields.isdst = nil else fields.isdst = fields.isdst > 0 end
    local ok, t = pcall(os.time, fields)
    if not ok or type(t) ~= "number" or not host.writeCalendar(at, t, false) then setErrno(75); return result(-1) end
    return result(t)
end

function libc.timegm(tmLo, tmHi)
    local at = address(tmLo, tmHi)
    local f = host.readCalendar(at)
    local months = f.month - 1
    local year = f.year + months // 12
    local t = ((host.civilDays(year, months % 12 + 1, 1) + f.day - 1) * 24 + f.hour) * 3600 + f.min * 60 + f.sec
    host.writeCalendar(at, t, true)
    return result(t)
end

host.monthNames = {"January", "February", "March", "April", "May", "June", "July", "August", "September",
    "October", "November", "December"}
host.dayNames = {"Sunday", "Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday"}

-- strftime in the C locale.
function host.formatCalendar(format: string, at: number): string
    local function field(index: number): number return signed32((read(4, at + index * 4))) end
    local sec, min, hour, day, month, year = field(0), field(1), field(2), field(3), field(4), field(5) + 1900
    local wday, yday = field(6), field(7)
    local zone = if libc.windows then "" else guestString(address(read(8, at + 48)))
    local offset = if libc.windows then 0 else signed64(read(8, at + 40))
    local function weekNumber(first: number): number return (yday + 7 - ((wday - first) % 7)) // 7 end
    local function isoWeek(): (number, number)
        local weekday = (wday + 6) % 7
        local week = (yday - weekday + 10) // 7
        local isoYear = year
        local function weeksIn(y: number): number
            local jan1 = (host.civilDays(y, 1, 1) + 4) % 7
            local leap = (y % 4 == 0 and y % 100 ~= 0) or y % 400 == 0
            return if jan1 == 4 or (leap and jan1 == 3) then 53 else 52
        end
        if week < 1 then
            isoYear -= 1
            week = weeksIn(isoYear)
        elseif week > weeksIn(year) then
            isoYear += 1
            week = 1
        end
        return isoYear, week
    end
    local out = {}
    local i = 1
    while i <= #format do
        local c = string.sub(format, i, i)
        if c ~= "%" or i == #format then
            table.insert(out, c)
            i += 1
        else
            local spec = string.sub(format, i + 1, i + 1)
            i += 2
            if spec == "E" or spec == "O" then
                spec = string.sub(format, i, i)
                i += 1
            end
            local text
            if spec == "a" then text = string.sub(host.dayNames[wday % 7 + 1], 1, 3)
            elseif spec == "A" then text = host.dayNames[wday % 7 + 1]
            elseif spec == "b" or spec == "h" then text = string.sub(host.monthNames[month % 12 + 1], 1, 3)
            elseif spec == "B" then text = host.monthNames[month % 12 + 1]
            elseif spec == "c" then text = host.formatCalendar("%a %b %e %H:%M:%S %Y", at)
            elseif spec == "C" then text = string.format("%02d", year // 100)
            elseif spec == "d" then text = string.format("%02d", day)
            elseif spec == "D" then text = host.formatCalendar("%m/%d/%y", at)
            elseif spec == "e" then text = string.format("%2d", day)
            elseif spec == "F" then text = host.formatCalendar("%Y-%m-%d", at)
            elseif spec == "g" then text = string.format("%02d", (isoWeek()) % 100)
            elseif spec == "G" then text = tostring((isoWeek()))
            elseif spec == "H" then text = string.format("%02d", hour)
            elseif spec == "I" then text = string.format("%02d", (hour + 11) % 12 + 1)
            elseif spec == "j" then text = string.format("%03d", yday + 1)
            elseif spec == "k" then text = string.format("%2d", hour)
            elseif spec == "l" then text = string.format("%2d", (hour + 11) % 12 + 1)
            elseif spec == "m" then text = string.format("%02d", month + 1)
            elseif spec == "M" then text = string.format("%02d", min)
            elseif spec == "n" then text = "\n"
            elseif spec == "p" then text = if hour < 12 then "AM" else "PM"
            elseif spec == "P" then text = if hour < 12 then "am" else "pm"
            elseif spec == "r" then text = host.formatCalendar("%I:%M:%S %p", at)
            elseif spec == "R" then text = host.formatCalendar("%H:%M", at)
            elseif spec == "s" then
                text = tostring(((host.civilDays(year, month + 1, day) * 24 + hour) * 3600 + min * 60 + sec) - offset)
            elseif spec == "S" then text = string.format("%02d", sec)
            elseif spec == "t" then text = "\t"
            elseif spec == "T" then text = host.formatCalendar("%H:%M:%S", at)
            elseif spec == "u" then text = tostring((wday + 6) % 7 + 1)
            elseif spec == "U" then text = string.format("%02d", weekNumber(0))
            elseif spec == "V" then text = string.format("%02d", select(2, isoWeek()))
            elseif spec == "w" then text = tostring(wday)
            elseif spec == "W" then text = string.format("%02d", weekNumber(1))
            elseif spec == "x" then text = host.formatCalendar("%m/%d/%y", at)
            elseif spec == "X" then text = host.formatCalendar("%H:%M:%S", at)
            elseif spec == "y" then text = string.format("%02d", year % 100)
            elseif spec == "Y" then text = tostring(year)
            elseif spec == "z" then
                local magnitude = math.abs(offset) // 60
                text = string.format("%s%02d%02d", if offset < 0 then "-" else "+", magnitude // 60, magnitude % 60)
            elseif spec == "Z" then text = zone
            elseif spec == "%" then text = "%"
            else text = "%" .. spec end
            table.insert(out, text)
        end
    end
    return table.concat(out)
end

function libc.strftime(bufLo, bufHi, maxLo, maxHi, formatLo, formatHi, tmLo, tmHi)
    local text = host.formatCalendar(guestString(address(formatLo, formatHi)), address(tmLo, tmHi))
    local limit = address(maxLo, maxHi)
    if #text + 1 > limit then return 0, 0 end
    writeString(address(bufLo, bufHi), text)
    write(1, address(bufLo, bufHi) + #text, 0, 0)
    return result(#text)
end

-- Sleeping takes no time beyond giving the other guest threads a turn.
function libc.nanosleep(requestLo, requestHi, remainLo, remainHi)
    if remainLo ~= 0 or remainHi ~= 0 then fillMemory(address(remainLo, remainHi), 0, 0, 16, 0) end
    return libc.yieldThread()
end

-- Guest threads take turns: each runs as a coroutine with its own registers, stack, errno, keys, and Darwin
-- thread-local variables until it blocks (joining, waiting on a condition variable or a mutex another thread
-- holds, or yielding), and the main thread runs the others while it waits. Threads therefore switch only where
-- they block, at routine boundaries.
-- Runs one other thread that can make progress for a turn, and says whether there was one.
function host.runOther(): boolean
    local count = #host.threads
    for step = 1, count do
        host.nextTurn = (host.nextTurn or 0) % count + 1
        local thread = host.threads[host.nextTurn :: number]
        if host.runnable(thread) then
            thread.ready = nil
            local main = host.mainThread
            main.context = (process.saveRegisters :: any)()
            if thread.context then (process.restoreRegisters :: any)(thread.context) end
            -- ELF thread-local blocks sit at fixed addresses: each thread's contents take their place in turn.
            main.blocks = main.blocks or {}
            thread.blocks = thread.blocks or {}
            for start, initial in process.threadBlocks do
                main.blocks[start] = readString(start, #initial)
                writeString(start, thread.blocks[start] or initial)
            end
            host.current = thread
            process.threadErrno = thread.errno
            local ok, first, second = coroutine.resume(thread.co)
            for start, initial in process.threadBlocks do
                thread.blocks[start] = readString(start, #initial)
                writeString(start, main.blocks[start])
            end
            if coroutine.status(thread.co) == "dead" then
                thread.finished = true
                if ok then
                    thread.resultLo, thread.resultHi = first, second
                elseif type(first) == "table" and (first :: any).luftThreadExit then
                    ok = true
                    thread.resultLo, thread.resultHi = (first :: any).lo, (first :: any).hi
                end
                resize(thread.stack, 0, 0, 0)
            else
                thread.context = (process.saveRegisters :: any)()
            end
            ;(process.restoreRegisters :: any)(main.context)
            host.current = main
            process.threadErrno = nil
            if not ok then error(first, 0) end
            if host.hostYield and os.clock() - process.yieldAt >= process.yieldInterval then
                host.hostYield()
                process.yieldAt = os.clock()
            end
            return true
        end
    end
    return false
end

-- Whether a thread can take a turn. Evaluating a wait can ask about the other threads, whose waits may ask about
-- it in turn: a thread being asked about already counts as unable.
function host.runnable(thread: any): boolean
    if thread.finished or thread.evaluating then return false end
    if thread.ready == nil then return true end
    thread.evaluating = true
    local ok, ready = pcall(thread.ready)
    thread.evaluating = nil
    if not ok then error(ready, 0) end
    return ready
end

-- Whether a thread other than `me` (and the main thread, which runs them) can take a turn.
function host.othersRunnable(me: any): boolean
    for _, thread in host.threads do
        if thread ~= me and host.runnable(thread) then return true end
    end
    return false
end

-- Waits until `ready` holds: another thread's turn ends where it blocks, and the main thread runs the others
-- meanwhile. Nothing being able to run then is a deadlock.
function host.block(ready: () -> boolean)
    if ready() then return end
    if not host.current.main then
        host.current.ready = ready
        coroutine.yield()
        return
    end
    while not ready() do
        if not host.runOther() then error("guest threads deadlocked", 0) end
    end
end

-- sched_yield and sleeping give the other threads a turn.
function libc.yieldThread()
    if #host.threads == 0 then return 0, 0 end
    if host.current.main then
        host.runOther()
    else
        host.current.ready = nil
        coroutine.yield()
    end
    return 0, 0
end

-- A thread for `body`, which receives the top of its stack and returns the thread's result, or nil when there is
-- no memory for its stack.
function host.createThread(body: (number) -> (number, number)): any
    local stackSize = 1048576
    local stack = resize(0, 0, stackSize, 0)
    if stack == 0 then return nil end
    if #host.threads == 0 then
        process.blockUntil = host.block
        process.threadLocal = host.threadLocal
        -- A guest thread's periodic yield returns its turn to the main thread, which yields to the host.
        host.hostYield = process.yield
        if process.yield then
            process.yield = function()
                if host.current.main then (host.hostYield :: any)() else coroutine.yield() end
            end
        end
    end
    host.nextThreadId = (host.nextThreadId or 0x1000) + 16
    local errno = resize(0, 0, 8, 0)
    write(8, errno, 0, 0)
    local thread = {id = host.nextThreadId, keys = {}, finished = false, stack = stack, errno = errno, locals = {}}
    local top = stack + stackSize - 16
    thread.co = coroutine.create(function() return body(top) end)
    table.insert(host.threads, thread)
    return thread
end

function host.findThread(id: number): any
    for _, thread in host.threads do
        if thread.id == id then return thread end
    end
    return nil
end

function libc.pthread_join(idLo, idHi, resultLo, resultHi)
    local thread = host.findThread(idLo)
    if not thread then return 3, 0 end
    if thread == host.current then return if libc.darwin then 11 else 35, 0 end
    host.block(function() return thread.finished end)
    if resultLo ~= 0 or resultHi ~= 0 then write(8, address(resultLo, resultHi), thread.resultLo or 0, thread.resultHi or 0) end
    return 0, 0
end
)luau", R"luau(
function libc.pthread_detach(idLo)
    return if host.findThread(idLo) then 0 else 3, 0
end

-- pthread_exit ends a guest thread with its result; the main thread's ends the process once the others have.
function libc.pthread_exit(lo, hi)
    if not host.current.main then error({luftThreadExit = true, lo = lo, hi = hi}, 0) end
    host.block(function()
        for _, thread in host.threads do
            if not thread.finished then return false end
        end
        return true
    end)
    exitProcess(0, true)
end
)luau", R"luau(
-- Condition variables keep their waiters; a signal wakes the first, a broadcast every one. A timed wait times
-- out when no other thread can run.
function host.waitCondition(condLo: number, condHi: number, mutexLo: number, mutexHi: number, timed: boolean): number
    local cond = address(condLo, condHi)
    host.conditions = host.conditions or {}
    local conditions = host.conditions :: any
    conditions[cond] = conditions[cond] or {}
    local waiter = {signaled = false}
    table.insert(conditions[cond], waiter)
    if pthreadMutex("pthread_mutex_unlock", mutexLo, mutexHi) ~= 0 then return 1 end
    local timedOut = false
    local me = host.current
    host.block(function()
        if waiter.signaled then return true end
        if timed and not host.othersRunnable(me) then
            timedOut = true
            return true
        end
        return false
    end)
    if not waiter.signaled then
        local list = conditions[cond]
        for index, entry in list do
            if entry == waiter then table.remove(list, index); break end
        end
    end
    pthreadMutex("pthread_mutex_lock", mutexLo, mutexHi)
    return if timedOut and not waiter.signaled then host.errno("ETIMEDOUT") else 0
end

function libc.pthread_cond_wait(condLo, condHi, mutexLo, mutexHi)
    if #host.threads == 0 then error("guest waits on a condition variable that no other thread can signal", 0) end
    return host.waitCondition(condLo, condHi, mutexLo, mutexHi, false), 0
end

function libc.pthread_cond_timedwait(condLo, condHi, mutexLo, mutexHi)
    if #host.threads == 0 then return host.errno("ETIMEDOUT"), 0 end
    return host.waitCondition(condLo, condHi, mutexLo, mutexHi, true), 0
end

function libc.pthread_cond_signal(condLo, condHi, all: boolean?)
    local list = ((host.conditions or {}) :: any)[address(condLo, condHi)]
    while list and #list > 0 do
        table.remove(list, 1).signaled = true
        if not all then break end
    end
    return 0, 0
end

function libc.pthread_cond_broadcast(condLo, condHi)
    return libc.pthread_cond_signal(condLo, condHi, true)
end

-- A Darwin thread-local variable's block for the current thread: the main thread uses the template itself, and
-- each other thread a copy made from the template's initial bytes.
function host.threadLocal(base: number): number
    local thread = host.current
    if thread.main then return base end
    local copy = thread.locals[base]
    if not copy then
        local initial = process.threadTemplates[base] or ""
        copy = resize(0, 0, math.max(#initial, 16), 0)
        fillMemory(copy, 0, 0, math.max(#initial, 16), 0)
        writeString(copy, initial)
        thread.locals[base] = copy
    end
    return copy
end

-- Darwin's pthread_get_stackaddr_np reports the top of the main thread's stack.
function libc.pthread_get_stackaddr_np()
    return stackTop, 0
end

-- The size of the program's stack (MappedStackSize).
function libc.pthread_get_stacksize_np()
    return 8388608, 0
end

-- Anonymous memory maps come from the heap, file maps are private copies; neither has page protection.
function libc.mmap(addrLo, addrHi, lengthLo, lengthHi, protLo, protHi, flagsLo, flagsHi, fdLo, fdHi, offsetLo, offsetHi)
    local length = address(lengthLo, lengthHi)
    local anonymous = bit32.btest(flagsLo, if libc.darwin then 0x1000 else 0x20)
    local fixed = bit32.btest(flagsLo, 0x10)
    if length == 0 or fixed then setErrno(22); return 4294967295, 4294967295 end
    local at = resize(0, 0, length, 0)
    if at == 0 then setErrno(12); return 4294967295, 4294967295 end
    fillMemory(at, 0, 0, length, 0)
    if not anonymous then
        local file = host.descriptors[signed32(fdLo)]
        if not file then resize(at, 0, 0, 0); setErrno(9); return 4294967295, 4294967295 end
        local offset = signed64(offsetLo, offsetHi)
        if file.directory or offset < 0 then resize(at, 0, 0, 0); setErrno(22); return 4294967295, 4294967295 end
        local available = math.max(0, math.min(length, file.contents.size - offset))
        if available > 0 then writeString(at, buffer.readstring(file.contents.data, offset, available)) end
    end
    host.maps = host.maps or {}
    ;(host.maps :: any)[at] = length
    return at, 0
end

function libc.munmap(addrLo, addrHi)
    local at = address(addrLo, addrHi)
    local maps = (host.maps or {}) :: any
    if maps[at] then
        maps[at] = nil
        resize(at, 0, 0, 0)
    end
    return 0, 0
end

function libc.one()
    return 1, 0
end

-- No thread but the main one exists to join or detach (ESRCH).
function libc.noThread()
    return 3, 0
end

function libc.notSupported()
    setErrno(host.errno("ENOSYS"))
    return result(-1)
end

function libc.notTerminal()
    setErrno(25)
    return result(-1)
end

function libc.notFound()
    setErrno(2)
    return result(-1)
end

-- assert(): Darwin's __assert_rtn(function, file, line, expression) and glibc's __assert_fail(expression, file,
-- line, function) print as their C libraries do, then abort.
function libc.assertDarwin(functionLo, functionHi, fileLo, fileHi, lineLo, lineHi, expressionLo, expressionHi)
    local name = if functionLo ~= 0 or functionHi ~= 0 then guestString(address(functionLo, functionHi)) else nil
    local file = guestString(address(fileLo, fileHi))
    local expression = guestString(address(expressionLo, expressionHi))
    if name then
        hostWrite(2, string.format("Assertion failed: (%s), function %s, file %s, line %d.\n", expression, name, file,
            signed32(lineLo)))
    else
        hostWrite(2, string.format("Assertion failed: (%s), file %s, line %d.\n", expression, file, signed32(lineLo)))
    end
    exitProcess(134, false)
end

function libc.assertGlibc(expressionLo, expressionHi, fileLo, fileHi, lineLo, lineHi, functionLo, functionHi)
    local program = host.args[1] or "program"
    hostWrite(2, string.format("%s: %s:%d: %s: Assertion `%s' failed.\n", program, guestString(address(fileLo, fileHi)),
        signed32(lineLo), guestString(address(functionLo, functionHi)), guestString(address(expressionLo, expressionHi))))
    exitProcess(134, false)
end

-- Message catalogs hold no messages, so catgets returns its default.
function libc.catgets(catLo, catHi, setLo, setHi, numberLo, numberHi, defaultLo, defaultHi)
    return defaultLo, defaultHi
end

-- In the C locale, collation compares bytes and transforms copy.
function libc.strxfrm(dstLo, dstHi, srcLo, srcHi, sizeLo, sizeHi)
    local text = guestString(address(srcLo, srcHi))
    local size = address(sizeLo, sizeHi)
    if #text < size then
        writeString(address(dstLo, dstHi), text)
        write(1, address(dstLo, dstHi) + #text, 0, 0)
    end
    return result(#text)
end

-- Darwin's copyfile_state_t is an opaque handle; fcopyfile copies a descriptor's contents into another.
function libc.copyfile_state_alloc()
    return resize(0, 0, 16, 0), 0
end

function libc.fcopyfile(fromLo, fromHi, toLo, toHi)
    local from, to = host.descriptors[signed32(fromLo)], host.descriptors[signed32(toLo)]
    if not from or not to or not to.writable then setErrno(9); return result(-1) end
    if from.directory or to.directory then setErrno(21); return result(-1) end
    local src, dst = from.contents, to.contents
    if src ~= dst then
        local data = buffer.create(src.size)
        buffer.copy(data, 0, src.data, 0, src.size)
        dst.data, dst.size = data, src.size
    end
    to.at = dst.size
    return result(0)
end
)luau", R"luau(
-- long double as stored by scanf's %Lf: a double on Darwin's ARM64 and Windows, IEEE quad precision on ARM64
-- Linux, and the x87 80-bit format on x86-64.
function host.writeLongDouble(at: number, value: number, platform: number)
    if platform ~= 0 then
        write(8, at, encodeFloat(8, value))
        return
    end
    local lo, hi = encodeFloat(8, value)
    local sign = if hi >= 2147483648 then 32768 else 0
    local exponent = bit32.extract(hi, 20, 11)
    -- The fraction without the implicit bit, and the unbiased exponent; subnormal doubles are normal in both
    -- wider formats.
    local fraction = bit32.band(hi, 0xfffff) * 4294967296 + lo
    fillMemory(at, 0, 0, 16, 0)
    if exponent == 0 and fraction == 0 then
        write(2, at + (if libc.arm then 14 else 8), sign, 0)
        return
    end
    local biased
    if exponent == 2047 then
        biased = 32767
    else
        local unbiased = exponent - 1023
        if exponent == 0 then
            unbiased = -1022
            while fraction < 2 ^ 52 do
                fraction *= 2
                unbiased -= 1
            end
            fraction -= 2 ^ 52
        end
        biased = unbiased + 16383
    end
    local fractionHi, fractionLo = fraction // 4294967296, fraction % 4294967296
    if libc.arm then
        -- IEEE quad precision: 112 fraction bits, the double's 52 at their top.
        write(4, at + 4, bit32.lshift(bit32.band(fractionLo, 15), 28), 0)
        write(4, at + 8, bit32.bor(bit32.rshift(fractionLo, 4), bit32.lshift(bit32.band(fractionHi, 15), 28)), 0)
        write(2, at + 12, bit32.rshift(fractionHi, 4), 0)
        write(2, at + 14, sign + biased, 0)
    else
        -- x87 extended precision: an explicit integer bit, then 63 fraction bits.
        write(4, at, bit32.lshift(fractionLo, 11), 0)
        write(4, at + 4, bit32.bor(2147483648, bit32.lshift(fractionHi, 11), bit32.rshift(fractionLo, 21)), 0)
        write(2, at + 8, sign + biased, 0)
    end
end

-- scanf's conversions over characters from `get` (nil at the end of the input), which `unget` puts back. The
-- result is the number of assignments, or -1 when the input ends before the first conversion.
function host.scanGuest(format: string, get: () -> number?, unget: (number) -> (), arguments: Arguments,
    platform: number): number
    local assigned, conversions, count = 0, 0, 0
    local function nextChar(): number?
        local c = get()
        if c then count += 1 end
        return c
    end
    local function back(c: number?)
        if c then
            unget(c)
            count -= 1
        end
    end
    local function isSpace(c: number?): boolean
        return c ~= nil and (c == 32 or (c >= 9 and c <= 13))
    end
    local function skipSpace(): boolean
        while true do
            local c = nextChar()
            if c == nil then return false end
            if not isSpace(c) then
                back(c)
                return true
            end
        end
    end
    local function failed(atEnd: boolean): number
        return if atEnd and conversions == 0 then -1 else assigned
    end
    local i, n = 1, #format
    while i <= n do
        local f = string.byte(format, i)
        if isSpace(f) then
            skipSpace()
            i += 1
        elseif f ~= 37 or string.sub(format, i + 1, i + 1) == "%" then
            if f == 37 then
                skipSpace()
                i += 1
            end
            local c = nextChar()
            if c ~= f then
                back(c)
                return failed(c == nil)
            end
            i += 1
        else
            i += 1
            local suppress = string.sub(format, i, i) == "*"
            if suppress then i += 1 end
            local digits = string.match(format, "^%d+", i)
            local width = if digits then tonumber(digits) :: number else nil
            if digits then i += #digits end
            local modifier = string.match(format, "^hh", i) or string.match(format, "^ll", i) or
                string.match(format, "^[hljztLq]", i) or ""
            i += #modifier
            local conversion = string.sub(format, i, i)
            i += 1
            local limit = width or math.huge
            if conversion == "n" then
                if not suppress then
                    local lo = arguments.nextInt()
                    local size = if modifier == "hh" then 1 elseif modifier == "h" then 2
                        elseif modifier == "" or (modifier == "l" and platform == 1) then 4 else 8
                    write(size, address(lo, 0), result(count))
                end
            elseif conversion == "c" or conversion == "s" or conversion == "[" then
                local accept: (number) -> boolean
                if conversion == "c" then
                    if not width then limit = 1 end
                    accept = function() return true end
                elseif conversion == "s" then
                    if not skipSpace() then return failed(true) end
                    accept = function(c) return not isSpace(c) end
                else
                    local negate = string.sub(format, i, i) == "^"
                    if negate then i += 1 end
                    local set: {[number]: boolean} = {}
                    local first = true
                    while i <= n and (first or string.sub(format, i, i) ~= "]") do
                        local c = string.byte(format, i)
                        if string.sub(format, i + 1, i + 1) == "-" and i + 2 <= n and string.sub(format, i + 2, i + 2) ~= "]" then
                            for code = c, string.byte(format, i + 2) do set[code] = true end
                            i += 3
                        else
                            set[c] = true
                            i += 1
                        end
                        first = false
                    end
                    i += 1
                    accept = function(c) return (set[c] == true) ~= negate end
                end
                local bytes = {}
                while #bytes < limit do
                    local c = nextChar()
                    if c == nil then break end
                    if not accept(c) then
                        back(c)
                        break
                    end
                    table.insert(bytes, c)
                end
                if #bytes == 0 or (conversion == "c" and #bytes < limit) then
                    return failed(#bytes == 0 and get() == nil)
                end
                conversions += 1
                if not suppress then
                    local lo, hi = arguments.nextInt()
                    local at = address(lo, hi)
                    for index, c in bytes do write(1, at + index - 1, c, 0) end
                    if conversion ~= "c" then write(1, at + #bytes, 0, 0) end
                    assigned += 1
                end
            elseif string.find("diouxXp", conversion, 1, true) then
                if not skipSpace() then return failed(true) end
                local base = if conversion == "o" then 8 elseif conversion == "x" or conversion == "X" or
                    conversion == "p" then 16 elseif conversion == "i" then 0 else 10
                local negative, used, lo, hi = false, 0, 0, 0
                local c = nextChar()
                if (c == 43 or c == 45) and used < limit then
                    negative = c == 45
                    used += 1
                    c = nextChar()
                end
                local digitsRead = 0
                if (base == 0 or base == 16) and c == 48 and used < limit then
                    used += 1
                    digitsRead = 1
                    local x = nextChar()
                    if (x == 120 or x == 88) and used < limit then
                        used += 1
                        base = 16
                        digitsRead = 0
                        c = nextChar()
                    else
                        if base == 0 then base = 8 end
                        c = x
                    end
                end
                if base == 0 then base = 10 end
                while c ~= nil and used < limit do
                    local value = if c >= 48 and c <= 57 then c - 48 elseif c >= 97 and c <= 122 then c - 87
                        elseif c >= 65 and c <= 90 then c - 55 else 99
                    if value >= base then break end
                    local low = lo * base + value
                    lo = low % 4294967296
                    hi = (hi * base + math.floor(low / 4294967296)) % 4294967296
                    digitsRead += 1
                    used += 1
                    c = nextChar()
                end
                back(c)
                if digitsRead == 0 then return failed(c == nil) end
                conversions += 1
                if negative then
                    lo, hi = (4294967296 - lo) % 4294967296, (4294967295 - hi + (if lo == 0 then 1 else 0)) % 4294967296
                end
                if not suppress then
                    local size = if conversion == "p" then 8 elseif modifier == "hh" then 1 elseif modifier == "h" then 2
                        elseif modifier == "" or (modifier == "l" and platform == 1) then 4 else 8
                    local pointerLo, pointerHi = arguments.nextInt()
                    write(size, address(pointerLo, pointerHi), lo, hi)
                    assigned += 1
                end
            elseif string.find("aAeEfFgG", conversion, 1, true) then
                if not skipSpace() then return failed(true) end
                -- The longest prefix that can begin a number; strtod's parser then decides how much is one.
                local token = {}
                local function take(c: number?): number?
                    table.insert(token, string.char(c :: number))
                    return nextChar()
                end
                local c = nextChar()
                if (c == 43 or c == 45) and #token < limit then c = take(c) end
                local lowered = function(code: number?): string
                    return if code then string.lower(string.char(code)) else ""
                end
                if lowered(c) == "i" or lowered(c) == "n" then
                    while c and #token < limit and string.find("infinityan()_0123456789", lowered(c), 1, true) do
                        c = take(c)
                    end
                else
                    local hex = false
                    if c == 48 and #token < limit then
                        c = take(c)
                        if lowered(c) == "x" and #token < limit then
                            hex = true
                            c = take(c)
                        end
                    end
                    local seenPoint, seenExponent = false, false
                    while c and #token < limit do
                        local l = lowered(c)
                        local digit = string.find(if hex then "0123456789abcdef" else "0123456789", l, 1, true)
                        if digit then
                            c = take(c)
                        elseif l == "." and not seenPoint and not seenExponent then
                            seenPoint = true
                            c = take(c)
                        elseif (l == (if hex then "p" else "e")) and not seenExponent then
                            seenExponent = true
                            c = take(c)
                            if (c == 43 or c == 45) and #token < limit then c = take(c) end
                        else
                            break
                        end
                    end
                end
                back(c)
                local text = table.concat(token)
                local value, used = parseDouble(text)
                if used == 0 then return failed(c == nil and #token == 0) end
                conversions += 1
                if not suppress then
                    local lo, hi = arguments.nextInt()
                    local at = address(lo, hi)
                    if modifier == "L" then
                        host.writeLongDouble(at, value, platform)
                    elseif modifier == "l" then
                        write(8, at, encodeFloat(8, value))
                    else
                        write(4, at, (encodeFloat(4, value)), 0)
                    end
                    assigned += 1
                end
            else
                return assigned
            end
        end
    end
    return assigned
end

function libc.scanString(textLo, textHi, formatLo, formatHi, arguments: Arguments, platform: number): number
    local text = guestString(address(textLo, textHi))
    local at = 1
    local function get(): number?
        local c = string.byte(text, at)
        if c then at += 1 end
        return c
    end
    local function unget() at -= 1 end
    return host.scanGuest(guestString(address(formatLo, formatHi)), get, unget, arguments, platform)
end

function libc.scanStream(fd: number, formatLo, formatHi, arguments: Arguments, platform: number): number
    local function get(): number?
        local c = getByte(fd)
        return if c >= 0 then c else nil
    end
    local function unget(c: number)
        host.pushback[fd] = c
        host.eof[fd] = nil
    end
    return host.scanGuest(guestString(address(formatLo, formatHi)), get, unget, arguments, platform)
end
)luau"};

constexpr std::string_view JumpOperators[] = {R"(
type JumpFrames = {[number]: {}}

local function protectJump(frames: JumpFrames, environment: number,
    resume: (number) -> (), restore: () -> ())
    local token = {}
    frames[environment] = token
    local value = 0
    while true do
        local ok, result = pcall(resume, value)
        local jump = if not ok and type(result) == "table" then result :: {[string]: unknown} else nil
        if jump and rawget(jump, "frame") == token then
            local resumedValue = rawget(jump, "value")
            assert(type(resumedValue) == "number")
            value = resumedValue
            restore()
        else
            if frames[environment] == token then
                frames[environment] = nil
            end
            if not ok then
                error(result, 0)
            end
            return
        end
    end
end

local function jumpToFrame(frames: JumpFrames, environment: number, value: number)
    local frame = frames[environment]
    if not frame then
        error("longjmp target is no longer active", 0)
    end
    error({frame = frame, value = if value == 0 then 1 else value}, 0)
end
)"};

// Clang and GCC accept longer literals, so check here what only an MSVC build would report.
consteval bool fitLiteralLimit(std::initializer_list<std::span<const std::string_view>> sources) {
    for (const auto chunks : sources)
        for (const auto chunk : chunks)
            if (chunk.size() > LiteralLimit)
                return false;
    return true;
}
static_assert(fitLiteralLimit({ArgumentReader, FlagOperators, RoutineOperators, ShiftOperators, FloatingOperators,
    VectorOperators, X87Operators, PrimeOperators, DivisionOperators, DecimalOperators, MultiplyOperators,
    MemoryOperators, SehOperators, UnwindLookups, ProcessOperators, JumpOperators}),
    "a runtime chunk exceeds MSVC's string literal limit; split it at a line break");
}

std::string quoted(std::string_view value) {
    std::string result;
    appendQuoted(result, {reinterpret_cast<const std::uint8_t*>(value.data()), value.size()});
    return result;
}

const GuestImport* Data::unresolved(std::uint64_t at, unsigned size) const {
    if (at >= image.size())
        return nullptr;
    for (const auto& import : imports)
        if (at < import.start + import.size && at + size > import.start)
            return &import;
    return nullptr;
}

bool Data::writable(std::uint64_t at, unsigned size) const {
    return std::ranges::any_of(regions, [&](const GuestRegion& region) {
        return !region.executable && region.readable && (region.writable || region.protectable) &&
            at >= region.start && at + size <= region.end;
    });
}

bool Data::readable(std::uint64_t at, unsigned size) const {
    if (at > image.size() || size > image.size() - at)
        return false;
    if (!regions.empty()) {
        return std::ranges::any_of(regions, [&](const GuestRegion& region) {
            return !region.executable && region.readable && at >= region.start && at + size <= region.end;
        });
    }
    return std::ranges::none_of(code, [&](const ir::CodeRange& range) {
        return at < range.last && at + size > range.first;
    });
}

std::optional<std::uint64_t> Data::immutableWord(std::uint64_t at, unsigned size) const {
    if (size > 8 || !readable(at, size) || writable(at, size) || unresolved(at, size))
        return {};
    std::uint64_t word = 0;
    for (unsigned i = 0; i < size; ++i)
        word |= std::uint64_t(image[at + i]) << (8 * i);
    return word;
}

void Data::materialize(std::size_t at, unsigned size) {
    if (!size)
        return;
    auto first = at, last = at + size;
    auto next = emitted.upper_bound(first);
    if (next != emitted.begin()) {
        const auto previous = std::prev(next);
        if (previous->second >= first) {
            first = previous->first;
            last = std::max(last, previous->second);
            next = emitted.erase(previous);
        }
    }
    while (next != emitted.end() && next->first <= last) {
        last = std::max(last, next->second);
        next = emitted.erase(next);
    }
    emitted.emplace(first, last);
}

bool Data::materialized(std::uint64_t at) const {
    const auto next = emitted.upper_bound(at);
    return next != emitted.begin() && std::prev(next)->second > at;
}

void Data::materializeAll() {
    // Code sections are included too: compilers place jump tables and constructor lists among the code.
    for (const auto& region : regions) {
        if (!region.readable && !region.executable)
            continue;
        auto start = region.start;
        std::vector<const GuestImport*> gaps;
        for (const auto& import : imports)
            if (import.start < region.end && import.start + import.size > region.start)
                gaps.push_back(&import);
        std::ranges::sort(gaps, {}, [](const GuestImport* import) { return import->start; });
        for (const auto* gap : gaps) {
            if (gap->start > start)
                materialize(start, unsigned(gap->start - start));
            start = std::max(start, gap->start + gap->size);
        }
        if (start < region.end)
            materialize(start, unsigned(region.end - start));
    }
}

bool Data::materializeObject(std::uint64_t at) {
    if (unresolved(at, 1))
        return false;
    for (const auto& object : objects) {
        if (at >= object.start && at < object.start + object.size &&
            readable(object.start, unsigned(object.size))) {
            auto start = object.start;
            const auto end = start + object.size;
            std::vector<const GuestImport*> gaps;
            for (const auto& import : imports)
                if (import.start < end && import.start + import.size > start)
                    gaps.push_back(&import);
            std::ranges::sort(gaps, {}, [](const GuestImport* import) { return import->start; });
            for (const auto* gap : gaps) {
                if (gap->start > start)
                    materialize(start, unsigned(gap->start - start));
                start = std::max(start, gap->start + gap->size);
            }
            if (start < end)
                materialize(start, unsigned(end - start));
            return true;
        }
    }
    return false;
}

void Data::materializeIndexed(std::uint64_t at) {
    if (materializeObject(at) || !readable(at, 1) || unresolved(at, 1))
        return;

    if (regions.empty()) {
        // Raw images have no sections, so use the gap between decoded instructions.
        std::size_t first = 0;
        auto last = image.size();
        for (const auto& range : code) {
            if (range.last <= at)
                first = std::max(first, range.last);
            else if (range.first > at)
                last = std::min(last, range.first);
        }
        materialize(first, unsigned(last - first));
        return;
    }

    const auto region = std::ranges::find_if(regions, [&](const GuestRegion& value) {
        return value.readable && !value.writable && !value.executable && at >= value.start && at < value.end;
    });
    if (region == regions.end())
        return;
    auto first = region->start;
    auto last = region->end;
    const auto clip = [&](std::size_t start, std::size_t size) {
        if (start > at)
            last = std::min(last, start);
        else if (start + size <= at)
            first = std::max(first, start + size);
    };
    for (const auto& object : objects)
        clip(object.start, object.size);
    for (const auto& import : imports)
        clip(import.start, import.size);
    materialize(first, unsigned(last - first));
}

void Data::materializeAddress(std::uint64_t at) {
    materializeObject(at);
    if (!readable(at, 1) || writable(at, 1) || materialized(at))
        return;
    // Address-taken printable literals may lack an ELF symbol.
    for (unsigned size = 1; size <= 4096 && readable(at, size); ++size) {
        const auto byte = image[at + size - 1];
        if (byte == 0) {
            if (!unresolved(at, size))
                materialize(at, size);
            return;
        }
        if (byte < 32 || byte > 126)
            return;
    }
}

std::string Data::source() const {
    const auto modeAt = [&](std::size_t at) {
        const auto region = std::ranges::find_if(regions, [&](const GuestRegion& value) {
            return value.readable && !value.executable && at >= value.start && at < value.end;
        });
        return region == regions.end() ? 0u : unsigned(region->writable) + (region->protectable ? 2 : 0);
    };
    // Split ranges where the write mode changes, and trim trailing zeros: the runtime zero-fills each range.
    std::vector<std::size_t> cuts;
    for (const auto& region : regions)
        cuts.insert(cuts.end(), {region.start, region.end});
    std::ranges::sort(cuts);
    // Ranges in address order: the runtime takes the first as the lowest guest data.
    std::map<std::size_t, std::string> ranges;
    for (const auto& [start, end] : emitted) {
        for (auto first = start; first < end;) {
            auto last = end;
            if (const auto cut = std::ranges::upper_bound(cuts, first); cut != cuts.end() && *cut < last)
                last = *cut;
            auto used = last;
            while (used > first && image[used - 1] == 0)
                --used;
            auto& range = ranges[first];
            range = std::format("    {{first = {}, last = {}, mode = {}, bytes = ", first, last, modeAt(first));
            appendQuoted(range, image.subspan(first, used - first));
            range += "},\n";
            first = last;
        }
    }
    for (const auto& [slot, import] : tokenSlots) {
        const auto token = ImportTokenBase + slot;
        std::array<std::uint8_t, 8> bytes{};
        for (unsigned i = 0; i < 8; ++i)
            bytes[i] = std::uint8_t(token >> (8 * i));
        auto& range = ranges[slot];
        range = std::format("    {{first = {}, last = {}, mode = {}, bytes = ", slot, slot + 8, modeAt(slot));
        appendQuoted(range, bytes);
        range += "},\n";
    }
    std::string result = "local data: {DataRange} = {\n";
    for (const auto& [first, range] : ranges)
        result += range;
    return result + "}\n";
}

void appendRuntime(std::string& source, const RuntimeFeatures& features, const Data& data) {
    appendChunks(source, ArgumentReader);
    if (features.landingPads && !data.landingPads.empty()) {
        // Unwinders jump to these with the stack pointer of the frame that resumes.
        source += "local landingPads: {[number]: boolean} = {";
        for (const auto pad : data.landingPads)
            source += std::format("[{}] = true, ", pad);
        source += "}\n";
    }
    // Guest process state that outlives a single export call.
    source += "\nlocal guestTrace: {number} = table.create(32, -1)\nlocal guestTraceAt = 1\n";
    source += "local function describeTrace(): string\n"
        "    local parts = {}\n"
        "    for i = 0, 31 do\n"
        "        local pc = guestTrace[(guestTraceAt + i - 1) % 32 + 1]\n"
        "        if pc >= 0 then table.insert(parts, string.format(\"%x\", pc)) end\n"
        "    end\n"
        "    return \"recent guest blocks: \" .. table.concat(parts, \" \")\n"
        "end\n";
    // A program's `yield` option runs about every `yieldInterval` seconds of guest execution, between routines;
    // it may yield the calling coroutine so that a host such as a game keeps running meanwhile. The state lives in
    // `process`: modules with many exports are close to Luau's limit of 200 locals per function.
    source += "\nlocal process = {initialized = false, exitCallbacks = {} :: {() -> ()}, "
        "fiberSlots = {} :: {[number]: {lo: number, hi: number, callbackLo: number, callbackHi: number}?}, "
        "fiberNext = 0, lastError = 0, exceptionFilterLo = 0, exceptionFilterHi = 0, "
        "yield = nil :: (() -> ())?, yieldInterval = 0.05, yieldAt = 0, yieldSteps = 0, "
        "watchMemory = nil :: (((buffer) -> ()) -> (number, number))?, "
        "wrappedAddress = nil :: ((number, number, number) -> number)?, "
        "heapLength = nil :: ((number) -> number?)?, "
        "threadId = nil :: (() -> number)?, blockUntil = nil :: (((() -> boolean)) -> ())?, threadErrno = nil :: number?, "
        "threadLocal = nil :: ((number) -> number)?, saveRegisters = nil :: (() -> {any})?, "
        "restoreRegisters = nil :: (({any}) -> ())?, threadTemplates = {} :: {[number]: string}, "
        "threadBlocks = {} :: {[number]: string}}\n";
    if (features.structured)
        appendChunks(source, RoutineOperators);
    if (features.stackGuard)
        source += "\n-- Synthetic guard for translated Linux x86-64 functions.\n"
            "local stackGuardLo, stackGuardHi = 0xa5a5a500, 0x5a5a5a5a\n";
    if (features.flags)
        appendChunks(source, FlagOperators);
    if (features.shifts)
        appendChunks(source, ShiftOperators);
    if (features.division)
        appendChunks(source, DivisionOperators);
    if (features.multiply)
        appendChunks(source, MultiplyOperators);
    if (features.floating)
        appendChunks(source, FloatingOperators);
    if (features.vector)
        appendChunks(source, VectorOperators);
    if (features.prime)
        appendChunks(source, PrimeOperators);
    if (features.decimal)
        appendChunks(source, DecimalOperators);
    if (features.jumpFrames)
        appendChunks(source, JumpOperators);
    if (features.memory) {
        appendChunks(source, MemoryOperators);
        source += data.source();
        source += std::format("local read, write, stackTop, resetMemory, resize, readXmm, writeXmm, "
            "compareStrings, stringLength, copyMemory, fillMemory, processHeap, allocateCpp, compareMemory, "
            "criticalSection, protectMemory, cLocale, useCLocale, wideClass, testWideClass, pthreadMutex, srwLock, errnoAddress, "
            "readString, writeString = makeMemory({}, data, {}, {}, {})\n",
            data.image.size(), features.heap, !data.regions.empty(), data.regions.empty() ? RawStackSize : MappedStackSize);
        if (features.process) {
            source += "\n-- Each mapped object's exception metadata, for unwinders that look it up.\n"
                "local unwindObjects = {\n";
            for (const auto& object : data.unwindObjects)
                source += std::format("    {{start = {}, stop = {}, header = {}, frameHeader = {}, frames = {}, "
                    "framesSize = {}, compact = {}, compactSize = {}}},\n", object.start, object.end, object.header,
                    object.frameHeader, object.frames, object.framesSize, object.compact, object.compactSize);
            source += "}\n";
            appendChunks(source, ProcessOperators);
            appendChunks(source, UnwindLookups);
        }
        if (features.seh) {
            appendChunks(source, SehOperators);
            if (!data.unwindObjects.empty())
                source += std::format("seh.base, seh.stop, seh.table, seh.count = {}, {}, {}, {}\n",
                    data.unwindObjects.front().header, data.unwindObjects.front().end,
                    data.unwindObjects.front().frames, data.unwindObjects.front().framesSize / 12);
        }
        if (features.x87)
            appendChunks(source, X87Operators);
    }
}
}
