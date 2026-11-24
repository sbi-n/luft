#include "runtime.h"

#include <algorithm>
#include <format>

namespace luau {
namespace {
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

constexpr std::string_view ArgumentReader = R"(
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
)";

constexpr std::string_view FlagOperators = R"(
local function evenParity(value: number): boolean
    return bit32.extract(0x9669, bit32.band(bit32.bxor(value, bit32.rshift(value, 4)), 15)) == 1
end

local function addFlags(subtract: boolean, arm: boolean, size: number,
    alo: number, ahi: number, blo: number, bhi: number, carryIn: boolean?): (number, number, boolean, boolean, boolean, boolean)
    local sign = if subtract then -1 else 1
    local sum = alo + sign * (blo + (if carryIn then 1 else 0))
    if size == 2 then
        local lo = sum % 65536
        local negative = lo >= 32768
        local carry = if subtract then sum < 0 else sum >= 65536
        return lo, 0, carry, ((alo >= 32768) ~= (blo >= 32768)) == subtract and negative ~= (alo >= 32768), negative, lo == 0
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
)";

constexpr std::string_view RoutineOperators = R"(
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
    while true do
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
)";

constexpr std::string_view ShiftOperators = R"(
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
    local right: (number, number) -> number = if op == 2 then bit32.arshift else bit32.rshift
    if size == 4 then
        return right(lo, count), 0, bit32.extract(lo, count - 1)
    elseif count < 32 then
        return bit32.bor(bit32.rshift(lo, count), bit32.lshift(hi, 32 - count)),
            right(hi, count), bit32.extract(lo, count - 1)
    end
    return right(hi, count - 32), if op == 2 and hi >= 2147483648 then 4294967295 else 0,
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
)";

constexpr std::string_view FloatingOperators = R"(
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
)";

// Vector lanes are four little-endian 32-bit words. Element access goes through scratch buffers.
constexpr std::string_view VectorOperators = R"(
local laneA, laneB, laneR = buffer.create(16), buffer.create(16), buffer.create(16)

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
        local right = if op == 26 then bit32.arshift else bit32.rshift
        if count >= 32 then return right(ahi, count - 32), fill end
        return bit32.bor(bit32.rshift(alo, count), bit32.lshift(ahi, 32 - count)), right(ahi, count)
    elseif op == 0 or op == 1 then
        local sum = if op == 0 then alo + blo else alo - blo
        local high = if op == 0 then ahi + bhi else ahi - bhi
        return sum % 4294967296, (high + math.floor(sum / 4294967296)) % 4294967296
    elseif op == 20 then
        local al, ah = alo % 65536, math.floor(alo / 65536)
        local bl, bh = blo % 65536, math.floor(blo / 65536)
        local cross = al * bh + ah * bl
        local lower = al * bl + cross % 65536 * 65536
        local upper = ah * bh + math.floor(cross / 65536) + math.floor(lower / 4294967296)
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
)";

// The x87 FPU: an eight-register stack of doubles (extended precision is not modeled), a status word for
// the condition codes, and the control word's rounding mode.
constexpr std::string_view X87Operators = R"luau(
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
)luau";

constexpr std::string_view PrimeOperators = R"(
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
)";

constexpr std::string_view DivisionOperators = R"(
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
)";

constexpr std::string_view DecimalOperators = R"luau(
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
)luau";

constexpr std::string_view MultiplyOperators = R"(
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
)";

constexpr std::string_view MemoryOperators = R"(
local function address(lo: number, hi: number): number
    if hi ~= 0 then
        error("guest address is out of range", 0)
    end
    return lo
end

local function offset(lo: number, hi: number, displacement: number): (number, number)
    local sum = lo + displacement
    return sum % 4294967296, (hi + math.floor(sum / 4294967296)) % 4294967296
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
    local stackData: buffer? = nil
    local stackInUse = false
    local contents: {buffer?} = {}
    -- Heap blocks get 16-byte-rounded storage: word-at-a-time string routines read past the requested size.
    local heap: {[number]: buffer} = {}
    local heapSizes: {[number]: number} = {}
    local heapStarts: {number} = {}
    local heapPages: {number} = {}
    local criticalSections: {[number]: number} = {}
    local pthreadLocks: {[number]: boolean} = {}
    local srwLocks: {[number]: number} = {}
    local pageProtection: {[number]: number} = {}
    local heapStart = stackTop + 16
    local nextAllocation = heapStart
    local lastHeapStart = 0
    local classicLocale = 0
    local useGlobalLocale = true
    -- Guest memory belongs to the module: data, heap, and locks persist across export calls.
    local function reset(stack: boolean)
        if stack and not stackData then
            stackData = buffer.create(stackSize)
        end
        stackInUse = stackInUse or stack
    end
    local function locate(at: number, size: number, write: boolean): (buffer, number)
        local limit = at + size
        local stack = stackData
        if stackInUse and stack and at >= stackBottom and limit <= stackTop then
            return stack, at - stackBottom
        end
        if heapEnabled and at >= heapStart then
            -- Look up the live buffer so freeing or resizing also affects cached addresses.
            local bytes = heap[lastHeapStart]
            if bytes and at >= lastHeapStart and limit <= lastHeapStart + buffer.len(bytes) then
                return bytes, at - lastHeapStart
            end
            local page = math.floor((at - heapStart) / 256) + 1
            local first = heapPages[page]
            if first and at < nextAllocation then
                local last = heapPages[page + 1] or #heapStarts
                while first < last do
                    local index = math.floor((first + last + 1) / 2)
                    if heapStarts[index] <= at then first = index else last = index - 1 end
                end
                local start = heapStarts[last]
                local bytes = heap[start]
                if bytes and limit <= start + buffer.len(bytes) then
                    lastHeapStart = start
                    return bytes, at - start
                end
            end
        else
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
                    local bytes = contents[index]
                    if bytes then
                        return bytes, at - range.first
                    end
                    local initialized = buffer.create(range.last - range.first)
                    buffer.writestring(initialized, 0, range.bytes)
                    contents[index] = initialized
                    return initialized, at - range.first
                else
                    break
                end
            end
        end
        error("guest memory range was not resolved during translation: " .. at, 0)
    end
    local function read(size: number, at: number): (number, number)
        local bytes, index = locate(at, size, false)
        if size == 1 then
            return buffer.readu8(bytes, index), 0
        end
        if size == 2 then
            return buffer.readu16(bytes, index), 0
        end
        return buffer.readu32(bytes, index), if size == 8 then buffer.readu32(bytes, index + 4) else 0
    end
    local function write(size: number, at: number, lo: number, hi: number)
        local bytes, index = locate(at, size, true)
        if size == 1 then
            buffer.writeu8(bytes, index, bit32.band(lo, 255))
        elseif size == 2 then
            buffer.writeu16(bytes, index, bit32.band(lo, 65535))
        else
            buffer.writeu32(bytes, index, lo)
            if size == 8 then
                buffer.writeu32(bytes, index + 4, hi)
            end
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
    local function resize(lo: number, hi: number, size: number, sizeHi: number): (number, number)
        local at = address(lo, hi)
        local previous = heap[at]
        if at ~= 0 and previous == nil then
            error("invalid guest allocation pointer", 0)
        end
        if sizeHi ~= 0 then
            return 0, 0
        end
        if size == 0 then
            heap[at] = nil
            heapSizes[at] = nil
            return 0, 0
        end
        if previous and size <= buffer.len(previous) and size * 2 > buffer.len(previous) then
            -- Shrinking or growing within the rounded block keeps the allocation.
            if size > heapSizes[at] then buffer.fill(previous, heapSizes[at], 0, size - heapSizes[at]) end
            heapSizes[at] = size
            return at, 0
        end
        local length = math.ceil(size / 16) * 16
        if nextAllocation + length - heapStart > heapLimit then
            return 0, 0
        end
        local bytes = buffer.create(length)
        if previous then
            buffer.copy(bytes, 0, previous, 0, math.min(size, heapSizes[at]))
            heap[at] = nil
            heapSizes[at] = nil
        end
        local start = nextAllocation
        heap[start] = bytes
        heapSizes[start] = size
        local index = #heapStarts + 1
        heapStarts[index] = start
        nextAllocation += length
        -- Record the first allocation covering each page, including its alignment padding.
        for page = math.floor((start - heapStart) / 256) + 1, math.ceil((nextAllocation - heapStart) / 256) do
            heapPages[page] = heapPages[page] or index
        end
        return start, 0
    end
    local function allocateCpp(size: number, sizeHi: number, throwing: boolean): (number, number)
        local pointer = resize(0, 0, math.max(size, 1), sizeHi)
        if pointer == 0 and throwing then
            error("guest C++ allocation failed", 0)
        end
        return pointer, 0
    end
    local errnoCell = 0
    local function errnoAddress(): number
        if errnoCell == 0 then
            errnoCell = resize(0, 0, 8, 0)
            write(8, errnoCell, 0, 0)
        end
        return errnoCell
    end
    local function cLocale(): (number, number)
        if classicLocale ~= 0 then return classicLocale, 0 end
        local base = allocateCpp(4074, 0, true)
        local bytes = heap[base]
        local classes, lower, upper = 232, 1000, 2536
        buffer.writeu32(bytes, 104, base + classes + 128 * 2)
        buffer.writeu32(bytes, 112, base + lower + 128 * 4)
        buffer.writeu32(bytes, 120, base + upper + 128 * 4)
        buffer.writeu8(bytes, 4072, 67)
        for category = 0, 12 do
            buffer.writeu32(bytes, 128 + category * 8, base + 4072)
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
        local previous = if pointerHi == 0 then heap[pointer] else nil
        if op == "HeapFree" then
            if not previous then return 0, 0 end
            heap[pointer] = nil
            heapSizes[pointer] = nil
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
            elseif size <= buffer.len(previous) then
                if size > heapSizes[pointer] then buffer.fill(previous, heapSizes[pointer], 0, size - heapSizes[pointer]) end
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
    local function pthreadMutex(op: string, lo: number, hi: number): number
        local at = address(lo, hi)
        if at == 0 then return 22 end
        locate(at, 1, false)
        if op == "pthread_mutex_unlock" then
            if not pthreadLocks[at] then return 1 end
            pthreadLocks[at] = nil
        else
            if pthreadLocks[at] then
                if op == "pthread_mutex_trylock" then return 16 end
                error("recursive guest pthread mutex lock", 0)
            end
            pthreadLocks[at] = true
        end
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
)";

constexpr std::string_view SehOperators = R"luau(
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
    if read(4, record) == 0x80000029 then
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
)luau";

// How unwinders find frame data: glibc's _dl_find_object and dyld's _dyld_find_unwind_sections.
constexpr std::string_view UnwindLookups = R"luau(
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
)luau";

// Host services for translated programs: arguments, standard streams, a file system, and C library I/O.
// Each libc entry takes and returns guest words as (lo, hi) pairs.
constexpr std::string_view ProcessOperators = R"luau(
type HostFile = {path: string, data: buffer, size: number, at: number, writable: boolean, readable: boolean}

local host = {
    args = {"program"} :: {string},
    env = {} :: {string},
    stdin = "",
    stdinAt = 1,
    output = {{}, {}} :: {{string}},
    writers = {} :: {[number]: ((string) -> ())?},
    files = {} :: {[string]: string},
    descriptors = {} :: {[number]: HostFile?},
    nextDescriptor = 3,
    streams = {} :: {[number]: number},
    eof = {} :: {[number]: boolean},
    pushback = {} :: {[number]: number},
    environment = 0,
    strings = {} :: {[string]: number},
}

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
    local finish = file.at + #text
    if finish > buffer.len(file.data) then
        local grown = buffer.create(math.max(finish, buffer.len(file.data) * 2, 64))
        buffer.copy(grown, 0, file.data, 0, file.size)
        file.data = grown
    end
    buffer.writestring(file.data, file.at, text)
    file.at = finish
    file.size = math.max(file.size, finish)
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
    local available = math.max(0, math.min(count, file.size - file.at))
    local text = buffer.readstring(file.data, file.at, available)
    file.at += available
    return text
end

local function hostOpen(path: string, readable: boolean, writable: boolean, create: boolean, truncate: boolean,
    append: boolean): number?
    local existing = host.files[path]
    if not existing and not create then return nil end
    local text = if truncate or not existing then "" else existing
    local data = buffer.create(math.max(#text, 64))
    buffer.writestring(data, 0, text)
    local fd = host.nextDescriptor
    host.nextDescriptor += 1
    host.descriptors[fd] = {path = path, data = data, size = #text, at = if append then #text else 0,
        writable = writable, readable = readable}
    if writable then host.files[path] = text end
    return fd
end

local function hostClose(fd: number): boolean
    local file = host.descriptors[fd]
    if not file then return fd >= 0 and fd <= 2 end
    if file.writable then host.files[file.path] = buffer.readstring(file.data, 0, file.size) end
    host.descriptors[fd] = nil
    return true
end

local function hostSeek(fd: number, offset: number, whence: number): number?
    local file = host.descriptors[fd]
    if not file then return nil end
    local base = if whence == 0 then 0 elseif whence == 1 then file.at else file.size
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

local function guestString(at: number, limit: number?): string
    local length = stringLength(at, 0)
    if limit then length = math.min(length, limit) end
    return readString(at, length)
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

type Arguments = {nextInt: () -> (number, number), nextFloat: () -> number}

-- Formats a C format string. `long` is 32 bits wide on Windows.
local function formatGuest(format: string, arguments: Arguments, windows: boolean): string
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
                (length == "l" and not windows) or length == "I"
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
            local lo, hi = arguments.nextInt()
            text = padded(digitsOf(lo, hi, 16, false), width, left, false, "0x")
        elseif conversion == "n" then
            local lo, hi = arguments.nextInt()
            write(4, address(lo, hi), written % 4294967296, 0)
        elseif string.find("fFeEgGaA", conversion, 1, true) then
            local value = arguments.nextFloat()
            if value ~= value or value == math.huge or value == -math.huge then
                local word = if value ~= value then "nan" else "inf"
                if string.find("FEGA", conversion, 1, true) then word = string.upper(word) end
                local sign = if value == -math.huge or (value ~= value and 1 / value < 0) then "-"
                    elseif string.find(flags, "+", 1, true) then "+" elseif string.find(flags, " ", 1, true) then " " else ""
                text = padded(word, width, left, false, sign)
            elseif conversion == "a" or conversion == "A" then
                local mantissa, exponent = math.frexp(math.abs(value))
                local digits = string.format("%x", math.floor(mantissa * 2 ^ 53))
                text = padded(string.format("0x%s.%sp%+d", string.sub(digits, 1, 1), string.sub(digits, 2), exponent - 1),
                    width, left, zero, if value < 0 then "-" else "")
            else
                local spec = "%" .. string.gsub(flags, "'", "") .. (if width then tostring(width) else "") ..
                    (if precision then "." .. precision else "") .. (if conversion == "F" then "f" else conversion)
                text = string.format(spec, value)
            end
        else
            text = string.sub(format, percent, j - 1)
        end
        table.insert(out, text)
        written += #text
        i = j
    end
    return table.concat(out)
end

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
            return decodeFloat(8, floats[index * 2 + 1], floats[index * 2 + 2])
        end
        return decodeFloat(8, fromStack())
    end
    return {nextInt = nextInt, nextFloat = nextFloat}
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
        return {nextInt = nextInt, nextFloat = nextFloat}
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
        return {nextInt = nextInt, nextFloat = nextFloat}
    end
    local cursor = at
    local function nextInt(): (number, number)
        local a, b = read(8, cursor)
        cursor += 8
        return a, b
    end
    return {nextInt = nextInt, nextFloat = function(): number return decodeFloat(8, nextInt()) end}
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
    if not text then setErrno(9); return result(-1) end
    writeString(address(bufLo, bufHi), text)
    return result(#text)
end

local function openFlags(flags: number): (boolean, boolean, boolean, boolean, boolean)
    local access = flags % 4
    local create = bit32.btest(flags, if libc.darwin then 0x200 else 0x40)
    local truncate = bit32.btest(flags, if libc.darwin then 0x400 else 0x200)
    local append = bit32.btest(flags, if libc.darwin then 0x8 else 0x400)
    return access ~= 1, access ~= 0, create, truncate, append
end

function libc.open(pathLo, pathHi, flagsLo, flagsHi)
    local fd = hostOpen(guestString(address(pathLo, pathHi)), openFlags(flagsLo))
    if not fd then setErrno(2); return result(-1) end
    return result(fd)
end

function libc.openat(dirLo, dirHi, pathLo, pathHi, flagsLo, flagsHi)
    return libc.open(pathLo, pathHi, flagsLo, flagsHi)
end

function libc.close(fdLo, fdHi)
    return result(if hostClose(signed32(fdLo)) then 0 else -1)
end

function libc.lseek(fdLo, fdHi, offsetLo, offsetHi, whenceLo, whenceHi)
    local position = hostSeek(signed32(fdLo), signed64(offsetLo, offsetHi), whenceLo)
    if not position then setErrno(29); return result(-1) end
    return result(position)
end

local function writeStat(at: number, fd: number?)
    local file = if fd then host.descriptors[fd] else nil
    local size = if file then file.size else 0
    local mode = if file then 0x81a4 else 0x2190
    fillMemory(at, 0, 0, 144, 0)
    if libc.darwin then
        write(2, at + 4, mode, 0)
        write(8, at + 96, result(size))
        write(4, at + 112, 4096, 0)
    else
        write(4, at + (if libc.arm then 16 else 24), mode, 0)
        write(8, at + 48, result(size))
        write(4, at + 56, 4096, 0)
    end
end

function libc.fstat(fdLo, fdHi, statLo, statHi)
    local fd = signed32(fdLo)
    if fd > 2 and not host.descriptors[fd] then setErrno(9); return result(-1) end
    writeStat(address(statLo, statHi), if fd > 2 then fd else nil)
    return result(0)
end

function libc.stat(pathLo, pathHi, statLo, statHi)
    local path = guestString(address(pathLo, pathHi))
    if not host.files[path] then setErrno(2); return result(-1) end
    local fd = hostOpen(path, true, false, false, false, false)
    writeStat(address(statLo, statHi), fd)
    if fd then hostClose(fd) end
    return result(0)
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
    local fd = hostOpen(guestString(address(pathLo, pathHi)), streamMode(guestString(address(modeLo, modeHi))))
    if not fd then setErrno(2); return 0, 0 end
    return newStream(fd), 0
end

function libc.fdopen(fdLo, fdHi)
    return newStream(signed32(fdLo)), 0
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
    local text = hostRead(fd, size * count) or ""
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

function libc.ferror()
    return 0, 0
end

function libc.clearerr(lo, hi)
    host.eof[streamDescriptor(lo, hi)] = nil
    return 0, 0
end

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

local function parseInteger(textLo: number, textHi: number, endLo: number, endHi: number, base: number,
    unsigned: boolean): (number, number)
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
    if string.sub(lowered, 1, 3) == "nan" then return 0 / 0, leading + signLength + 3 end
    local hex = string.match(lowered, "^0x[%x]*%.?[%x]*p?[+-]?%d*")
    if hex and #hex > 2 then
        local mantissa, exponent = string.match(hex, "^0x([%x]*%.?[%x]*)p?([+-]?%d*)$")
        local whole, fraction = string.match(mantissa :: string, "^(%x*)%.?(%x*)$")
        local value = tonumber((whole :: string) .. (fraction :: string), 16) or 0
        value = value * 2 ^ ((tonumber(exponent) or 0) - 4 * #(fraction :: string))
        return sign * value, leading + signLength + #hex
    end
    local number = string.match(lowered, "^%d*%.?%d*")
    if not number or number == "" or number == "." then return 0, 0 end
    local exponent = string.match(lowered, "^e[+-]?%d+", #number + 1)
    local literal = number .. (exponent or "")
    return sign * (tonumber(literal) or 0), leading + signLength + #literal
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

-- The guest runs on a single thread.
function libc.pthread_self()
    return 0x1000, 0
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

function libc.pthread_getspecific(key)
    local slot = threadKeys[key]
    if not slot then return 0, 0 end
    return slot.lo, slot.hi
end

function libc.pthread_setspecific(key, keyHi, lo, hi)
    threadKeys[key] = {lo = lo, hi = hi}
    return 0, 0
end

function libc.pthread_cond_wait()
    error("guest waits on a condition variable that no other thread can signal", 0)
end

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

function libc.strerror(code)
    return cachedString("guest error " .. signed32(code)), 0
end

function libc.strerror_r(code, codeHi, bufLo, bufHi, sizeLo, sizeHi)
    local text = string.sub("guest error " .. signed32(code), 1, math.max(address(sizeLo, sizeHi) - 1, 0))
    writeString(address(bufLo, bufHi), text)
    write(1, address(bufLo, bufHi) + #text, 0, 0)
    return 0, 0
end

function libc.aligned_alloc(alignLo, alignHi, sizeLo, sizeHi)
    -- Heap allocations are 16-byte aligned; larger alignments are not available.
    if address(alignLo, alignHi) > 16 then return 0, 0 end
    return resize(0, 0, math.max(address(sizeLo, sizeHi), 1), 0), 0
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

function win32.CreateFileW(nameLo, nameHi, accessLo, accessHi, shareLo, shareHi, securityLo, securityHi, sp)
    local path = string.gsub(readWide(address(nameLo, nameHi)), "\\", "/")
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
    write(8, address(sizeLo, sizeHi), result(file.size))
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
    if file then file.size = file.at end
    return 1, 0
end

function win32.GetCommandLineW()
    if host.strings["\0commandW"] == nil then host.strings["\0commandW"] = newGuestWide(commandLine()) end
    return host.strings["\0commandW"], 0
end

function win32.GetCommandLineA()
    return cachedString(commandLine()), 0
end

function win32.GetModuleFileNameW(moduleLo, moduleHi, bufLo, bufHi, sizeLo)
    local name = host.args[1] or "program.exe"
    name = string.sub(name, 1, math.max(sizeLo - 1, 0))
    writeWide(address(bufLo, bufHi), name, true)
    return #name, 0
end

function win32.GetModuleFileNameA(moduleLo, moduleHi, bufLo, bufHi, sizeLo)
    local name = string.sub(host.args[1] or "program.exe", 1, math.max(sizeLo - 1, 0))
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

function libc.sigaction()
    return 0, 0
end
)luau";

constexpr std::string_view JumpOperators = R"(
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
)";

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
    std::string result = "local data: {DataRange} = {\n";
    for (const auto& [start, end] : emitted) {
        for (auto first = start; first < end;) {
            auto last = end;
            if (const auto cut = std::ranges::upper_bound(cuts, first); cut != cuts.end() && *cut < last)
                last = *cut;
            auto used = last;
            while (used > first && image[used - 1] == 0)
                --used;
            result += std::format("    {{first = {}, last = {}, mode = {}, bytes = ", first, last, modeAt(first));
            appendQuoted(result, image.subspan(first, used - first));
            result += "},\n";
            first = last;
        }
    }
    return result + "}\n";
}

void appendRuntime(std::string& source, const RuntimeFeatures& features, const Data& data) {
    source += ArgumentReader;
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
    source += "\nlocal process = {initialized = false, exitCallbacks = {} :: {() -> ()}, "
        "fiberSlots = {} :: {[number]: {lo: number, hi: number, callbackLo: number, callbackHi: number}?}, "
        "fiberNext = 0, lastError = 0, exceptionFilterLo = 0, exceptionFilterHi = 0}\n";
    if (features.structured)
        source += RoutineOperators;
    if (features.stackGuard)
        source += "\n-- Synthetic guard for translated Linux x86-64 functions.\n"
            "local stackGuardLo, stackGuardHi = 0xa5a5a500, 0x5a5a5a5a\n";
    if (features.flags)
        source += FlagOperators;
    if (features.shifts)
        source += ShiftOperators;
    if (features.division)
        source += DivisionOperators;
    if (features.multiply)
        source += MultiplyOperators;
    if (features.floating)
        source += FloatingOperators;
    if (features.vector)
        source += VectorOperators;
    if (features.prime)
        source += PrimeOperators;
    if (features.decimal)
        source += DecimalOperators;
    if (features.jumpFrames)
        source += JumpOperators;
    if (features.memory) {
        source += MemoryOperators;
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
            source += ProcessOperators;
            source += UnwindLookups;
        }
        if (features.seh) {
            source += SehOperators;
            if (!data.unwindObjects.empty())
                source += std::format("seh.base, seh.stop, seh.table, seh.count = {}, {}, {}, {}\n",
                    data.unwindObjects.front().header, data.unwindObjects.front().end,
                    data.unwindObjects.front().frames, data.unwindObjects.front().framesSize / 12);
        }
        if (features.x87)
            source += X87Operators;
    }
}
}
