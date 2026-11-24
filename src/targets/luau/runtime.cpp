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
type GuestRoutine = (number) -> GuestRoutine?

local function runGuestRoutine(action: GuestRoutine, expectedReturn: number)
    local nextAction: GuestRoutine? = action
    while nextAction do
        nextAction = nextAction(expectedReturn)
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

local function makeMemory(imageSize: number, data: {DataRange}, heapEnabled: boolean, mapped: boolean)
    local stackSize = if mapped then 262144 else 65536
    local heapLimit = if mapped then 67108864 else 16777216
    local stackBottom = math.ceil(imageSize / 16) * 16
    local stackTop = stackBottom + stackSize
    local stackData: buffer? = nil
    local stackInUse = false
    local contents: {buffer?} = {}
    local heap: {[number]: buffer} = {}
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
    local function reset(stack: boolean)
        stackInUse = stack
        if stack then
            local bytes = stackData
            if bytes then
                buffer.fill(bytes, 0, 0)
            else
                stackData = buffer.create(stackSize)
            end
        end
        table.clear(contents)
        table.clear(criticalSections)
        table.clear(pthreadLocks)
        table.clear(srwLocks)
        table.clear(pageProtection)
        if heapEnabled then
            table.clear(heap)
            table.clear(heapStarts)
            table.clear(heapPages)
            nextAllocation = heapStart
            lastHeapStart = 0
            classicLocale = 0
            useGlobalLocale = true
        end
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
                    local initialized = buffer.fromstring(range.bytes)
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
            return 0, 0
        end
        if previous and buffer.len(previous) == size then
            return at, 0
        end
        local length = math.ceil(size / 16) * 16
        if nextAllocation + length - heapStart > heapLimit then
            return 0, 0
        end
        local bytes = buffer.create(size)
        if previous then
            buffer.copy(bytes, 0, previous, 0, math.min(size, buffer.len(previous)))
            heap[at] = nil
        end
        local start = nextAllocation
        heap[start] = bytes
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
            return 1, 0
        elseif op == "HeapSize" then
            if previous then return buffer.len(previous), 0 end
            return 4294967295, 4294967295
        end
        local result = 0
        if op == "HeapAlloc" then
            result = resize(0, 0, math.max(pointer, 1), pointerHi)
        elseif previous and size and sizeHi == 0 then
            if bit32.band(flags, 16) == 0 then
                result = resize(pointer, 0, math.max(size, 1), 0)
            elseif size <= math.ceil(buffer.len(previous) / 16) * 16 then
                local bytes = buffer.create(math.max(size, 1))
                buffer.copy(bytes, 0, previous, 0, math.min(buffer.len(bytes), buffer.len(previous)))
                heap[pointer] = bytes
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
        elseif depth == nil then
            error("uninitialized guest critical section", 0)
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
        wideClass, testWideClass, pthreadMutex, srwLock
end
)";

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
    const auto region = std::ranges::find_if(regions, [&](const GuestRegion& value) {
        return value.readable && !value.executable && at >= value.start && at + size <= value.end;
    });
    const unsigned mode = region == regions.end() ? 0 :
        unsigned(region->writable) + (region->protectable ? 2 : 0);
    for (unsigned i = 0; i < size; ++i)
        emitted.emplace(at + i, std::pair(image[at + i], mode));
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
    if (!readable(at, 1) || writable(at, 1) || emitted.contains(at))
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
    std::string result = "local data: {DataRange} = {\n";
    for (auto it = emitted.begin(); it != emitted.end();) {
        const auto start = it->first;
        auto end = start;
        const auto mode = it->second.second;
        std::vector<std::uint8_t> bytes;
        for (; it != emitted.end() && it->first == end && it->second.second == mode; ++it, ++end)
            bytes.push_back(it->second.first);
        result += std::format("    {{first = {}, last = {}, mode = {}, bytes = ", start, end, mode);
        appendQuoted(result, bytes);
        result += "},\n";
    }
    return result + "}\n";
}

void appendRuntime(std::string& source, const RuntimeFeatures& features, const Data& data) {
    source += ArgumentReader;
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
            "criticalSection, protectMemory, cLocale, useCLocale, wideClass, testWideClass, pthreadMutex, srwLock = makeMemory({}, data, {}, {})\n",
            data.image.size(), features.heap, !data.regions.empty());
    }
}
}
