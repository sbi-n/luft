local function quicksort(list: {number}, low: number?, high: number?)
    local lo = low or 1
    local hi = high or #list
    if lo < hi then
        local pivot = list[hi]
        local i = lo - 1
        for j = lo, hi - 1 do
            if list[j] <= pivot then
                i += 1
                list[i], list[j] = list[j], list[i]
            end
        end
        list[i + 1], list[hi] = list[hi], list[i + 1]
        quicksort(list, lo, i)
        quicksort(list, i + 2, hi)
    end
    return list
end

local function binarySearch(list: {number}, target: number): number?
    local low, high = 1, #list
    while low <= high do
        local middle = (low + high) // 2
        if list[middle] == target then
            return middle
        elseif list[middle] < target then
            low = middle + 1
        else
            high = middle - 1
        end
    end
    return nil
end

local function sieve(limit: number): {number}
    local composite = {}
    local primes = {}
    for n = 2, limit do
        if not composite[n] then
            table.insert(primes, n)
            for multiple = n * n, limit, n do
                composite[multiple] = true
            end
        end
    end
    return primes
end

local function serialize(value, indent: string?): string
    indent = indent or ""
    if type(value) == "table" then
        local keys = {}
        for key in pairs(value) do
            table.insert(keys, key)
        end
        table.sort(keys, function(a, b) return tostring(a) < tostring(b) end)
        local parts = {}
        for _, key in keys do
            table.insert(parts, indent .. "  " .. tostring(key) .. ": " .. serialize(value[key], indent .. "  "))
        end
        return "{\n" .. table.concat(parts, ",\n") .. "\n" .. indent .. "}"
    elseif type(value) == "string" then
        return string.format("%q", value)
    end
    return tostring(value)
end

local seed = 12345
local function random(): number
    seed = (seed * 1103515245 + 12345) % 2147483648
    return seed
end
local numbers = {}
for i = 1, 40 do
    numbers[i] = random() % 1000
end
quicksort(numbers)
print(table.concat(numbers, " "))
print(binarySearch(numbers, numbers[17]), binarySearch(numbers, -1))
local primes = sieve(100)
print(#primes, primes[#primes], table.concat(primes, ","))
print(serialize({name = "luau", tags = {"fast", "safe"}, version = 0.736, nested = {flag = true}}))
return quicksort
