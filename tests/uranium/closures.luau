local function counter(start: number, step: number?)
    local value = start
    local increment = step or 1
    return function()
        value += increment
        return value
    end, function()
        value = start
    end
end

local next1, reset1 = counter(10)
local next2 = counter(0, 5)
print(next1(), next1(), next2(), next2())
reset1()
print(next1())

local function sum(...)
    local total = 0
    for i = 1, select("#", ...) do
        total += select(i, ...)
    end
    return total, select("#", ...)
end
print(sum(1, 2, 3, 4))

local function curry(f)
    return function(a)
        return function(b)
            return f(a, b)
        end
    end
end
local add = curry(function(a, b) return a + b end)
print(add(3)(4))

local memo = {}
local function fib(n: number): number
    if n < 2 then
        return n
    end
    local cached = memo[n]
    if cached then
        return cached
    end
    local result = fib(n - 1) + fib(n - 2)
    memo[n] = result
    return result
end
print(fib(60))

local callbacks = {}
for i = 1, 5 do
    callbacks[i] = function() return i * i end
end
local results = {}
for _, callback in ipairs(callbacks) do
    table.insert(results, callback())
end
print(table.concat(results, ","))

local function pack(...)
    return {n = select("#", ...), ...}
end
local packed = pack(nil, 2, nil)
print(packed.n, packed[2])
return fib
