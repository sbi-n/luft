local function range(n: number)
    return coroutine.wrap(function()
        for i = 1, n do
            coroutine.yield(i)
        end
    end)
end
local items = {}
for value in range(5) do
    table.insert(items, value * 3)
end
print(table.concat(items, " "))

local producer = coroutine.create(function(a, b)
    local c = coroutine.yield(a + b)
    local d, e = coroutine.yield(c * 2)
    return d + e
end)
print(coroutine.resume(producer, 1, 2))
print(coroutine.resume(producer, 10))
print(coroutine.resume(producer, 3, 4))
print(coroutine.status(producer), coroutine.resume(producer))

local function fibonacci()
    local a, b = 0, 1
    return coroutine.wrap(function()
        while true do
            coroutine.yield(a)
            a, b = b, a + b
        end
    end)
end
local nextFib = fibonacci()
local fibs = {}
for _ = 1, 12 do
    table.insert(fibs, nextFib())
end
print(table.concat(fibs, ","))
print(coroutine.isyieldable(), coroutine.running() ~= nil)
return fibs
