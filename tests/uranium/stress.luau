local function bigFunction(seed: number)
    local a1, a2, a3, a4, a5, a6, a7, a8 = seed, seed + 1, seed + 2, seed + 3, seed + 4, seed + 5, seed + 6, seed + 7
    local b1, b2, b3, b4, b5, b6, b7, b8 = a1 * 2, a2 * 3, a3 * 4, a4 * 5, a5 * 6, a6 * 7, a7 * 8, a8 * 9
    local labels = {"alpha", "beta", "gamma", "delta", "epsilon", "zeta", "eta", "theta", "iota", "kappa"}
    local result = {}
    for index, label in labels do
        local key = label .. "_" .. index
        if index % 3 == 0 then
            result[key] = a1 + b1 * index - a8
        elseif index % 3 == 1 then
            result[key] = string.format("%s:%d", label, b2 + a3 * index)
        else
            result[key] = {index, label:upper(), b4 - a5, (b6 + b7) // (a2 + 1)}
        end
    end
    local checksum = 0
    for key, value in pairs(result) do
        checksum += #key
        if type(value) == "number" then
            checksum += value
        elseif type(value) == "string" then
            checksum += #value
        else
            checksum += value[1] + #value[2] + value[3] + value[4]
        end
    end
    local accumulator = 0
    for i = 1, 50 do
        if i % 15 == 0 then
            accumulator += b8
        elseif i % 5 == 0 then
            accumulator -= a6
        elseif i % 3 == 0 then
            accumulator *= 1
            accumulator += b3
        else
            accumulator += i
        end
    end
    return checksum, accumulator, a4 + b5 + a7, b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8
end
for seed = 1, 3 do
    print(bigFunction(seed))
end
local dispatch = {
    add = function(x, y) return x + y end,
    sub = function(x, y) return x - y end,
    mul = function(x, y) return x * y end,
    div = function(x, y) return if y == 0 then nil else x / y end,
    pow = function(x, y) return x ^ y end,
}
local operations = {"add", "sub", "mul", "div", "pow"}
for _, op in operations do
    print(op, dispatch[op](12, 3), dispatch[op](2, 0))
end
return bigFunction
