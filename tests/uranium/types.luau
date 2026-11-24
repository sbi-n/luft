--!strict
export type Shape = {kind: "circle", radius: number} | {kind: "rect", width: number, height: number}

type Pair<A, B> = {first: A, second: B}

local function area(shape: Shape): number
    if shape.kind == "circle" then
        return math.pi * shape.radius ^ 2
    else
        return shape.width * shape.height
    end
end

local function swap<A, B>(pair: Pair<A, B>): Pair<B, A>
    return {first = pair.second, second = pair.first}
end

local function map<T, U>(list: {T}, f: (T) -> U): {U}
    local result: {U} = {}
    for index, item in list do
        result[index] = f(item)
    end
    return result
end

local shapes: {Shape} = {
    {kind = "circle", radius = 2},
    {kind = "rect", width = 3, height = 4},
}
local areas = map(shapes, area)
print(string.format("%.3f %.3f", areas[1], areas[2]))
local swapped = swap({first = 1, second = "one"})
print(swapped.first, swapped.second)
local maybe: number? = nil
local value = (maybe or 3) :: number
print(value, typeof(value), typeof(shapes), type(print))
local function describe(x: unknown): string
    if typeof(x) == "number" then
        return "number " .. tostring(x)
    elseif typeof(x) == "string" then
        return "string " .. (x :: string)
    end
    return "other"
end
print(describe(1), describe("s"), describe({}))
return areas
