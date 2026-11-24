local Vector = {}
Vector.__index = Vector

function Vector.new(x: number, y: number)
    return setmetatable({x = x, y = y}, Vector)
end

function Vector.__add(a, b)
    return Vector.new(a.x + b.x, a.y + b.y)
end

function Vector.__eq(a, b)
    return a.x == b.x and a.y == b.y
end

function Vector.__lt(a, b)
    return a:length() < b:length()
end

function Vector.__tostring(self)
    return "(" .. self.x .. ", " .. self.y .. ")"
end

function Vector.__len(self)
    return 2
end

function Vector:length()
    return math.sqrt(self.x * self.x + self.y * self.y)
end

local Animal = {}
Animal.__index = Animal
function Animal.new(name, sound)
    local self = setmetatable({}, Animal)
    self.name = name
    self.sound = sound
    return self
end
function Animal:speak()
    return self.name .. " says " .. self.sound
end

local Dog = setmetatable({}, {__index = Animal})
Dog.__index = Dog
function Dog.new(name)
    local self = Animal.new(name, "woof")
    return setmetatable(self, Dog)
end
function Dog:fetch(item)
    return self.name .. " fetches the " .. item
end

local a, b = Vector.new(3, 4), Vector.new(1, 2)
print(tostring(a + b), a == Vector.new(3, 4), b < a, #a, a:length())
local dog = Dog.new("Rex")
print(dog:speak(), dog:fetch("ball"), getmetatable(dog) == Dog)

local log = {}
local proxy = setmetatable({}, {
    __index = function(_, key)
        table.insert(log, "get " .. key)
        return key:upper()
    end,
    __newindex = function(t, key, value)
        table.insert(log, "set " .. key)
        rawset(t, key, value * 2)
    end,
    __call = function(_, x)
        return x + 1
    end,
})
print(proxy.hello, proxy(41))
proxy.n = 21
print(proxy.n, table.concat(log, ";"))
return Vector
