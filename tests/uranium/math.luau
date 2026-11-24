local values = {7, -7, 2.5, -2.5, 1e10, 0.1}
for _, v in values do
    print(v, v // 2, v % 3, v ^ 2, math.floor(v), math.ceil(v), math.abs(v), math.sign(v))
end
print(math.max(3, 9, -1), math.min(3, 9, -1), math.clamp(15, 0, 10), math.round(2.5), math.round(-2.5))
print(math.sqrt(2), math.sin(1), math.cos(1), math.exp(1), math.log(10), math.log(8, 2), math.fmod(7, 3))
print(bit32.band(0xF0F0, 0x0FF0), bit32.bor(1, 2, 4), bit32.bxor(0xFF, 0x0F), bit32.lshift(1, 31), bit32.rshift(0x80000000, 4))
print(bit32.arshift(0x80000000, 4), bit32.extract(0xABCD, 4, 8), bit32.replace(0, 0xF, 8, 4), bit32.countlz(1), bit32.countrz(8))
local x = 10
x += 5
x -= 3
x *= 2
x /= 4
x //= 1
x %= 4
x ^= 3
print(x)
local big = 2 ^ 53
print(big, big + 1, -big, 1 / 0, -1 / 0, 0 / 0 ~= 0 / 0)
print(string.format("%.17g", 0.1 + 0.2), 9007199254740993, 1e300 * 1e10)
local sum = 0
for i = 1, 100 do
    sum += i * i
end
print(sum, sum / 3, math.floor(sum / 3), 255 // 16, -255 // 16)
return sum
