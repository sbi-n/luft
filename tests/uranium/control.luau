local function classify(n: number): string
    if n < 0 then
        return "negative"
    elseif n == 0 then
        return "zero"
    elseif n % 2 == 0 and n > 100 then
        return "big even"
    elseif n % 2 == 0 then
        return "even"
    else
        return "odd"
    end
end
for _, value in {-5, 0, 4, 7, 200} do
    print(value, classify(value))
end

local total = 0
for i = 10, 1, -2 do
    if i == 6 then
        continue
    end
    total += i
end
print(total)

local n = 27
local steps = 0
while n ~= 1 do
    n = if n % 2 == 0 then n // 2 else 3 * n + 1
    steps += 1
    if steps > 1000 then
        break
    end
end
print(steps)

local attempts = 0
repeat
    attempts += 1
    local done = attempts * attempts > 50
until done
print(attempts)

local found = nil
for x = 1, 20 do
    for y = 1, 20 do
        if x * y == 91 and x < y then
            found = {x, y}
            break
        end
    end
    if found then
        break
    end
end
print(found and found[1], found and found[2])

local grade = function(score)
    return if score >= 90 then "A" elseif score >= 80 then "B" elseif score >= 70 then "C" else "F"
end
print(grade(95), grade(85), grade(75), grade(10))
local a, b, c = 1, nil, false
print(a and b, a or b, b or c, not c, c == false, a ~= nil)
return total
