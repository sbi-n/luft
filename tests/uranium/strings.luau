local text = "The quick brown fox jumps over the lazy dog"
print(#text, text:upper(), text:lower():sub(5, 9))
print(text:find("fox"), text:match("(%a+) dog"), string.rep("ab", 3, "-"))
local words = {}
for word in text:gmatch("%a+") do
    table.insert(words, word:reverse())
end
print(table.concat(words, " "))
local replaced, count = text:gsub("(%w+)", function(word)
    if #word > 4 then
        return word:upper()
    end
    return nil
end)
print(replaced, count)
print(string.format("%5.2f|%-6s|%x|%q|%d%%", math.pi, "pad", 255, "quote\"d", 42))
local name, age = "Luau", 7
print(`{name} is {age * 2} half-years old; nested {`{age}`}`)
print(("a,b,,c"):split(","), #("a,b,,c"):split(","))
local bytes = {string.byte("Hello", 1, -1)}
print(table.concat(bytes, " "), string.char(72, 105))
local buffer = {}
for i = 1, 20 do
    buffer[#buffer + 1] = tostring(i % 7)
end
print(table.concat(buffer))
print(tostring(nil), tostring(true), tonumber("0x1F"), tonumber("  42  "), tonumber("1e3"), tonumber("z", 36))
return replaced
