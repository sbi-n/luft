local inventory = {
    apples = 3,
    pears = 0,
    ["sweet potatoes"] = 12,
    nested = { deep = { deeper = { value = "found" } } },
    list = {10, 20, 30, 40},
}
inventory.pears += 7
inventory.list[#inventory.list + 1] = 50
table.insert(inventory.list, 1, 5)
table.remove(inventory.list, 3)
print(inventory.nested.deep.deeper.value, #inventory.list, inventory.list[3])

local names = {}
for name in pairs(inventory) do
    table.insert(names, name)
end
table.sort(names)
print(table.concat(names, "|"))

local people = {
    {name = "Ana", age = 31},
    {name = "Bo", age = 25},
    {name = "Cy", age = 31},
    {name = "Di", age = 19},
}
table.sort(people, function(a, b)
    if a.age ~= b.age then
        return a.age > b.age
    end
    return a.name < b.name
end)
for index, person in ipairs(people) do
    print(index, person.name, person.age)
end

local matrix = table.create(3)
for row = 1, 3 do
    matrix[row] = table.create(3, 0)
    for column = 1, 3 do
        matrix[row][column] = row * 10 + column
    end
end
print(matrix[2][3], table.find(matrix[3], 32), table.unpack(matrix[1]))

local frozen = table.freeze({a = 1})
print(table.isfrozen(frozen), pcall(function() (frozen :: any).a = 2 end))
local copy = table.clone(inventory.list)
table.clear(inventory.list)
print(#copy, #inventory.list, rawlen(copy), rawequal(copy, copy))
return inventory
