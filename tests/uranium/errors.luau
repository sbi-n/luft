local function risky(n: number)
    if n < 0 then
        error("negative input: " .. n)
    elseif n == 0 then
        error({code = 42, message = "zero"})
    end
    return math.sqrt(n)
end
print(pcall(risky, 16))
local ok, err = pcall(risky, -1)
print(ok, string.match(err, "negative input: %-1$") ~= nil)
local ok2, err2 = pcall(risky, 0)
print(ok2, type(err2), err2.code, err2.message)
print(xpcall(function() return risky(-2) end, function(message)
    return "handled: " .. tostring(string.match(message, "negative input: .*"))
end))
local ok3, err3 = pcall(function()
    local t = nil
    return t.field
end)
print(ok3, typeof(err3))
local function cleanup()
    local log = {}
    local success = pcall(function()
        table.insert(log, "start")
        error("boom", 0)
        table.insert(log, "unreachable")
    end)
    table.insert(log, if success then "ok" else "failed")
    return table.concat(log, "/")
end
print(cleanup(), select("#", pcall(error)))
print(pcall(assert, false, "assertion text"), pcall(assert, 1, 2))
return cleanup
