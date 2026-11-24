type Token = {kind: string, value: string | number}

local function tokenize(source: string): {Token}
    local tokens: {Token} = {}
    local i = 1
    while i <= #source do
        local c = source:sub(i, i)
        if c:match("%s") then
            i += 1
        elseif c:match("%d") then
            local number = source:match("^%d+%.?%d*", i)
            table.insert(tokens, {kind = "number", value = tonumber(number) :: number})
            i += #number
        elseif c:match("%a") then
            local name = source:match("^[%a_][%w_]*", i)
            table.insert(tokens, {kind = "name", value = name})
            i += #name
        else
            table.insert(tokens, {kind = "op", value = c})
            i += 1
        end
    end
    return tokens
end

local precedence = {["+"] = 1, ["-"] = 1, ["*"] = 2, ["/"] = 2, ["^"] = 3}

local function evaluate(source: string, variables: {[string]: number}): number
    local tokens = tokenize(source)
    local position = 1
    local parseExpression

    local function parsePrimary(): number
        local token = tokens[position]
        position += 1
        if token.kind == "number" then
            return token.value :: number
        elseif token.kind == "name" then
            local name = token.value :: string
            if tokens[position] and tokens[position].value == "(" then
                position += 1
                local argument = parseExpression(0)
                position += 1
                if name == "sqrt" then
                    return math.sqrt(argument)
                elseif name == "abs" then
                    return math.abs(argument)
                end
                error("unknown function " .. name)
            end
            return variables[name] or error("unknown variable " .. name)
        elseif token.value == "(" then
            local value = parseExpression(0)
            position += 1
            return value
        elseif token.value == "-" then
            return -parsePrimary()
        end
        error("unexpected token " .. tostring(token.value))
    end

    function parseExpression(minimum: number): number
        local left = parsePrimary()
        while true do
            local token = tokens[position]
            local level = token and precedence[token.value :: string]
            if not level or level < minimum then
                break
            end
            position += 1
            local right = parseExpression(if token.value == "^" then level else level + 1)
            local op = token.value
            if op == "+" then left += right
            elseif op == "-" then left -= right
            elseif op == "*" then left *= right
            elseif op == "/" then left /= right
            else left ^= right end
        end
        return left
    end

    return parseExpression(0)
end

local variables = {x = 3, y = 4, rate = 0.5}
for _, expression in {"1 + 2 * 3", "(1 + 2) * 3", "sqrt(x * x + y * y)", "2 ^ 3 ^ 2", "-x + abs(-y) * rate", "10 / 4 - 1"} do
    print(expression, "=", evaluate(expression, variables))
end
print(pcall(evaluate, "unknown + 1", variables))
return evaluate
