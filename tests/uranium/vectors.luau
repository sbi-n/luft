local a = vector.create(1, 2, 3)
local b = vector.create(0.5, -1, 4)
local sum = a + b
local scaled = a * 2
local mixed = (a - b) / vector.create(2, 2, 2)
print(sum.x, sum.y, sum.z, scaled, mixed)
print(vector.magnitude(vector.create(3, 4, 0)), vector.dot(a, b), vector.cross(a, b))
print(vector.normalize(vector.create(0, 3, 4)), vector.floor(vector.create(1.5, -1.5, 2)))
print(vector.zero, vector.one, a == vector.create(1, 2, 3), -a)
local function centroid(points: {vector}): vector
    local total = vector.zero
    for _, point in points do
        total += point
    end
    return total / #points
end
print(centroid({vector.create(0, 0, 0), vector.create(2, 4, 6), vector.create(4, 2, 0)}))
return centroid
