a = (10, 20)[true]
b = try
    [10, 20][true]
catch e
    e
end
println(a, " ", b)
println(get((1, 2), true, 0), " ", Base.setindex((1, 2), 0, true), " ", isassigned((1, 2), true))
if a == 10 && b isa ArgumentError
    println("REPRODUCED tuples-getindex-bool")
end
