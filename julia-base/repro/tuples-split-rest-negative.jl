f, l = Base.split_rest(Any[1, 2, 3], -1)
println(length(f), " ", length(l), " ", isassigned(f, 4))
s = try
    Base.split_rest("abc", -1)
catch e
    e
end
println(s)
if length(f) == 4 && !isassigned(f, 4)
    println("REPRODUCED tuples-split-rest-negative")
end
