a = try
    (10, 20)[false:true]
catch e
    e
end
b = (10, 20)[[false, true]]
c = [10, 20][false:true]
println(a, " ", b, " ", c, " ", (1, 2, 3)[true:true])
if a isa BoundsError && b == (20,)
    println("REPRODUCED tuples-getindex-bool-range")
end
