v = [1, 2, 3]
i = UInt(2)^63
e1 = try v[i]; nothing catch e; e end
e2 = try LinearIndices(v)[i]; nothing catch e; e end
e3 = try CartesianIndices(v)[i]; nothing catch e; e end
e4 = try v[Int128(2)^64]; nothing catch e; e end
println(repr(e1))
println(repr(e2))
println(repr(e3))
println(repr(e4))
println(checkbounds(Bool, v, i), " ", checkbounds(Bool, LinearIndices(v), i))
if e1 isa BoundsError && e2 isa InexactError
    println("REPRODUCED arrayops-index-type-exception")
end
