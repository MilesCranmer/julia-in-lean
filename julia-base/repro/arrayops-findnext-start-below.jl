println(repr(findnext(iseven, [1, 2], 3)))
println(repr(findprev(iseven, [1, 2], 0)))
e1 = try findnext(iseven, [1, 2], 0); nothing catch e; e end
e2 = try findprev(iseven, [1, 2], 3); nothing catch e; e end
println(repr(e1))
println(repr(e2))
if e1 isa BoundsError && e2 isa BoundsError
    println("REPRODUCED arrayops-findnext-start-below")
end
