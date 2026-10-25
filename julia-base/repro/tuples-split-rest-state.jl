function mid(t)
    a, b..., c = t
    return (a, b, c)
end
r = mid((1,))
println(r)
q = mid((x = 1,))
println(q)
s = Base.split_rest((1, 2, 3), 2, 3)
println(s)
v = try
    Base.split_rest([1, 2, 3], 2, 3)
catch e
    e
end
println(v)
if r == (1, (), 1) && q == (1, NamedTuple(), 1) && s == ((), (2, 3)) && v isa ArgumentError
    println("REPRODUCED tuples-split-rest-state")
end
