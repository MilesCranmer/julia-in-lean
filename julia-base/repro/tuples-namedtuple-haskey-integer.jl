nt = (a = 1,)
h = try
    haskey(nt, Int32(1))
catch e
    e
end
g = try
    get(nt, 0x01, 0)
catch e
    e
end
println(haskey(nt, 1), " ", get(nt, 1, 0))
println(h)
println(g)
if h isa TypeError && g isa TypeError
    println("REPRODUCED tuples-namedtuple-haskey-integer")
end
