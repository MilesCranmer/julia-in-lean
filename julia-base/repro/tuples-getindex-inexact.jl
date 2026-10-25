err(f) = try
    f()
catch e
    e
end
a = err(() -> (1, 2)[typemax(UInt)])
b = err(() -> Base.setindex((1, 2), 0, typemax(UInt)))
c = err(() -> [1, 2][typemax(UInt)])
println(typeof(a), " ", typeof(b), " ", typeof(c), " ", isassigned((1, 2), typemax(UInt)))
if a isa InexactError && b isa BoundsError
    println("REPRODUCED tuples-getindex-inexact")
end
