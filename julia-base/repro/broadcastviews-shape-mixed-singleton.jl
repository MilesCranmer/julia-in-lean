# broadcast_shape treats a singleton axis as non-broadcastable when combined with an integer size.
f(a, b) = try Broadcast.broadcast_shape(a, b) catch e; e end
println("broadcast_shape((3,), (1,)) = ", f((3,), (1,)))
println("broadcast_shape((Base.OneTo(3),), (Base.OneTo(1),)) = ", f((Base.OneTo(3),), (Base.OneTo(1),)))
println("broadcast_shape((1,), (Base.OneTo(3),)) = ", f((1,), (Base.OneTo(3),)))
r = f((3,), (Base.OneTo(1),))
println("broadcast_shape((3,), (Base.OneTo(1),)) = ", r)
if r isa DimensionMismatch
    println("REPRODUCED broadcastviews-shape-mixed-singleton")
end
