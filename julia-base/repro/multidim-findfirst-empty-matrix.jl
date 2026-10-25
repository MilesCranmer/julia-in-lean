# findfirst/findlast throw BoundsError on an empty matrix whose empty dimension is not the last one.
M = zeros(Bool, 0, 3)
r1 = try findfirst(M) catch e; e end
r2 = try findlast(M) catch e; e end
r3 = try findfirst(iszero, zeros(0, 2)) catch e; e end
r4 = try findlast(==(1), zeros(Int, 0, 2)) catch e; e end
r5 = try findfirst(zeros(Bool, 3, 0)) catch e; e end     # empty last dimension: fine
r6 = try findfirst(BitMatrix(undef, 0, 3)) catch e; e end
println(repr(r1), "\n", repr(r2), "\n", repr(r3), "\n", repr(r4), "\n", repr(r5), "\n", repr(r6))
if r1 isa BoundsError && r2 isa BoundsError && r3 isa BoundsError && r4 isa BoundsError && r5 === nothing
    println("REPRODUCED multidim-findfirst-empty-matrix")
end
