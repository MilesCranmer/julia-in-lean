# cat/vcat broadcast a scalar (and accept an empty array) whose size does not match
# the other arguments along a non-concatenated dimension, instead of throwing.
r1 = try vcat(1, [2 3]) catch e; e end              # scalar has 1 column, [2 3] has 2
r2 = try vcat([1], [2 3]) catch e; e end            # same shapes as arrays: DimensionMismatch
r3 = try cat([1 2], 3; dims=3) catch e; e end       # scalar is 1x1, [1 2] is 1x2
r4 = try cat([1 2], [3]; dims=3) catch e; e end
r5 = try cat(Int[], [1 2; 3 4]; dims=1) catch e; e end   # 0x1 and 2x2
r6 = try vcat(Int[], [1 2; 3 4]) catch e; e end
println(repr(r1), "\n", repr(r2), "\n", repr(r3), "\n", repr(r4), "\n", repr(r5), "\n", repr(r6))
if r1 == [1 1; 2 3] && r2 isa DimensionMismatch && r3 == cat([1 2], [3 3]; dims=3) &&
        r4 isa DimensionMismatch && r5 == [1 2; 3 4] && r6 isa DimensionMismatch
    println("REPRODUCED multidim-cat-scalar-shape")
end
