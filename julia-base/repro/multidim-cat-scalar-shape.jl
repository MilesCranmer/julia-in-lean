# cat/vcat broadcast a scalar (and accept an empty array) whose size does not match
# the other arguments along a non-concatenated dimension, instead of throwing.
r1 = try vcat(1, [2 3]) catch e; e end              # scalar has 1 column, [2 3] has 2
r2 = try vcat([1], [2 3]) catch e; e end            # same shapes as arrays: DimensionMismatch
r3 = try cat([1 2], 3; dims=3) catch e; e end       # scalar is 1x1, [1 2] is 1x2
r4 = try cat([1 2], [3]; dims=3) catch e; e end
r5 = try cat(Int[], [1 2; 3 4]; dims=1) catch e; e end   # 0x1 and 2x2
r6 = try vcat(Int[], [1 2; 3 4]) catch e; e end
r7 = try Base.cat_shape((true,), ((1,), (1, 2))) catch e; e end
r8 = try Base._cat_size_shape((true,), (1,), [1 2]) catch e; e end
r9 = try invoke(vcat, Tuple{Vararg{Any}}, Int[], [1 2; 3 4]) catch e; e end
r10 = try invoke(Base.typed_vcat, Tuple{Type{Int}, Vararg{Any}}, Int, Int[], [1 2; 3 4]) catch e; e end
r11 = try Base._cat(Val(1), Int[], [1 2; 3 4]) catch e; e end
r12 = try Base.cat_t(Int, Int[], [1 2; 3 4]; dims=1) catch e; e end
r13 = try invoke(vcat, Tuple{AbstractArray,AbstractArray}, Int[], [1 2; 3 4]) catch e; e end
r14 = try invoke(Base.typed_vcat, Tuple{Type{Int},AbstractArray,AbstractArray}, Int, Int[], [1 2; 3 4]) catch e; e end
println("two-array vcat => ", repr(r13), "\ntwo-array typed_vcat => ", repr(r14))
println("_cat => ", repr(r11), "\ncat_t => ", repr(r12))
println("generic vcat => ", repr(r9), "\ngeneric typed_vcat => ", repr(r10))
println("cat_shape => ", repr(r7), "\n_cat_size_shape => ", repr(r8))
println(repr(r1), "\n", repr(r2), "\n", repr(r3), "\n", repr(r4), "\n", repr(r5), "\n", repr(r6))
if r1 == [1 1; 2 3] && r2 isa DimensionMismatch && r3 == cat([1 2], [3 3]; dims=3) &&
        r4 isa DimensionMismatch && r5 == [1 2; 3 4] && r6 isa DimensionMismatch &&
        r7 == (2, 2) && r8 == (2, 2) && r9 == [1 2; 3 4] && r10 == [1 2; 3 4] &&
        r11 == [1 2; 3 4] && r12 == [1 2; 3 4] && r13 == [1 2; 3 4] && r14 == [1 2; 3 4]
    println("REPRODUCED multidim-cat-scalar-shape")
end
