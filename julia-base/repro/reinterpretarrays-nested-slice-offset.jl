# view(V, :) of a view with an IdentityUnitRange index reads and writes the wrong parent elements
IUR = Base.IdentityUnitRange
M = reshape(collect(1:20), 4, 5)
V = view(M, IUR(2:3), 2)                 # V[2] == M[2,2] == 6, V[3] == M[3,2] == 7
W = view(V, :)                           # same axes as V
println("V[2], V[3] = ", V[2], ", ", V[3], ";  view(V, :)[2], [3] = ", W[2], ", ", W[3])
I = (Base.Slice(axes(V, 1)),)
unsafe = Base.unsafe_view(V, I...)
reindexed = Base._maybe_reindex(V, I)
println("unsafe_view(V, Slice(...))[2] = ", unsafe[2],
        "; _maybe_reindex(V, (Slice(...),))[2] = ", reindexed[2])
offset = Base.compute_offset1(M, W.stride1, W.indices)
println("compute_offset1 for nested Slice = ", offset,
        "; parent linear index at 2 = ", offset + W.stride1 * 2)
constructed = Base.SubArray(Base.IndexLinear(), M, W.indices, Base.index_dimsum(W.indices...))
println("linear SubArray constructor reads ", constructed[2], " instead of ", V[2])
generic_fast_read = invoke(getindex, Tuple{Base.FastSubArray, Int}, constructed, 2)
println("generic fast getindex reads ", generic_fast_read)
pointer_shifted = GC.@preserve M constructed pointer(constructed, 2) == pointer(M, 7)
println("pointer on the nested view targets parent index 7: ", pointer_shifted)
strided_parent = view(M, 1, IUR(2:3))
strided = view(strided_parent, :)
strided_pointer_shifted = GC.@preserve M strided pointer(strided, 2) == pointer(M, 9)
println("pointer on the strided nested view targets parent index 9: ", strided_pointer_shifted)
Mwrite = copy(M)
Wwrite = view(view(Mwrite, IUR(2:3), 2), :)
Wwrite[2] = 0
write_shifted = Mwrite[3, 2] == 0 && Mwrite[2, 2] == M[2, 2]
println("setindex! on the nested view writes the shifted element: ", write_shifted)
U = Matrix{Any}(undef, 4, 5)
U[3, 2] = 1
VU = view(U, IUR(2:3), 2)
WU = view(VU, :)
assignment_shifted = !isassigned(VU, 2) && isassigned(WU, 2)
println("isassigned on the nested view reports the shifted element: ", assignment_shifted)
M2 = copy(M); fill!(view(view(M2, IUR(2:3), 2), :), 0)
println("fill!(view(view(M, IUR(2:3), 2), :), 0) zeroed ", Tuple.(findall(M2 .!= M)))
M3 = copy(M); copyto!(view(M3, IUR(2:3), 2), view(M3, IUR(2:3), 2))
println("copyto!(V, V) changed column 2 from ", M[:, 2], " to ", M3[:, 2])
X = view(M, IUR(3:4), 5)                 # last column
Y = view(X, :)
println("view(view(M, IUR(3:4), 5), :) reads parent linear index ", Y.offset1 + Y.stride1 * 4, " for index 4; length(M) = ", length(M))
if W[2] == M[3, 2] && unsafe[2] == M[3, 2] && reindexed[2] == M[3, 2] && constructed[2] == M[3, 2] && generic_fast_read == M[3, 2] && pointer_shifted && strided_pointer_shifted && write_shifted && assignment_shifted && offset == W.offset1 && offset + W.stride1 * 2 == LinearIndices(M)[3, 2] && Tuple.(findall(M2 .!= M)) == [(3, 2), (4, 2)] && M3[:, 2] != M[:, 2] && Y.offset1 + Y.stride1 * 4 > length(M)
    println("REPRODUCED reinterpretarrays-nested-slice-offset")
end
