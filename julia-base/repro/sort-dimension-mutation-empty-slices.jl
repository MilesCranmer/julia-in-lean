# sort!(A; dims) on an empty array throws when size(A, dims) >= 30, dims != 1 and another
# dimension has length 0: the temporary-vector branch calls get_view(first(idxs)) on empty
# CartesianIndices. With size(A, dims) < 30 the same empty array is returned unchanged.
A = zeros(0, 30)
r = try
    sort!(copy(A); dims=2)
catch e
    e
end
println("sort!(zeros(0, 30); dims=2) -> ", r isa Exception ? sprint(showerror, r) : summary(r))
small = sort!(zeros(0, 29); dims=2)
println("sort!(zeros(0, 29); dims=2) -> ", summary(small))
if r isa BoundsError && size(small) == (0, 29)
    println("REPRODUCED sort-dimension-mutation-empty-slices")
end
