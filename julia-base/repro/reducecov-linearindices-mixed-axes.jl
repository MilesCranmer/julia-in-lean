# LinearIndices(inds) with a mixed tuple of integers and ranges converts each range
# with _convert2ind(r) = first(r):last(r) (base/indices.jl:490), which drops offset axes:
# the axes of LinearIndices((Base.IdentityUnitRange(3:5), 2)) start at 1, while
# LinearIndices((Base.IdentityUnitRange(3:5), Base.OneTo(2))) keeps 3:5.
a = axes(LinearIndices((Base.IdentityUnitRange(3:5), 2)))
b = axes(LinearIndices((Base.IdentityUnitRange(3:5), Base.OneTo(2))))
println("axes(LinearIndices((Base.IdentityUnitRange(3:5), 2))) = ", a)
println("axes(LinearIndices((Base.IdentityUnitRange(3:5), Base.OneTo(2)))) = ", b)
if first(a[1]) == 1 && first(b[1]) == 3
    println("REPRODUCED reducecov-linearindices-mixed-axes")
end
