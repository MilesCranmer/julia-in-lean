# LinearIndices((3:5,)) has axes (Base.OneTo(3),) and holds 1, 2, 3, and indexing it with
# an Int returns that Int. Indexing it with a range returns iter.indices[1][i]
# (base/indices.jl:514-518), i.e. elements of 3:5, not the linear indices.
L = LinearIndices((3:5,))
println("axes(LinearIndices((3:5,))) = ", axes(L))
println("collect(LinearIndices((3:5,))) = ", collect(L))
println("LinearIndices((3:5,))[2] = ", L[2], ", [3] = ", L[3])
r = L[2:3]
println("LinearIndices((3:5,))[2:3] = ", repr(r))
println("collect(LinearIndices((3:5,)))[2:3] = ", collect(L)[2:3])
if collect(r) != collect(L)[2:3]
    println("REPRODUCED reducecov-linearindices-range-index")
end
