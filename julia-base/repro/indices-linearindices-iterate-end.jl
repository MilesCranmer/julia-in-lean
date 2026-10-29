# iterate(iter::LinearIndices, i=1) = i > length(iter) ? nothing : (i, i+1)
# (base/indices.jl:523). For a LinearIndices of length typemax(Int) the state after the last
# element, typemax(Int) + 1, wraps to typemin(Int), which is not > length(iter), so iteration
# continues with the invalid linear index typemin(Int) instead of ending.
L = LinearIndices((typemax(Int), 1))
n = length(L)
println("length(LinearIndices((typemax(Int), 1))) = ", n)
last_step = iterate(L, n)
println("iterate(L, length(L)) = ", last_step)
after = iterate(L, last_step[2])
println("iterate(L, ", last_step[2], ") = ", repr(after))
if last_step[1] == n && after !== nothing
    println("REPRODUCED indices-linearindices-iterate-end")
end
