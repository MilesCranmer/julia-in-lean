# symdiff!(s::AbstractSet, itr) = symdiff!(s, Set(itr)) (base/abstractset.jl:297)
# collapses isequal but ===-distinct elements of itr before toggling them in an
# IdSet, which compares by ===.
a = [1]; b = [1]                     # a == b, a !== b
s = symdiff!(IdSet{Any}(), Any[a, b])
u = union!(IdSet{Any}(), Any[a, b])
t = symdiff!(IdSet{Any}(), IdSet{Any}(Any[a, b]))
n = symdiff(IdSet{Any}(), Any[1, 1.0])
println("symdiff!(IdSet{Any}(), [a, b]): length = ", length(s), ", a in = ", a in s, ", b in = ", b in s)
println("union!(IdSet{Any}(), [a, b]): length = ", length(u))
println("symdiff!(IdSet{Any}(), IdSet{Any}([a, b])): length = ", length(t))
println("symdiff(IdSet{Any}(), Any[1, 1.0]) = ", collect(n))
if length(s) == 1 && length(u) == 2 && length(t) == 2
    println("REPRODUCED iddicts-idset-symdiff")
end
