# issubset(a, b) returns false as soon as a is an AbstractSet longer than b
# (base/abstractset.jl:340-342). An IdSet can hold more elements than an
# isequal-based b although every one of them is `in` b.
a = IdSet{Any}(Any[1, 1.0])
s = Set([1])
println("a ⊆ Set([1]) = ", a ⊆ s, "; all(x -> x in Set([1]), a) = ", all(x -> x in s, a))
println("a ⊆ [1] = ", a ⊆ Any[1], "; all(x -> x in [1], a) = ", all(x -> x in Any[1], a))
x = [1]; y = [1]
c = IdSet{Any}(Any[x, y])
println("IdSet{Any}([x, y]) ⊆ [x] = ", c ⊆ Any[x], "; all in = ", all(z -> z in Any[x], c), " with x == y, x !== y")
if !(a ⊆ s) && all(x -> x in s, a) && !(c ⊆ Any[x]) && all(z -> z in Any[x], c)
    println("REPRODUCED iddicts-idset-issubset")
end
