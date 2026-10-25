# issetequal(a::AbstractSet, b) = issetequal(a, Set(b)) (base/abstractset.jl:522)
# and ==(::AbstractSet, ::AbstractSet) compares lengths first
# (base/abstractset.jl:622). For an IdSet holding isequal but ===-distinct
# elements, the lengths differ although a ⊆ b and b ⊆ a both hold.
a = IdSet{Any}(Any[1, 1.0])
b = Any[1, 1.0]
println("issetequal(a, b) = ", issetequal(a, b))
println("issetequal(b, a) = ", issetequal(b, a))
println("a ⊆ b = ", a ⊆ b, ", b ⊆ a = ", b ⊆ a)
x = [1]; y = [1]
c = IdSet{Any}(Any[x, y])
d = Any[x, y]
println("issetequal(IdSet{Any}([x, y]), [x, y]) = ", issetequal(c, d), " with x == y, x !== y")
println("IdSet{Any}([x, y]) ⊆ [x, y] = ", c ⊆ d, ", [x, y] ⊆ IdSet{Any}([x, y]) = ", d ⊆ c)
if !issetequal(a, b) && (a ⊆ b) && (b ⊆ a) && !issetequal(c, d) && (c ⊆ d) && (d ⊆ c)
    println("REPRODUCED iddicts-idset-issetequal")
end
