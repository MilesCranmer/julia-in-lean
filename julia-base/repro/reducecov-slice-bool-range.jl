# Indexing a Base.Slice with a Bool unit range returns the Bool range itself
# instead of performing logical indexing. getindex(S::Slice, i::AbstractUnitRange{<:Integer})
# (base/indices.jl:351) also matches AbstractUnitRange{Bool} because Bool <: Integer.
s = Base.Slice(Base.OneTo(2))
r = s[false:true]
expected = collect(s)[false:true]
println("Base.Slice(Base.OneTo(2))[false:true] = ", repr(r))
println("collect(Base.Slice(Base.OneTo(2)))[false:true] = ", repr(expected))
println("Base.IdentityUnitRange(Base.OneTo(2))[false:true] = ", repr(Base.IdentityUnitRange(Base.OneTo(2))[false:true]))
# The Slice produced by to_indices for a colon behaves the same way.
t = to_indices([10, 20], (:,))[1]
println("to_indices([10, 20], (:,))[1][false:true] = ", repr(t[false:true]))
if collect(r) != expected
    println("REPRODUCED reducecov-slice-bool-range")
end
