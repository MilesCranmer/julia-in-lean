# subtype_tfunc returns Const(false) for `a <: b` when the type `a` stands for does not
# intersect `b`, or when instanceof_tfunc calls it exact. But `Union{}` is an instance of
# `Type{<:Integer}` and of `Union{Type{Int}, Core.TypeofBottom}`, and `Union{} <: b` is true
# for every `b`.
id = "compiler-tfuncs-subtype-bottom-lhs"
struct S
    t::Type{<:Integer}
end
h(s::S) = s.t <: String
r = h(S(Union{}))
println("Union{} isa Type{<:Integer} = ", Union{} isa Type{<:Integer}, "; Union{} <: String = ", Union{} <: String)
println("code_typed(h, (S,)) = ", only(code_typed(h, (S,)))[1].code)
println("h(S(Union{})) = ", r)
# The same through instanceof_tfunc's Union rule, which drops a Union{} member and keeps the
# other member's `isexact`.
struct S2
    t::Union{Type{Int}, Core.TypeofBottom}
end
h2(s::S2) = s.t <: String
r2 = h2(S2(Union{}))
println("code_typed(h2, (S2,)) = ", only(code_typed(h2, (S2,)))[1].code)
println("h2(S2(Union{})) = ", r2)
println(r === false && r2 === false && (Base.inferencebarrier(Union{}) <: String) ?
        "REPRODUCED $id" : "NOT REPRODUCED $id")
