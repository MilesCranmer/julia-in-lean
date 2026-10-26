# promote_rule(Slice{T1}, Slice{T2}) and promote_rule(IdentityUnitRange{T1},
# IdentityUnitRange{T2}) (base/indices.jl:499-502) call el_same(promote_type(T1, T2), a, b).
# el_same expects an element type, but T1 and T2 are range types while the element
# type of every Slice is Int, so el_same always falls back to typejoin. The promoted
# type is the UnionAll Base.Slice; the LinearIndices rule promotes the wrapped ranges.
p = promote_type(Base.Slice{Base.OneTo{Int}}, Base.Slice{UnitRange{Int}})
q = promote_type(Base.IdentityUnitRange{Base.OneTo{Int}}, Base.IdentityUnitRange{UnitRange{Int}})
l = promote_type(LinearIndices{1,Tuple{Base.OneTo{Int}}}, LinearIndices{1,Tuple{UnitRange{Int}}})
v = [Base.Slice(Base.OneTo(2)), Base.Slice(1:2)]
println("promote_type(Slice{OneTo{Int}}, Slice{UnitRange{Int}}) = ", p)
println("promote_type(IdentityUnitRange{OneTo{Int}}, IdentityUnitRange{UnitRange{Int}}) = ", q)
println("promote_type(LinearIndices{1,Tuple{OneTo{Int}}}, LinearIndices{1,Tuple{UnitRange{Int}}}) = ", l)
println("typeof([Base.Slice(Base.OneTo(2)), Base.Slice(1:2)]) = ", typeof(v))
if !isconcretetype(p) && !isconcretetype(q) && isconcretetype(l)
    println("REPRODUCED reducecov-slice-promote-rule")
end
