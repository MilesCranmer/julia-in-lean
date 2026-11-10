# Scratch probes for typelattice properties (not part of the difftest).
const CC = Base.Compiler
const L = CC.typeinf_lattice(CC.NativeInterpreter())
const OL = CC.optimizer_lattice(CC.NativeInterpreter())
⊑ = CC.:⊑
ptv = CC.PartialTypeVar(TypeVar(:T), true, true)
println("PTV ⊑ TypeVar: ", ⊑(L, ptv, TypeVar))
println("PTV ⊑ Union{TypeVar,Nothing}: ", ⊑(L, ptv, Union{TypeVar,Nothing}))
println("PTV ⊑ Any (opt): ", ⊑(OL, ptv, Any))
println("tmerge(PTV, Nothing): ", CC.tmerge(L, ptv, Nothing))
c1 = CC.Conditional(1, 0, Any, Union{})
c2 = CC.Conditional(1, 0, Any, Int)
println("Const(true) ⊑ c1: ", ⊑(L, Core.Const(true), c1), "  c1 ⊑ c2: ", ⊑(L, c1, c2),
        "  Const(true) ⊑ c2: ", ⊑(L, Core.Const(true), c2))

function loopy(n)
    x = nothing
    for i in 1:n
        x = Core._typevar(:T, Union{}, Any)
    end
    return x
end
t = @elapsed rt = Base.return_types(loopy, (Int,))
println("loopy: ", rt, " in ", t, " s")
flush(stdout)
v = Vector{TypeVar(:T, Integer)}
println("free Const: ", CC.has_free_typevars(v), " ", CC.widenconst(Core.Const(v)), " isa=", isa(v, CC.widenconst(Core.Const(v))))
w = Vector{T} where T<:Integer
println("closed Const: ", CC.widenconst(Core.Const(w)), " isa=", isa(w, CC.widenconst(Core.Const(w))), " ⊑=", ⊑(L, Core.Const(w), CC.widenconst(Core.Const(w))))
println("opt: Union{} ⊑ Const(1): ", ⊑(OL, Union{}, Core.Const(1)), "  typeinf: ", ⊑(L, Union{}, Core.Const(1)))
ps = Core.PartialStruct(CC.fallback_lattice, Tuple{Int,Int}, Any[Core.Const(1), Int])
println("opt: Union{} ⊑ PartialStruct: ", ⊑(OL, Union{}, ps), " is_lattice_equal(opt, Union{}, Union{}) ", CC.is_lattice_equal(OL, Union{}, Union{}))
println("opt: tmeet(ps, Tuple{Int,Symbol}) = ", CC.tmeet(OL, ps, Tuple{Int,Symbol}))
println("is_valid_lattice(typeinf, Int) = ", CC.is_valid_lattice(L, Int), "  (Consts, Const(1)) = ", CC.is_valid_lattice(CC.ConstsLattice(), Core.Const(1)))
