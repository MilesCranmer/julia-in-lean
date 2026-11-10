# ⊑ on the inference lattice is not transitive:
# Const(true) ⊑ Conditional(x, Any, Union{}) ⊑ Conditional(x, Any, Int), but
# Const(true) ⋢ Conditional(x, Any, Int). Compiler/src/typelattice.jl:433-441 requires the
# elsetype of `b` to be Union{}, although a `Const(true)` never takes the else branch.
const CC = Base.Compiler
# Julia 1.13 has no `ssadef` field: `Conditional(slot, thentype, elsetype)`.
mkcond(slot, t, e) = hasfield(CC.Conditional, :ssadef) ? CC.Conditional(slot, 0, t, e) : CC.Conditional(slot, t, e)
id = "compiler-tl-sqsub-transitive"
L = CC.typeinf_lattice(CC.NativeInterpreter())
a = Core.Const(true)
b = mkcond(1, Any, Union{})
c = mkcond(1, Any, Int)
ab = CC.:⊑(L, a, b); bc = CC.:⊑(L, b, c); ac = CC.:⊑(L, a, c)
println("Const(true) ⊑ Conditional(1, 0, Any, Union{}) = ", ab)
println("Conditional(1, 0, Any, Union{}) ⊑ Conditional(1, 0, Any, Int) = ", bc)
println("Const(true) ⊑ Conditional(1, 0, Any, Int) = ", ac)
println(ab && bc && !ac ? "REPRODUCED $id" : "NOT REPRODUCED $id")
