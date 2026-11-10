# On the optimizer lattice, Any is not the top element: a PartialTypeVar is not ⊑ Any.
# The optimizer lattice has no conditional layer, so the `b === Any` fast path
# (Compiler/src/typelattice.jl:422) never runs, and ⊑(::ConstsLattice) accepts a PartialTypeVar
# only below TypeVar itself (Compiler/src/typelattice.jl:561-562).
# A PartialTypeVar reaches IR statement types from `typevar_tfunc` (Compiler/src/tfuncs.jl:709).
const CC = Base.Compiler
id = "compiler-tl-sqsub-any-top-optimizer"
OL = CC.optimizer_lattice(CC.NativeInterpreter())
p = CC.PartialTypeVar(TypeVar(:T), true, true)
r1 = CC.:⊑(OL, CC.widenconst(p), Any)
r2 = CC.:⊑(OL, p, Any)
println("optimizer: TypeVar ⊑ Any = ", r1, ", PartialTypeVar ⊑ Any = ", r2)
println(r1 && !r2 ? "REPRODUCED $id" : "NOT REPRODUCED $id")
