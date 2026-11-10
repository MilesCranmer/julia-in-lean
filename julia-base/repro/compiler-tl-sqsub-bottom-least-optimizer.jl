# On the optimizer lattice (PartialsLattice(ConstsLattice())), Union{} is not ⊑ a Const or a
# PartialStruct: the Union{} fast path exists only in the conditional layers
# (Compiler/src/typelattice.jl:424-428), which this lattice does not have.
const CC = Base.Compiler
id = "compiler-tl-sqsub-bottom-least-optimizer"
OL = CC.optimizer_lattice(CC.NativeInterpreter())
L = CC.typeinf_lattice(CC.NativeInterpreter())
ps = Core.PartialStruct(CC.fallback_lattice, Tuple{Int,Int}, Any[Core.Const(1), Int])
r1 = CC.:⊑(OL, Union{}, Core.Const(1))
r2 = CC.:⊑(OL, Union{}, ps)
r3 = CC.:⊑(L, Union{}, Core.Const(1))
println("optimizer: Union{} ⊑ Const(1) = ", r1, ", Union{} ⊑ PartialStruct = ", r2)
println("typeinf:   Union{} ⊑ Const(1) = ", r3)
println(!r1 && !r2 && r3 ? "REPRODUCED $id" : "NOT REPRODUCED $id")
