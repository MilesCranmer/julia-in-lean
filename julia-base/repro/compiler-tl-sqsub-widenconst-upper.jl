# A PartialTypeVar is only ⊑ TypeVar itself: it is not ⊑ Union{Nothing, TypeVar} on the inference
# lattice, nor ⊑ Any on the optimizer lattice, although widenconst(PartialTypeVar) = TypeVar is a
# subtype of both (Compiler/src/typelattice.jl:553-554).
const CC = Base.Compiler
id = "compiler-tl-sqsub-widenconst-upper"
L = CC.typeinf_lattice(CC.NativeInterpreter())
OL = CC.optimizer_lattice(CC.NativeInterpreter())
p = CC.PartialTypeVar(TypeVar(:T), true, true)
w = CC.widenconst(p)
r1 = CC.:⊑(L, p, w)
r2 = CC.:⊑(L, w, Union{Nothing, TypeVar})
r3 = CC.:⊑(L, p, Union{Nothing, TypeVar})
r4 = CC.:⊑(OL, p, Any)
println("widenconst(PartialTypeVar(T)) = ", w)
println("typeinf: PartialTypeVar ⊑ TypeVar = ", r1, ", TypeVar ⊑ Union{Nothing, TypeVar} = ", r2,
        ", PartialTypeVar ⊑ Union{Nothing, TypeVar} = ", r3)
println("optimizer: PartialTypeVar ⊑ Any = ", r4)
println(r1 && r2 && !r3 && !r4 ? "REPRODUCED $id" : "NOT REPRODUCED $id")
