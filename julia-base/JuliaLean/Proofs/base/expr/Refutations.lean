import JuliaLean.Proofs.base.expr.Claims

namespace JuliaLean.ExprReflect

open JuliaLean

def copyAliasWitness : CopyVal :=
  .expr 1 "tuple" (.args
    (.quoteNode (.expr 0 "call" (.args (.atom "f") (.args (.atom "x") .nil))))
    .nil)

theorem copyIndependent_refuted : ¬ CopyIndependent := by
  unfold CopyIndependent
  intro h
  have shared := h copyAliasWitness 2 (by decide +kernel)
  revert shared
  decide +kernel

end JuliaLean.ExprReflect
