import JuliaLean.ExprReflect.Props

namespace JuliaLean.ExprReflect

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

def enumExtremaWitness : EnumResult := {
  names := ["high", "low", "top"]
  instances := [5, -2, 9]
  typeminValue := 5
  typemaxValue := 9 }

theorem enumExtremaCorrect_refuted : ¬ EnumExtremaCorrect := by
  unfold EnumExtremaCorrect
  intro h
  have wrong := h int8Bounds [
    ⟨"high", some 5⟩, ⟨"low", some (-2)⟩, ⟨"top", some 9⟩]
    enumExtremaWitness (by rfl)
  revert wrong
  decide +kernel

theorem cartesianLoopsTotal_refuted : ¬ CartesianLoopsTotal := by
  unfold CartesianLoopsTotal
  intro h
  have wrong := h 2 "i" "A" (.atom "body")
  simp [nloops, isCompound] at wrong

end JuliaLean.ExprReflect
