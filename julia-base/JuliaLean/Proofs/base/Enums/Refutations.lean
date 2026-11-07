import JuliaLean.Proofs.base.Enums.Claims

namespace JuliaLean.ExprReflect

open JuliaLean

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

end JuliaLean.ExprReflect
