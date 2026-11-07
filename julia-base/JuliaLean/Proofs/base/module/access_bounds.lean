import JuliaLean.Proofs.base.abstractarray.common.input_invariants

namespace JuliaLean.MemSafety.G3

open JuliaLean

/-- A Symbol points to at least its terminating byte,
`base/module.jl:67-75`. -/
def ModuleSymbolSafe : Prop :=
  ∀ storageLength : Nat, 1 ≤ storageLength → inOneBased storageLength 1

theorem moduleSymbolSafe_proven : ModuleSymbolSafe := by
  intro storageLength h
  exact ⟨by omega, h⟩

end JuliaLean.MemSafety.G3
