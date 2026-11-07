import JuliaLean.Proofs.base.runtime_internals.Common

namespace JuliaLean.MemSafety.G4

/-- The bootstrap array getter's unsigned comparison before `memoryrefnew`,
`base/boot.jl:879-883`. -/
def bootArrayIndex (len : Nat) (i : Int) : Option Int :=
  if 0 ≤ i - 1 ∧ i - 1 < len then some i else none

def BootArrayRefInBounds : Prop :=
  ∀ (len : Nat) (i j : Int), bootArrayIndex len i = some j → InBounds len j


theorem bootArrayRefInBounds : BootArrayRefInBounds := by
  intro len i j h
  unfold bootArrayIndex at h
  split at h
  · simp only [Option.some.injEq] at h
    subst j
    unfold InBounds
    omega
  · contradiction

end JuliaLean.MemSafety.G4
