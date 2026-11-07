import JuliaLean.Proofs.base.runtime_internals.Common

namespace JuliaLean.MemSafety.G4

/-- The lookup implementation is exactly `table[i+1]`; its docstring states no
index restriction, `base/ryu/utils.jl:286-325`. -/
def ryuLookupIndex (_tableLen : Nat) (i : Int) : Int := i + 1

def RyuLookupInBounds : Prop :=
  ∀ (tableLen : Nat) (i : Int), 0 < tableLen → InBounds tableLen (ryuLookupIndex tableLen i)


theorem ryuLookupInBounds_refuted : ¬ RyuLookupInBounds := by
  intro h
  have hz := h 1 (-1) (by omega)
  unfold ryuLookupIndex InBounds at hz
  omega

end JuliaLean.MemSafety.G4
