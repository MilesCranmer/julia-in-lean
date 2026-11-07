import JuliaLean.base.range

namespace JuliaLean.Multidim

/-- A range that Julia can construct: nonzero step and every element representable. -/
def Rng.WF (r : Rng) : Prop :=
  r.step.val ≠ 0 ∧ ∀ j : Nat, j < r.len → IntTy.min .i64 ≤ r.elem j ∧ r.elem j ≤ IntTy.max .i64

instance (r : Rng) : Decidable r.WF := by
  unfold Rng.WF; exact inferInstance

end JuliaLean.Multidim
