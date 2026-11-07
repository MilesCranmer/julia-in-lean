import JuliaLean.base.essentials
import JuliaLean.base.abstractarray
import JuliaLean.Proofs.base.range.cartesian_components

namespace JuliaLean.Multidim

/-- `isempty(R)` for a `CartesianIndices` holds exactly when one of its ranges is empty
(`isempty` docstring: "Determine whether a collection is empty (has no elements)"). -/
def CartesianIsEmpty : Prop :=
  ∀ R : List Rng, (∀ r ∈ R, r.WF) → (ciIsEmpty ciLength R = true ↔ ∃ r ∈ R, r.len = 0)

/-- `CartesianIndices((2^32, 2^32))` has `length` 0 (`2^64` wraps) and so `isempty` is true. -/
theorem cartesian_length_wraps :
    ciIsEmpty ciLength [unitRng 1 (2 ^ 32), unitRng 1 (2 ^ 32)] = true ∧
      (ciLength [unitRng 1 (2 ^ 63 - 1), unitRng 1 2]).val = -2 := by
  decide

/-- `1:hi` is a well-formed range for `0 ≤ hi < 2^62`. -/
theorem unitRng_one_wf (hi : Int) (h0 : 0 ≤ hi) (hn : hi < 2 ^ 62) : (unitRng 1 hi).WF := by
  have h1 : (i64 1).val = 1 := by decide
  have hmin : IntTy.min .i64 = -(2 ^ 63) := by decide
  have hmax : IntTy.max .i64 = 2 ^ 63 - 1 := by decide
  refine ⟨show (i64 1).val ≠ 0 by rw [h1]; decide, ?_⟩
  intro j hj
  change j < (hi - 1 + 1).toNat at hj
  have hlen : (((hi - 1 + 1).toNat : Nat) : Int) = hi - 1 + 1 := Int.toNat_of_nonneg (by omega)
  have hj' : ((j : Nat) : Int) < (((hi - 1 + 1).toNat : Nat) : Int) := by exact_mod_cast hj
  show IntTy.min .i64 ≤ (i64 1).val + (j : Int) * (i64 1).val ∧
    (i64 1).val + (j : Int) * (i64 1).val ≤ IntTy.max .i64
  rw [h1, hmin, hmax]
  constructor <;> omega

theorem cartesianIsEmpty_refuted : ¬ CartesianIsEmpty := by
  intro h
  have hwf : ∀ r ∈ [unitRng 1 (2 ^ 32), unitRng 1 (2 ^ 32)], r.WF := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hr
    subst hr
    exact unitRng_one_wf _ (by decide) (by decide)
  have := (h [unitRng 1 (2 ^ 32), unitRng 1 (2 ^ 32)] hwf).1 cartesian_length_wraps.1
  revert this
  decide

end JuliaLean.Multidim
