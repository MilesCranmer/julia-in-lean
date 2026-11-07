import JuliaLean.base.subarray

/-!
`view(view(M, r, c), :)` for a matrix `M`, an `IdentityUnitRange` row index `r` and a scalar column
`c` (`base/subarray.jl`, `base/indices.jl`, master). Values are exact integers: every quantity below
is a small in-range `Int`.
-/

namespace JuliaLean.ReinterpretArrays


/-- For every in-bounds `IdentityUnitRange(lo:hi)` row range, column `c` and `i ∈ lo:hi`,
`view(view(M, IdentityUnitRange(lo:hi), c), :)[i]` reads `M[i, c]` (linear index `i + (c-1)*s1`),
the same element as `view(M, IdentityUnitRange(lo:hi), c)[i]`. -/
def NestedColonViewCorrect : Prop :=
  ∀ (s1 s2 lo hi c i : Int), 1 ≤ lo → lo ≤ hi → hi ≤ s1 → 1 ≤ c → c ≤ s2 → lo ≤ i → i ≤ hi →
    nestedColonParentIndex s1 lo hi c i = i + (c - 1) * s1

/-- The single view reads the right element: `view(M, IdentityUnitRange(lo:hi), c)[i]` is `M[i, c]`. -/
theorem single_view_correct (s1 lo c i : Int) : offset1 s1 (.iur lo lo) c + 1 * i = i + (c - 1) * s1 := by
  simp only [offset1, RowIndex.lo]; omega

/-- `view(view(M, IdentityUnitRange(2:3), 2), :)[2]` for a `4 × 5` matrix reads `M[3, 2]`. -/
theorem nestedColonViewCorrect_refuted : ¬ NestedColonViewCorrect := by
  intro h
  have e := h 4 5 2 3 2 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  revert e
  decide

end JuliaLean.ReinterpretArrays
