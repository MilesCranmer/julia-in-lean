import JuliaLean.Proofs.base.abstractarraymath.cartesian_contracts

namespace JuliaLean.Multidim

/-- `selectdim([1 2; 3 4], 1, CartesianIndex(2, 2))` is the view
`view(B, CartesianIndex(2, 2), Slice(OneTo(2)))`, whose second element is `B[2, 2, 2]`. -/
theorem selectdim_cart_idxs :
    selectdim [2, 2] 1 (.cart [2, 2]) = .ok [.cart [2, 2], .slice 2] := by
  decide

theorem selectdimInBounds_refuted : ¬ SelectdimInBounds := by
  intro h
  have := h [2, 2] 1 (.cart [2, 2]) (by decide) (by intro n; simp)
  rw [selectdim_cart_idxs] at this
  exact absurd this (by decide)

/-- `selectdim([1 2 3; 4 5 6], 3, 1:1)` throws `BoundsError`; `view(A, :, :, 1:1)` is 2×3×1. -/
theorem selectdim_trailing_range :
    (selectdim [2, 3] ((3 : Nat) : Int) (.urange 1 1) >>= view [2, 3]) = .error .boundsError ∧
      view [2, 3] [.colon, .colon, .urange 1 1] = .ok [2, 3, 1] := by
  decide

theorem selectdimViewAgrees_refuted : ¬ SelectdimViewAgrees := by
  intro h
  have := h [2, 3] 3 (.urange 1 1) (by decide) (by decide) (by intro n; simp)
  rw [selectdim_trailing_range.1] at this
  exact absurd this (by decide)

end JuliaLean.Multidim
