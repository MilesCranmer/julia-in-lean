import JuliaLean.Proofs.base.abstractarray.cartesian_contracts

namespace JuliaLean.Multidim

/-- `vcat(1, [2 3])`: the shape is `(2, 2)` and the scalar is broadcast into the first row. -/
theorem cat_scalar_row : cat [1] [.scalar, .array [1, 2]] = .ok [2, 2] := by
  decide

theorem catShapeChecked_refuted : ¬ CatShapeChecked := by
  intro h
  have := h [1] [.scalar, .array [1, 2]]
  rw [cat_scalar_row] at this
  have := this .scalar (by simp) 1 (by decide) (by decide)
  exact absurd this (by decide)

/-- `hvcat((2, 1), 1, 2, 3)`: `ArgumentError` for one number type, `DimensionMismatch`
for mixed types. -/
theorem hvcat_rows_2_1 :
    hvcatSame [2, 1] 3 = .error .argumentError ∧ hvcatTyped [2, 1] 3 = .error .dimensionMismatch := by
  decide

theorem hvcatNumbersAgree_refuted : ¬ HvcatNumbersAgree := by
  intro h
  have := h [2, 1] 3
  rw [hvcat_rows_2_1.1, hvcat_rows_2_1.2] at this
  exact absurd this (by decide)

/-- `hvcat(0, 1)` throws `DivideError` from `mod(1, 0)`. -/
theorem hvcat_zero_cols : hvcatCols (i64 0) 1 = .error .divideError := by
  decide

theorem hvcatColumnsError_refuted : ¬ HvcatColumnsError := by
  intro h
  have := h (i64 0) 1 (by decide) (by decide) (by decide)
  rw [hvcat_zero_cols] at this
  exact absurd this (by decide)

end JuliaLean.Multidim
