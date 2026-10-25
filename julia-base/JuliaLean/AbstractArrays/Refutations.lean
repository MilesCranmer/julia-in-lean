import JuliaLean.AbstractArrays.Props

namespace JuliaLean.AbstractArrays

/-- `Bool(true)` has numeric value one, so `checkindex` accepts it on `1:3`,
while `to_index(::Bool)` throws `ArgumentError`. -/
theorem checkboundsAgreesGetindex_refuted : ¬ CheckboundsAgreesGetindex := by
  intro h
  have bad := (h (Axis.oneTo 3) (.unsupportedReal (i64 1))).mp (by decide)
  rcases bad with ⟨j, hj, _⟩
  simp [ScalarIndex.toIndex] at hj

/-- `UInt(2)^63` is beyond every practical `ndims`, but converting it to
`Int64` throws before `size` can return the trailing singleton size. -/
theorem sizeAllIntegerDims_refuted : ¬ SizeAllIntegerDims := by
  intro h
  have bad := h [] .u64 (JInt.lit .u64 (2^63)) (by decide)
  revert bad
  decide

/-- `typemax(UInt64)` is not one, but the vector fast path throws while
converting it to `Int64`, before the documented ArgumentError. -/
theorem requireOneBasedAllIntegerAxes_refuted : ¬ RequireOneBasedAllIntegerAxes := by
  intro h
  obtain ⟨m, bad⟩ := h .u64 (JInt.typemax .u64) (by decide)
  have actual : requireOneBasedInteger (JInt.typemax .u64) =
      .error (.inexactError "Int64") := by decide
  rw [actual] at bad
  cases bad

end JuliaLean.AbstractArrays
