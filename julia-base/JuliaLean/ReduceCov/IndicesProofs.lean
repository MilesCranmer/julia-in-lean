import JuliaLean.ReduceCov.Indices

namespace JuliaLean.ReduceCov.Indices

theorem sliceIntegerIndex_refuted : ¬ SliceIntegerIndex := by
  intro h
  have counterexample := h (.unit (i64 3) (i64 5)) .i8 (JInt.lit .i8 3)
  revert counterexample
  decide

theorem sliceBoolMask_refuted : ¬ SliceBoolMask := by
  intro h
  have counterexample := h (.oneTo (i64 2)) (.brange false true) rfl
  revert counterexample
  decide

theorem identityBoolStep_refuted : ¬ IdentityBoolStep := by
  intro h
  have counterexample := h (.unit (i64 1) (i64 2)) true (i64 (-1)) false (by decide)
  revert counterexample
  decide

theorem slicePromoteRule_refuted : ¬ SlicePromoteRule := by
  intro h
  have counterexample := (h .oneTo .unitRange).1
  revert counterexample
  decide

theorem linearIndicesRangeIndex_refuted : ¬ LinearIndicesRangeIndex := by
  intro h
  have counterexample := h ⟨[.unit (i64 3) (i64 5)]⟩ (.unit (i64 2) (i64 3)) (by decide)
  revert counterexample
  decide

theorem linearIndicesAxes_refuted : ¬ LinearIndicesAxes := by
  intro h
  have counterexample := h [.range (.ident (.unit (i64 3) (i64 5))), .int (i64 2)] (by decide)
  revert counterexample
  decide

theorem promoteShapeMessage_refuted : ¬ PromoteShapeMessage := by
  intro h
  apply h [.oneTo (i64 3)] [.unit (i64 2) (i64 4)] "(1:3,)" 1
  decide

end JuliaLean.ReduceCov.Indices
