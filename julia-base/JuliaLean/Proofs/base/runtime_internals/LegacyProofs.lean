import JuliaLean.Proofs.base.runtime_internals.Claims

namespace JuliaLean.ExprReflect

open JuliaLean

theorem fieldNamesCount_proven : FieldNamesCount := by
  unfold FieldNamesCount
  intro layout names count hnames hcount
  cases hdef : layout.definite <;>
    simp [fieldNames, fieldCount, hdef] at hnames hcount
  simp_all

theorem fieldOffsetInBounds_proven : FieldOffsetInBounds := by
  unfold FieldOffsetInBounds
  intro layout index offset hoffset
  by_cases hconvert : index < -2147483648 ∨ 2147483647 < index
  · simp [fieldOffset, hconvert] at hoffset
  · by_cases hdef : layout.definite
    · by_cases hbad : index < 1 ∨ (layout.names.length : Int) < index
      · simp [fieldOffset, hconvert, hdef, hbad] at hoffset
      · omega
    · simp [fieldOffset, hconvert, hdef] at hoffset

theorem methodFiltering_proven : MethodFiltering := by
  unfold MethodFiltering
  intro table modules method h
  have filtered := (List.mem_filter.mp h).2
  simpa using filtered

end JuliaLean.ExprReflect
