import JuliaLean.Proofs.base.Enums.Claims

namespace JuliaLean.ExprReflect

open JuliaLean

theorem enumAssignsDocumentedValues_proven : EnumAssignsDocumentedValues := by
  unfold EnumAssignsDocumentedValues
  intro value hlo hhi
  have hle : value ≤ 127 := by omega
  have hne : value ≠ 127 := by omega
  have hsucc : value + 1 ≠ value := by omega
  have horder : value ≤ value + 1 := by omega
  have hnotlo : value + 1 ≠ -128 := by omega
  simp [enumBuild, enumLoop, enumStep, enumFinish, enumConvert, enumNext, int8Bounds,
    hlo, hle, hne, hsucc, hnotlo, Int.max_def, horder]

theorem enumRejectsDuplicateValues_proven : EnumRejectsDuplicateValues := by
  unfold EnumRejectsDuplicateValues
  intro value hlo hhi
  simp [enumBuild, enumLoop, enumStep, enumFinish, enumConvert, enumNext, int8Bounds,
    hlo, hhi]

theorem enumRejectsDuplicateNames_proven : EnumRejectsDuplicateNames := by
  unfold EnumRejectsDuplicateNames
  intro first second hflo hfhi hslo hshi hne
  simp [enumBuild, enumLoop, enumStep, enumFinish, enumConvert, enumNext, int8Bounds,
    hflo, hfhi, hslo, hshi, Ne.symm hne]

theorem enumRejectsOutOfRange_proven : EnumRejectsOutOfRange := by
  unfold EnumRejectsOutOfRange
  intro value hout
  rcases hout with hlo | hhi
  · have hnot : ¬ -128 ≤ value := by omega
    simp [enumBuild, enumLoop, enumStep, enumConvert, int8Bounds, hnot]
  · have hnot : ¬ value ≤ 127 := by omega
    simp [enumBuild, enumLoop, enumStep, enumConvert, int8Bounds, hnot]

theorem enumRejectsOverflow_proven : EnumRejectsOverflow := by
  unfold EnumRejectsOverflow
  intro first second hne
  simp [enumBuild, enumLoop, enumStep, enumFinish, enumConvert, enumNext, int8Bounds]

theorem enumInstancesOrder_proven : EnumInstancesOrder := by
  unfold EnumInstancesOrder
  intro first second third hflo hfhi hslo hshi htlo hthi hfs hft hst
  simp [enumBuild, enumLoop, enumStep, enumFinish, enumConvert, enumNext, int8Bounds,
    hflo, hfhi, hslo, hshi, htlo, hthi,
    Ne.symm hfs, Ne.symm hft, Ne.symm hst]

end JuliaLean.ExprReflect
