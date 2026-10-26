import JuliaLean.ExprReflect.Props

namespace JuliaLean.ExprReflect

open JuliaLean

theorem copyEqual_proven : CopyEqual := by
  unfold CopyEqual
  intro value fresh
  induction value with
  | nil => rfl
  | atom => rfl
  | args first rest ihFirst ihRest => simp [copyExprs, eraseCopyIds, ihFirst, ihRest]
  | quoteNode => rfl
  | expr id head args ih => simp [copyExprs, eraseCopyIds, ih]

theorem isExprContract_proven : IsExprContract := by
  unfold IsExprContract
  intros
  rfl

theorem quotContract_proven : QuotContract := by
  unfold QuotContract
  intro
  rfl

theorem showSexprContract_proven : ShowSexprContract := by
  unfold ShowSexprContract
  intros
  simp [toSExpr]

theorem inlineContract_proven : InlineContract := by
  unfold InlineContract
  intro
  rfl

theorem generatedContract_proven : GeneratedContract := by
  unfold GeneratedContract
  intros
  rfl

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

theorem whichHasMethod_proven : WhichHasMethod := by
  unfold WhichHasMethod
  intro table modules method h
  cases filtered : methods table modules with
  | nil => simp [whichMethod, filtered] at h
  | cons first rest => simp [hasMethod, filtered]

theorem nameofContract_proven : NameofContract := by
  unfold NameofContract
  intro
  rfl

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

theorem nrefExact_proven : NrefExact := by
  unfold NrefExact
  intros
  rfl

theorem ntupleExact_proven : NtupleExact := by
  unfold NtupleExact
  intros
  rfl

theorem cartesianLoopsCompoundExact_proven : CartesianLoopsCompoundExact := by
  unfold CartesianLoopsCompoundExact
  intros
  rfl

end JuliaLean.ExprReflect
