import JuliaLean.base.Enums
import JuliaLean.Proofs.base.Enums.LegacyProofs

namespace JuliaLean.ExprReflect

open JuliaLean

def EnumRuntimeBodies : Prop := ∀ definition value,
  enumContains definition value = definition.instances.contains value ∧
  (enumBroadcast value).length = 1 ∧
  enumIsless value value = false ∧
  enumName definition value =
    ((definition.names.find? (·.1 == value)).map (·.2)).getD ("<invalid #" ++ toString value ++ ">") ∧
  enumWriteRead value = value ∧
  (∀ hashType hashValue typeHash seed,
    enumHashModel hashType hashValue typeHash value seed =
      hashType typeHash (hashValue value seed))

theorem enumRuntimeBodies_proven : EnumRuntimeBodies := by
  intro definition value
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · simp [enumIsless]
  constructor
  · rfl
  constructor
  · rfl
  · intros; rfl

def EnumMacroBodies : Prop :=
  (∀ value, membershipStrategy [value] = .interval) ∧
  EnumAssignsDocumentedValues ∧ EnumRejectsDuplicateValues ∧
  EnumRejectsDuplicateNames ∧ EnumRejectsOutOfRange ∧ EnumRejectsOverflow

theorem enumMacroBodies_proven : EnumMacroBodies := by
  constructor
  · intro value; rfl
  exact ⟨enumAssignsDocumentedValues_proven, enumRejectsDuplicateValues_proven,
    enumRejectsDuplicateNames_proven, enumRejectsOutOfRange_proven,
    enumRejectsOverflow_proven⟩

end JuliaLean.ExprReflect
