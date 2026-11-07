import JuliaLean.base.Enums

namespace JuliaLean.ExprReflect

open JuliaLean

def EnumAssignsDocumentedValues : Prop := ∀ value,
  -128 ≤ value → value < 127 →
  enumBuild int8Bounds [⟨"first", some value⟩, ⟨"second", none⟩] = .ok {
    names := ["first", "second"]
    instances := [value, value + 1]
    typeminValue := value
    typemaxValue := value + 1 }

def EnumRejectsDuplicateValues : Prop := ∀ value,
  -128 ≤ value → value ≤ 127 →
  enumBuild int8Bounds [⟨"first", some value⟩, ⟨"second", some value⟩] =
    .error (.argumentError "values must be unique")

def EnumRejectsDuplicateNames : Prop := ∀ first second,
  -128 ≤ first → first ≤ 127 → -128 ≤ second → second ≤ 127 → first ≠ second →
  enumBuild int8Bounds [⟨"same", some first⟩, ⟨"same", some second⟩] =
    .error (.argumentError "name is not unique")

def EnumRejectsOutOfRange : Prop := ∀ value,
  (value < -128 ∨ 127 < value) →
  enumBuild int8Bounds [⟨"value", some value⟩] = .error (.inexactError "@enum")

def EnumRejectsOverflow : Prop := ∀ first second,
  first ≠ second →
  enumBuild int8Bounds [⟨first, some 127⟩, ⟨second, none⟩] =
    .error (.argumentError "overflow in value")

def EnumInstancesOrder : Prop := ∀ first second third,
  -128 ≤ first → first ≤ 127 → -128 ≤ second → second ≤ 127 →
  -128 ≤ third → third ≤ 127 →
  first ≠ second → first ≠ third → second ≠ third →
  enumBuild int8Bounds [
    ⟨"first", some first⟩, ⟨"second", some second⟩, ⟨"third", some third⟩] = .ok {
      names := ["first", "second", "third"]
      instances := [first, second, third]
      typeminValue := first
      typemaxValue := max first (max second third) }

def EnumExtremaCorrect : Prop := ∀ bounds members result,
  enumBuild bounds members = .ok result →
  enumMinimum? result.instances = some result.typeminValue ∧
  enumMaximum? result.instances = some result.typemaxValue

end JuliaLean.ExprReflect
