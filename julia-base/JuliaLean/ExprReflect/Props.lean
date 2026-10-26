import JuliaLean.ExprReflect.Model

namespace JuliaLean.ExprReflect

open JuliaLean

/-! ### Expressions and annotation macros -/

def CopyEqual : Prop := ∀ value fresh,
  eraseCopyIds (copyExprs fresh value) = eraseCopyIds value

def CopyIndependent : Prop := ∀ value fresh,
  allIdsBelow value fresh = true →
  idsDisjoint (copyIds value) (copyIds (copyExprs fresh value)) = true

def IsExprContract : Prop := ∀ head args heads arity,
  isExpr (.expr head args) heads arity =
    (heads.contains head && arity.all (args.length == ·))

def QuotContract : Prop := ∀ ex, quot ex = .expr "quote" [ex]

def ShowSexprContract : Prop := ∀ head args,
  toSExpr (.expr head args) = .form head (args.map toSExpr)

def InlineContract : Prop := ∀ ex,
  annotateInline false ex = .expr "block" [
    .expr "inline" [.atom "true"],
    .expr "local" [.expr "=" [.atom "val", .expr "escape" [ex]]],
    .expr "inline" [.atom "false"],
    .atom "val"]

def GeneratedContract : Prop := ∀ signature body,
  annotateGenerated true signature body =
    .ok (.expr "escape" [.expr "function" [signature,
      .expr "if" [.expr "generated" [], body,
        .expr "block" [.expr "meta" [.atom "generated_only"],
          .expr "return" [.atom "nothing"]]]]])

/-! ### Reflection -/

def FieldNamesCount : Prop := ∀ layout names count,
  fieldNames layout = .ok names → fieldCount layout = .ok count →
  names.length = count

def FieldOffsetInBounds : Prop := ∀ layout index offset,
  fieldOffset layout index = .ok offset →
  1 ≤ index ∧ index ≤ (layout.names.length : Int)

def MethodFiltering : Prop := ∀ table modules method,
  method ∈ methods table modules →
  method.signatureMatches = true ∧ modules.all (·.contains method.moduleName) = true

def WhichHasMethod : Prop := ∀ table modules method,
  whichMethod table modules = some method → hasMethod table modules = true

def NameofContract : Prop := ∀ functionName, nameOf functionName = functionName

/-! ### Enums -/

def int8Bounds : EnumBounds := ⟨-128, 127⟩

def enumMinimum? : List Int → Option Int
  | [] => none
  | value :: rest => some (rest.foldl min value)

def enumMaximum? : List Int → Option Int
  | [] => none
  | value :: rest => some (rest.foldl max value)

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

/-! ### Cartesian macros -/

def NrefExact : Prop := ∀ dimensions array stem,
  nref dimensions array stem = .expr "escape" [.expr "ref" (.atom array ::
    (List.range dimensions).map fun index => .atom (indexedName stem (index + 1)))]

def NtupleExact : Prop := ∀ dimensions stem,
  ntuple dimensions stem = .expr "escape" [.expr "tuple"
    ((List.range dimensions).map fun index => .atom (indexedName stem (index + 1)))]

def CartesianLoopsTotal : Prop := ∀ dimensions iterator array body,
  nloops dimensions iterator array body =
    .ok (documentedLoops dimensions iterator array body)

def CartesianLoopsCompoundExact : Prop := ∀ dimensions iterator array head args,
  nloops dimensions iterator array (.expr head args) =
    .ok (documentedLoops dimensions iterator array (.expr head args))

end JuliaLean.ExprReflect
