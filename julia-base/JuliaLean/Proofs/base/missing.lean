import JuliaLean.base.array
import JuliaLean.base.abstractdict
import JuliaLean.base.missing
import JuliaLean.Proofs.base.array
import JuliaLean.base.promotion
import JuliaLean.base.iterators
import JuliaLean.base.essentials
import JuliaLean.base.operators
import JuliaLean.Registry.Types

/-!
# Specifications of `base/missing.jl`

The values in `Option α` represent `Union{Missing, α}`. Missing-specific overloads are combined
with ordinary operations from their source-mirrored Base models.
-/

namespace JuliaLean.Proofs.base.missing

open JuliaLean.Registry
open JuliaLean.base.missing
def optionJuliaValue {α : Type} : Option α → JuliaValue
  | none => .missing
  | some value => .value value


/-! ## Three-valued logic -/


def completions : Option Bool → List Bool
  | none => [false, true]
  | some b => [b]

def kleene2 (f : Bool → Bool → Bool) (x y : Option Bool) : Option Bool :=
  let rs := (completions x).flatMap fun a => (completions y).map fun b => f a b
  if rs.all (· == true) then some true else if rs.all (· == false) then some false else none

def kleene1 (f : Bool → Bool) (x : Option Bool) : Option Bool :=
  match x with
  | none => none
  | some b => some (f b)

inductive MaybeBool where
  | missing
  | falseValue
  | trueValue
  deriving DecidableEq

def MaybeBool.toOption : MaybeBool → Option Bool
  | .missing => none
  | .falseValue => some false
  | .trueValue => some true
def ThreeValuedLogic : Prop :=
  ∀ x y : MaybeBool,
    andOption x.toOption y.toOption = kleene2 (· && ·) x.toOption y.toOption ∧
    orOption x.toOption y.toOption = kleene2 (· || ·) x.toOption y.toOption ∧
    xorOption x.toOption y.toOption = kleene2 (· ^^ ·) x.toOption y.toOption ∧
    nandOption x.toOption y.toOption =
      kleene2 (fun left right => !(left && right)) x.toOption y.toOption ∧
    norOption x.toOption y.toOption =
      kleene2 (fun left right => !(left || right)) x.toOption y.toOption ∧
    notOption x.toOption = kleene1 (! ·) x.toOption

theorem threeValuedLogic_proven : ThreeValuedLogic := by
  intro x y
  cases x <;> cases y <;>
    simp [ThreeValuedLogic, andOption, orOption, xorOption, nandOption, norOption,
      notOption, kleene2, kleene1, completions, MaybeBool.toOption,
      andMissingMissing, andMissingBool, andBoolMissing, orMissingMissing,
      orMissingBool, orBoolMissing, xorMissingMissing, xorMissingBool,
      xorBoolMissing, generatedUnaryMissing, JuliaLean.base.essentials.ifelse]

/-! ## Algebraic laws and comparison propagation -/


def LogicAlgebra : Prop :=
  ∀ x y z : MaybeBool,
    andOption x.toOption y.toOption = andOption y.toOption x.toOption ∧
    orOption x.toOption y.toOption = orOption y.toOption x.toOption ∧
    andOption (andOption x.toOption y.toOption) z.toOption =
      andOption x.toOption (andOption y.toOption z.toOption) ∧
    orOption (orOption x.toOption y.toOption) z.toOption =
      orOption x.toOption (orOption y.toOption z.toOption) ∧
    notOption (andOption x.toOption y.toOption) =
      orOption (notOption x.toOption) (notOption y.toOption) ∧
    notOption (orOption x.toOption y.toOption) =
      andOption (notOption x.toOption) (notOption y.toOption) ∧
    andOption x.toOption (orOption y.toOption z.toOption) =
      orOption (andOption x.toOption y.toOption) (andOption x.toOption z.toOption)

theorem logicAlgebra_proven : LogicAlgebra := by
  intro x y z
  cases x <;> cases y <;> cases z <;>
    decide


def ComparisonPropagates : Prop :=
  (∀ (α : Type) (eq lt : α → α → Bool) (x y : Option α),
    ((x = none ∨ y = none) →
      eqOption eq x y = none ∧ neOption eq x y = none ∧ ltOption lt x y = none ∧
      leOption eq lt x y = none ∧ gtOption lt x y = none ∧ geOption eq lt x y = none) ∧
    (∀ a b, x = some a → y = some b →
      eqOption eq x y = some (eq a b) ∧ neOption eq x y = some (!eq a b) ∧
      ltOption lt x y = some (lt a b) ∧ leOption eq lt x y = some (lt a b || eq a b) ∧
      gtOption lt x y = some (lt b a) ∧ geOption eq lt x y = some (lt b a || eq b a))) ∧
  (∀ {WeakRef : Type} (value : WeakRef) (fallback : Bool),
    coalesce [optionJuliaValue (equalMissingWeakRef value), .value fallback] =
        .value fallback ∧
    coalesce [optionJuliaValue (equalWeakRefMissing value), .value fallback] =
        .value fallback)

theorem comparisonPropagates_proven : ComparisonPropagates := by
  constructor
  · intro α eq lt x y
    refine ⟨?_, ?_⟩
    · intro hmiss
      rcases hmiss with hx | hy
      · subst x
        cases y <;> simp [eqOption, neOption, ltOption, leOption, gtOption, geOption,
            notOption, orOption, equalMissingMissing, equalMissingAny, equalAnyMissing,
            lessMissingMissing, lessMissingAny, lessAnyMissing, generatedUnaryMissing,
            orMissingMissing, orMissingBool, orBoolMissing,
            JuliaLean.base.operators.notEqual, JuliaLean.base.operators.lessEqual,
            JuliaLean.base.operators.greaterThan, JuliaLean.base.operators.greaterEqual,
            JuliaLean.base.essentials.ifelse]
      · subst y
        cases x <;> simp [eqOption, neOption, ltOption, leOption, gtOption, geOption,
            notOption, orOption, equalMissingMissing, equalMissingAny, equalAnyMissing,
            lessMissingMissing, lessMissingAny, lessAnyMissing, generatedUnaryMissing,
            orMissingMissing, orMissingBool, orBoolMissing,
            JuliaLean.base.operators.notEqual, JuliaLean.base.operators.lessEqual,
            JuliaLean.base.operators.greaterThan, JuliaLean.base.operators.greaterEqual,
            JuliaLean.base.essentials.ifelse]
    · intro a b hx hy
      rw [hx, hy]
      simp [eqOption, neOption, ltOption, leOption, gtOption, geOption, notOption,
        orOption, JuliaLean.base.operators.notEqual, JuliaLean.base.operators.lessEqual,
        JuliaLean.base.operators.greaterThan, JuliaLean.base.operators.greaterEqual,
        JuliaLean.base.essentials.ifelse]
  · intro WeakRef value fallback
    simp [optionJuliaValue, coalesce, equalMissingWeakRef, equalWeakRefMissing]
/-! ## Missing-last ordering, equality, and extrema -/


def StrictWeak (lt : α → α → Bool) : Prop :=
  (∀ a, lt a a = false) ∧
  (∀ a b c, lt a b = true → lt b c = true → lt a c = true) ∧
  (∀ a b c, lt a b = false → lt b a = false → lt b c = false → lt c b = false →
    lt a c = false ∧ lt c a = false)

def IslessStrictWeak : Prop :=
  ∀ (α : Type) (lt : α → α → Bool), StrictWeak lt → StrictWeak (islessOption lt)

theorem islessStrictWeak_proven : IslessStrictWeak := by
  intro α lt ⟨hirr, htr, hinc⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x
    cases x with
    | none => simp [islessOption, islessMissingMissing]
    | some a => exact hirr a
  · intro x y z hxy hyz
    cases x <;> cases y <;> cases z <;>
      simp_all [islessOption, islessMissingMissing, islessMissingAny, islessAnyMissing] <;>
      try exact htr _ _ _ hxy hyz
  · intro x y z hxy hyx hyz hzy
    cases x <;> cases y <;> cases z <;>
      simp_all [islessOption, islessMissingMissing, islessMissingAny, islessAnyMissing] <;>
      try exact hinc _ _ _ hxy hyx hyz hzy

def IslessTrichotomy : Prop :=
  ∀ (α : Type) (lt eq : α → α → Bool),
    (∀ a b, [lt a b, lt b a, eq a b].count true = 1) →
    ∀ x y : Option α, [islessOption lt x y, islessOption lt y x, isequalOption eq x y].count true = 1

theorem islessTrichotomy_proven : IslessTrichotomy := by
  intro α lt eq h x y
  cases x <;> cases y <;> simp [islessOption, isequalOption, islessMissingMissing,
    islessMissingAny, islessAnyMissing, isequalMissingMissing, isequalMissingAny,
    isequalAnyMissing]
  exact h _ _

def MissingLast : Prop :=
  ∀ (α : Type) (lt : α → α → Bool) (x : Option α),
    islessOption lt none x = false ∧ (x ≠ none → islessOption lt x none = true)

theorem missingLast_proven : MissingLast := by
  intro α lt x
  cases x <;> simp [islessOption, islessMissingMissing, islessMissingAny, islessAnyMissing]

def IsequalMissing : Prop :=
  ∀ (α : Type) (eq : α → α → Bool),
    (∀ x : Option α, isequalOption eq none x = true ↔ x = none) ∧
    ((∀ a, eq a a = true) → (∀ a b, eq a b = eq b a) →
      (∀ a b c, eq a b = true → eq b c = true → eq a c = true) →
      (∀ x : Option α, isequalOption eq x x = true) ∧
      (∀ x y : Option α, isequalOption eq x y = isequalOption eq y x) ∧
      (∀ x y z, isequalOption eq x y = true → isequalOption eq y z = true →
        isequalOption eq x z = true))

theorem isequalMissing_proven : IsequalMissing := by
  intro α eq
  refine ⟨?_, ?_⟩
  · intro x
    cases x <;> simp [isequalOption, isequalMissingMissing, isequalMissingAny]
  · intro href hsym htrans
    refine ⟨?_, ?_, ?_⟩
    · intro x
      cases x <;> simp [isequalOption, isequalMissingMissing, isequalMissingAny, href]
    · intro x y
      cases x <;> cases y <;>
        simp [isequalOption, isequalMissingMissing, isequalMissingAny, isequalAnyMissing, hsym]
    · intro x y z hxy hyz
      cases x <;> cases y <;> cases z <;>
        simp_all [isequalOption, isequalMissingMissing, isequalMissingAny, isequalAnyMissing] <;>
        try exact htrans _ _ _ hxy hyz


def MinMaxMissing : Prop :=
  ∀ (α : Type) (lt : α → α → Bool) (x y : Option α),
    ((x = none ∨ y = none) → minOption lt x y = none ∧ maxOption lt x y = none) ∧
    minmaxOption lt x y = (minOption lt x y, maxOption lt x y)

theorem minMaxMissing_proven : MinMaxMissing := by
  intro α lt x y
  refine ⟨?_, ?_⟩
  · intro h
    cases x <;> cases y <;> simp_all [minOption, maxOption,
      minmaxBinaryBothMissing, minmaxBinaryMissingAny, minmaxBinaryAnyMissing]
  · cases x <;> cases y <;>
      simp [minmaxOption, minOption, maxOption, minmaxPairBothMissing,
        minmaxPairMissingAny, minmaxPairAnyMissing, minmaxBinaryBothMissing,
        minmaxBinaryMissingAny, minmaxBinaryAnyMissing] <;> split <;> simp

/-! ## Type splitting and `coalesce` -/

def unionWithoutMissing (members : List (Option α)) : JuliaType α :=
  match members.filterMap (fun member => member.map some) with
  | [] => .bottom
  | [some value] => .named value
  | kept => .union kept

def stringMembersToPTypes : List (Option String) → List JuliaLean.base.promotion.PType
  | [] => []
  | none :: rest => JuliaLean.base.promotion.primitiveMissingType :: stringMembersToPTypes rest
  | some name :: rest => JuliaLean.base.promotion.PType.parameter name :: stringMembersToPTypes rest

def pTypeUnion : List JuliaLean.base.promotion.PType → JuliaLean.base.promotion.PType
  | [] => .bottom
  | [value] => value
  | value :: rest => .union value (pTypeUnion rest)

def encodeMissingType : JuliaType String → JuliaLean.base.promotion.PType
  | .any => .any
  | .bottom => .bottom
  | .missing => JuliaLean.base.promotion.primitiveMissingType
  | .named name => .parameter name
  | .union members => pTypeUnion (stringMembersToPTypes members)

def decodedMissingMembers : JuliaLean.base.promotion.PType → List (Option String)
  | .bottom => []
  | .union left right => decodedMissingMembers left ++ decodedMissingMembers right
  | .parameter name => [some name]
  | value =>
      if JuliaLean.base.promotion.pEqual value
          JuliaLean.base.promotion.primitiveMissingType then [none] else []

def decodeMissingType : JuliaLean.base.promotion.PType → JuliaType String
  | .any => .any
  | .bottom => .bottom
  | .parameter name => .named name
  | .union left right =>
      match decodedMissingMembers (.union left right) with
      | [] => .bottom
      | [some name] => .named name
      | members => .union members
  | value =>
      if JuliaLean.base.promotion.pEqual value
          JuliaLean.base.promotion.primitiveMissingType then .missing
      else .named (reprStr value)

def sourceTypeSplit (left right : JuliaType String) : JuliaType String :=
  decodeMissingType (JuliaLean.base.promotion.typesplit
    JuliaLean.base.promotion.sourcePTypeOps (encodeMissingType left) (encodeMissingType right))

def NonmissingTypeUnion : Prop :=
  ∀ left right : String,
    nonmissingtype sourceTypeSplit (.union [none, some left, some right]) =
      unionWithoutMissing [none, some left, some right] ∧
    nonmissingtype sourceTypeSplit .any = .any ∧
    eltypeSkipMissing
      (fun (_ : TypeRef Unit) => JuliaType.union [none, some left, some right])
      sourceTypeSplit (⟨()⟩ : TypeRef (SkipMissing Unit)) =
        unionWithoutMissing [none, some left, some right]

theorem nonmissingTypeUnion_proven : NonmissingTypeUnion := by
  intro left right
  constructor <;>
    simp [nonmissingtype, eltypeSkipMissing, sourceTypeSplit, encodeMissingType,
      stringMembersToPTypes, pTypeUnion, decodeMissingType, decodedMissingMembers,
      unionWithoutMissing, JuliaLean.base.promotion.typesplit,
      JuliaLean.base.promotion.sourcePTypeOps, JuliaLean.base.promotion.pSubtype,
      JuliaLean.base.promotion.pEqual, JuliaLean.base.promotion.pListEqual,
      JuliaLean.base.promotion.primitiveMissingType]
def sourceMissingTypeSupertype (supertype subtype : JuliaType String) : Bool :=
  JuliaLean.base.promotion.pSubtype (encodeMissingType subtype) (encodeMissingType supertype)

def sourceMissingTypeBottom : JuliaType String → Bool
  | .bottom => true
  | _ => false

def sourceWrapMissing : JuliaType String → JuliaType String
  | .any => .any
  | .bottom => .missing
  | .missing => .missing
  | .named name => .union [none, some name]
  | .union members => .union (none :: members)


def MissingTypeFunctions : Prop :=
  ∀ {α : Type} (f : UnaryTypeFunction) (T : TypeRef MissingValue),
    JuliaLean.base.essentials.ismissing Option.isNone
        (unaryTypeMissing (α := α) f T) = true ∧
    (∀ (α : Type) (f : UnaryTypeFunction),
      match unaryTypeAnyError (α := α) f with
      | .error (.methodError name arguments) =>
          name = f.juliaName ∧ arguments = [.any]
      | .ok _ => False) ∧
    (∀ (α : Type) (f : FloatTypeFunction),
      match floatTypeAnyError (α := α) f with
      | .error (.methodError name arguments) =>
          name = f.juliaName ∧ arguments = [.any]
      | .ok _ => False) ∧
    (∀ (left right : String)
        (apply : FloatTypeFunction → JuliaType String → JuliaType String)
        (f : FloatTypeFunction),
      match floatTypeWithMissing sourceWrapMissing sourceTypeSplit apply f
        (.union [none, some left, some right]) with
      | .any | .missing => True
      | .union members => none ∈ members
      | .bottom | .named _ => False)

theorem missingTypeFunctions_proven : MissingTypeFunctions := by
  intro α f T
  refine ⟨?_, ?_⟩
  · simp [JuliaLean.base.essentials.ismissing, Option.isNone, unaryTypeMissing]
  · refine ⟨?_, ?_⟩
    · intro α f
      cases f <;> simp [unaryTypeAnyError, UnaryTypeFunction.juliaName]
    · refine ⟨?_, ?_⟩
      · intro α f
        cases f <;> simp [floatTypeAnyError, FloatTypeFunction.juliaName]
      · intro left right apply f
        change match sourceWrapMissing
            (apply f (nonmissingtype sourceTypeSplit (.union [none, some left, some right]))) with
          | .any | .missing => True
          | .union members => none ∈ members
          | .bottom | .named _ => False
        cases apply f (nonmissingtype sourceTypeSplit (.union [none, some left, some right])) <;>
          simp [sourceWrapMissing]


/-!
Nothing to promise: zero/one/oneunit(::Type{T}) where T>:Missing@108: after checked type removal, this wrapper forwards to the ordinary operation; `nonmissingtypeChecked` specifies the removal and its errors.
Nothing to promise: IteratorSize(::Type{<:SkipMissing})@236: dispatch metadata marks the wrapper's size as unknown.
Nothing to promise: IteratorEltype(::Type{SkipMissing{T}})@237: forwards the parent iterator's eltype trait.
Nothing to promise: IndexStyle(::Type{<:SkipMissing{T}})@252: forwards the parent iterator's indexing trait.
Nothing to promise: float(::AbstractArray{Missing})@180: there are no non-missing numeric elements to transform.
-/

def NonmissingTypeChecked : Prop :=
  nonmissingtypeChecked sourceTypeSplit sourceMissingTypeSupertype sourceMissingTypeBottom
      (fun message => .error message) .any = .error "could not compute non-missing type" ∧
  nonmissingtypeChecked sourceTypeSplit sourceMissingTypeSupertype sourceMissingTypeBottom
      (fun message => .error message) .missing =
    .error "cannot convert a value to missing for assignment" ∧
  ∀ value : String,
    nonmissingtypeChecked sourceTypeSplit sourceMissingTypeSupertype sourceMissingTypeBottom
        (fun message => .error message) (.union [none, some value]) =
      .ok (.named value) ∧
    sourceMissingTypeSupertype (.union [none, some value]) (.named value) = true ∧
    nonmissingtype sourceTypeSplit (.union [none, some value]) = .named value

theorem nonmissingTypeChecked_proven : NonmissingTypeChecked := by
  unfold NonmissingTypeChecked
  refine ⟨?_, ?_, ?_⟩
  · simp [sourceMissingTypeSupertype, sourceMissingTypeBottom, nonmissingtypeChecked,
      nonmissingtype, sourceTypeSplit, encodeMissingType, stringMembersToPTypes,
      pTypeUnion, decodeMissingType, decodedMissingMembers,
      JuliaLean.base.promotion.typesplit, JuliaLean.base.promotion.sourcePTypeOps,
      JuliaLean.base.promotion.pSubtype, JuliaLean.base.promotion.pEqual,
      JuliaLean.base.promotion.pListEqual, JuliaLean.base.promotion.primitiveMissingType]
  · simp [sourceMissingTypeSupertype, sourceMissingTypeBottom, nonmissingtypeChecked,
      nonmissingtype, sourceTypeSplit, encodeMissingType, stringMembersToPTypes,
      pTypeUnion, decodeMissingType, decodedMissingMembers,
      JuliaLean.base.promotion.typesplit, JuliaLean.base.promotion.sourcePTypeOps,
      JuliaLean.base.promotion.pSubtype, JuliaLean.base.promotion.pEqual,
      JuliaLean.base.promotion.pListEqual, JuliaLean.base.promotion.primitiveMissingType]
  · intro value
    simp [sourceMissingTypeSupertype, sourceMissingTypeBottom, nonmissingtypeChecked,
      nonmissingtype, sourceTypeSplit, encodeMissingType, stringMembersToPTypes,
      pTypeUnion, decodeMissingType, decodedMissingMembers,
      JuliaLean.base.promotion.typesplit, JuliaLean.base.promotion.sourcePTypeOps,
      JuliaLean.base.promotion.pSubtype, JuliaLean.base.promotion.pEqual,
      JuliaLean.base.promotion.pListEqual, JuliaLean.base.promotion.primitiveMissingType]


def firstNonmissingValue : List JuliaValue → JuliaValue
  | [] => .missing
  | .missing :: rest => firstNonmissingValue rest
  | value :: _ => value

def firstEvaluated (evaluate : Arg → JuliaValue) : List Arg → JuliaValue
  | [] => .missing
  | arg :: rest =>
    match evaluate arg with
    | .missing => firstEvaluated evaluate rest
    | value => value

def evaluatedPrefix (evaluate : Arg → JuliaValue) : List Arg → List Arg
  | [] => []
  | arg :: rest =>
    arg :: (match evaluate arg with
      | .missing => evaluatedPrefix evaluate rest
      | .value _ => [])

def coalesceBody {Arg : Type} : CoalesceExpr Arg → CoalesceExpr Arg
  | .letValue body => body
  | expr => expr

theorem coalesceMacro_cons {Arg : Type} (arg : Arg) (args : List Arg) :
    coalesceMacro (arg :: args) =
      .letValue (.conditional (.not (.ismissing (.escapedAssignment "val" arg)))
        (.variable "val") (coalesceBody (coalesceMacro args))) := by
  simp [coalesceMacro, coalesceBody, List.reverse_cons, List.foldl_append]

def CoalesceMacroFirst : Prop :=
  ∀ (Arg : Type) (evaluate : Arg → JuliaValue) (args : List Arg),
    let result := evalCoalesceExprWithState
      (fun arg trace => (evaluate arg, trace ++ [arg]))
      (coalesceMacro args) ([], none)
    result.1 = firstEvaluated evaluate args ∧
    result.2.1 = evaluatedPrefix evaluate args

def CoalesceMacroBodyFirst : Prop :=
  ∀ {Arg : Type} (evaluate : Arg → JuliaValue) (args : List Arg)
      (trace : List Arg) (binding : Option JuliaValue),
    let result := evalCoalesceExprWithState
      (fun arg evaluated => (evaluate arg, evaluated ++ [arg]))
      (coalesceBody (coalesceMacro args)) (trace, binding)
    result.1 = firstEvaluated evaluate args ∧
    result.2.1 = trace ++ evaluatedPrefix evaluate args

theorem coalesceMacroBodyFirst_proven : CoalesceMacroBodyFirst := by
  intro Arg evaluate args
  induction args with
  | nil =>
    intro trace binding
    simp [CoalesceMacroBodyFirst, coalesceBody, coalesceMacro,
      evalCoalesceExprWithState, firstEvaluated, evaluatedPrefix]
  | cons arg args ih =>
    intro trace binding
    rw [coalesceMacro_cons]
    cases he : evaluate arg with
    | missing =>
      simp only [coalesceBody, evalCoalesceExprWithState, evalCoalesceCondition,
        evalCoalesceAssignment, he, Bool.not_true, if_false]
      have h := ih (trace ++ [arg]) (some .missing)
      simpa [coalesceBody, he, firstEvaluated, evaluatedPrefix, List.append_assoc] using h
    | value value =>
      simp [coalesceBody, evalCoalesceExprWithState, evalCoalesceCondition,
        evalCoalesceAssignment, he, firstEvaluated, evaluatedPrefix]

theorem coalesceMacroFirst_proven : CoalesceMacroFirst := by
  intro Arg evaluate args
  have h := coalesceMacroBodyFirst_proven evaluate args [] none
  simpa [CoalesceMacroFirst, evalCoalesceExprWithState, coalesceBody,
    coalesceMacro] using h

def CoalesceFirst : Prop :=
  (∀ values : List JuliaValue, coalesce values = firstNonmissingValue values) ∧
  CoalesceMacroFirst

theorem coalesceFirst_proven : CoalesceFirst := by
  constructor
  · intro values
    induction values with
    | nil => rfl
    | cons value values ih =>
      cases value <;> simp [coalesce, firstNonmissingValue, ih]
  · exact coalesceMacroFirst_proven
/-! ## `skipmissing` on finite vectors -/

def NonmissingLength (xs : List (Option α)) : Prop :=
  (xs.filterMap id).length = xs.countP Option.isSome

theorem nonmissingLength_proven : ∀ (xs : List (Option α)), NonmissingLength xs := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    unfold NonmissingLength at ih ⊢
    cases x <;> simp [ih]

def filterMissingStep {α : Type} (predicate : α → Bool) (values : List α)
    (entry : Option α) : List α :=
  if !Option.isNone entry then
    match entry with
    | none => values
    | some x => if predicate x then values ++ [x] else values
  else values

theorem foldlFilterMissing {α : Type} (predicate : α → Bool) :
    ∀ (entries : List (Option α)) (values : List α),
      entries.foldl (filterMissingStep predicate) values =
        values ++ (entries.filterMap id).filter predicate := by
  intro entries
  induction entries with
  | nil => intro values; simp
  | cons entry entries ih =>
    intro values
    simp only [List.foldl_cons]
    rw [ih]
    cases entry with
    | none => simp [filterMissingStep, Option.isNone]
    | some value =>
      by_cases h : predicate value
      · simp [filterMissingStep, Option.isNone, h, List.filter_cons,
          List.filterMap_cons, List.append_assoc]
      · simp [filterMissingStep, Option.isNone, h, List.filter_cons,
          List.filterMap_cons, List.append_assoc]

def filterSkipMissingList {α : Type} (xs : List (Option α)) (predicate : α → Bool) : List α :=
  filterSkipMissing (fun values => values) (fun _ _ _ => ([] : List α))
    (fun values value => values ++ [value]) (fun T _ => T)
    (fun _ => JuliaType.union []) Option.isNone predicate (skipmissing xs)

def SkipMissingFilter : Prop :=
  ∀ {α : Type} (xs : List (Option α)) (predicate : α → Bool),
    filterSkipMissingList xs predicate = (xs.filterMap id).filter predicate

theorem skipMissingFilter_proven : SkipMissingFilter := by
  intro α xs predicate
  change xs.foldl (filterMissingStep predicate) [] =
    (xs.filterMap id).filter predicate
  simpa using foldlFilterMissing predicate xs ([] : List α)

def listIteratorStep {α : Type} (itr : List (Option α))
    (states : List (List (Option α))) :
    Option (Option α × List (Option α)) :=
  match states with
  | [] =>
      match itr with
      | [] => none
      | item :: rest => some (item, rest)
  | [remaining] =>
      match remaining with
      | [] => none
      | item :: rest => some (item, rest)
  | _ => none

def listIteratorNext {α : Type} (_itr : List (Option α))
    (state : List (Option α)) : Option (Option α × List (Option α)) :=
  match state with
  | [] => none
  | item :: rest => some (item, rest)

def firstNonmissingState {α : Type} :
    List (Option α) → Option (Option α × List (Option α))
  | [] => none
  | none :: rest => firstNonmissingState rest
  | some value :: rest => some (some value, rest)

def firstNonmissingWith {α : Type} (item : Option α) (rest : List (Option α)) :
    Option (Option α × List (Option α)) :=
  match item with
  | none => firstNonmissingState rest
  | some _ => some (item, rest)

private theorem listLoopReturnsSpec {α : Type} (itr : List (Option α)) :
    ∀ (item : Option α) (rest : List (Option α))
      (result : Option (Option α × List (Option α))),
      iterateSkipMissingLoopReturns listIteratorNext Option.isNone itr item rest result →
      result = firstNonmissingWith item rest := by
  intro item rest result h
  induction rest generalizing item result with
  | nil =>
      cases item with
      | none =>
          cases h with
          | returned h => simp [Option.isNone] at h
          | exhausted _ _ => simp [firstNonmissingWith, firstNonmissingState]
          | skipped _ hnext _ => simp [listIteratorNext] at hnext
      | some value =>
          cases h with
          | returned _ => rfl
          | exhausted h _ => simp [Option.isNone] at h
          | skipped h _ _ => simp [Option.isNone] at h
  | cons next rest ih =>
      cases item with
      | none =>
          cases h with
          | returned h => simp [Option.isNone] at h
          | exhausted _ hnext => simp [listIteratorNext] at hnext
          | skipped _ hnext tail =>
              dsimp [listIteratorNext] at hnext
              cases hnext
              have hs := ih next result tail
              cases next <;> simpa [firstNonmissingWith, firstNonmissingState] using hs
      | some value =>
          cases h with
          | returned _ => rfl
          | exhausted h _ => simp [Option.isNone] at h
          | skipped h _ _ => simp [Option.isNone] at h

private theorem listIteratorStartSpec {α : Type} (xs : List (Option α))
    (result : Option (Option α × List (Option α))) :
    iterateSkipMissingReturns listIteratorStep listIteratorNext Option.isNone
      (skipmissing xs) [] result →
    result = firstNonmissingState xs := by
  intro h
  cases xs with
  | nil =>
      simp [iterateSkipMissingReturns, listIteratorStep, skipmissing] at h
      exact h
  | cons item rest =>
      simp [iterateSkipMissingReturns, listIteratorStep, skipmissing] at h
      have hs := listLoopReturnsSpec (item :: rest) item rest result h
      cases item <;> simpa [firstNonmissingWith, firstNonmissingState] using hs

private theorem listIteratorStateSpec {α : Type} (xs suffix : List (Option α))
    (result : Option (Option α × List (Option α))) :
    iterateSkipMissingReturns listIteratorStep listIteratorNext Option.isNone
      (skipmissing xs) [suffix] result →
    result = firstNonmissingState suffix := by
  intro h
  cases suffix with
  | nil =>
      simp [iterateSkipMissingReturns, listIteratorStep, skipmissing] at h
      exact h
  | cons item rest =>
      simp [iterateSkipMissingReturns, listIteratorStep, skipmissing] at h
      have hs := listLoopReturnsSpec xs item rest result h
      cases item <;> simpa [firstNonmissingWith, firstNonmissingState] using hs

def SkipMissingIterate : Prop :=
  ∀ {α : Type} (xs : List (Option α)),
    (∀ result, iterateSkipMissingReturns listIteratorStep listIteratorNext Option.isNone
      (skipmissing xs) [] result → result = firstNonmissingState xs) ∧
    (∀ suffix result, iterateSkipMissingReturns listIteratorStep listIteratorNext Option.isNone
      (skipmissing xs) [suffix] result → result = firstNonmissingState suffix)

theorem skipMissingIterate_proven : SkipMissingIterate := by
  intro α xs
  constructor
  · exact listIteratorStartSpec xs
  · intro suffix result
    exact listIteratorStateSpec xs suffix result

theorem firstNonmissingStateCount {α : Type} (xs : List (Option α)) :
    (firstNonmissingState xs = none → xs.countP Option.isSome = 0) ∧
    (∀ value suffix, firstNonmissingState xs = some (some value, suffix) →
      xs.countP Option.isSome = suffix.countP Option.isSome + 1) := by
  induction xs with
  | nil =>
    constructor
    · intro _
      rfl
    · intro value suffix h
      simp [firstNonmissingState] at h
  | cons item xs ih =>
    cases item with
    | none =>
      rcases ih with ⟨hnone, hyield⟩
      constructor
      · intro h
        have h' : firstNonmissingState xs = none := by
          simpa [firstNonmissingState] using h
        have hc := hnone h'
        simpa [Option.isSome] using hc
      · intro value suffix h
        have h' : firstNonmissingState xs = some (some value, suffix) := by
          simpa [firstNonmissingState] using h
        have hc := hyield value suffix h'
        simpa [Option.isSome] using hc
    | some item =>
      constructor
      · intro h
        simp [firstNonmissingState] at h
      · intro value suffix h
        simp [firstNonmissingState] at h
        rcases h with ⟨rfl, rfl⟩
        simp [Option.isSome]

theorem firstNonmissingState_ne_missing {α : Type} (xs : List (Option α))
    (suffix : List (Option α)) :
    firstNonmissingState xs ≠ some (none, suffix) := by
  induction xs with
  | nil => simp [firstNonmissingState]
  | cons item xs ih =>
    cases item with
    | none => simpa [firstNonmissingState] using ih
    | some value => simp [firstNonmissingState]

def SkipMissingLength : Prop :=
  ∀ {α : Type} (xs : List (Option α))
      (result : Option (Option α × List (Option α))),
    iterateSkipMissingReturns listIteratorStep listIteratorNext Option.isNone
      (skipmissing xs) [] result →
    match result with
    | none => xs.countP Option.isSome = 0
    | some (none, _) => False
    | some (some _, suffix) =>
        xs.countP Option.isSome = suffix.countP Option.isSome + 1

theorem skipMissingLength_proven : SkipMissingLength := by
  intro α xs result h
  have hstate := listIteratorStartSpec xs result h
  cases result with
  | none =>
      exact (firstNonmissingStateCount xs).1 hstate.symm
  | some pair =>
      rcases pair with ⟨item, suffix⟩
      cases item with
      | none =>
          exact False.elim (firstNonmissingState_ne_missing xs suffix hstate.symm)
      | some value =>
          exact (firstNonmissingStateCount xs).2 value suffix hstate.symm

def listIndices {α : Type} (xs : List (Option α)) : List Nat :=
  (List.range xs.length).map Nat.succ

def listIndexValue {α : Type} (xs : List (Option α)) (i : Nat) : Option α :=
  xs.getD (i - 1) none

def listKeysSkipMissing {α : Type} (xs : List (Option α)) : List Nat :=
  keysSkipMissing List.filter listIndices listIndexValue Option.isNone (skipmissing xs)

def listEachindexSkipMissing {α : Type} (xs : List (Option α)) : List Nat :=
  eachindexSkipMissing List.filter listIndices listIndexValue Option.isNone (skipmissing xs)

def listGetindexScalar {α : Type} (xs : List (Option α)) (indices : List Nat) :
    Except Unit (Option α) :=
  match indices with
  | [i] => .ok (listIndexValue xs i)
  | _ => .error ()

def listSkipMissingGetindex {α : Type} (xs : List (Option α)) (i : Nat) :
    Except (MissingIndexError Unit String) (Option α) :=
  getindexSkipMissing listGetindexScalar Option.isNone (fun _ => "missing")
    (skipmissing xs) [i]

def SkipMissingKeys : Prop :=
  ∀ {α : Type} (xs : List (Option α)),
    listKeysSkipMissing xs =
        (listIndices xs).filter (fun i => !Option.isNone (listIndexValue xs i)) ∧
    listEachindexSkipMissing xs =
        (listIndices xs).filter (fun i => !Option.isNone (listIndexValue xs i)) ∧
    (∀ i value, listIndexValue xs i = some value →
      listSkipMissingGetindex xs i = .ok (some value)) ∧
    (∀ i, listIndexValue xs i = none →
      listSkipMissingGetindex xs i = .error (.missing ⟨"missing"⟩))

theorem skipMissingKeys_proven : SkipMissingKeys := by
  intro α xs
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro i value h
    simp [listSkipMissingGetindex, getindexSkipMissing, listGetindexScalar,
      skipmissing, Option.isNone, h]
  · intro i h
    simp [listSkipMissingGetindex, getindexSkipMissing, listGetindexScalar,
      skipmissing, Option.isNone, h]

def skipMissingPairs {α : Type} (xs : List (Option α)) : List (Nat × α) :=
  JuliaLean.base.abstractdict.pairsGeneric listKeysSkipMissing
    (fun values => filterSkipMissingList values (fun _ => true))
    (fun keys values => keys.zip values) xs

def sourcePairsFromParent {α : Type} (xs : List (Option α)) : List (Nat × α) :=
  (listKeysSkipMissing xs).zip (xs.filterMap id)

private theorem skipMissingPairsSourceSpec {α : Type} (xs : List (Option α)) :
    skipMissingPairs xs = sourcePairsFromParent xs := by
  have hvalues := skipMissingFilter_proven xs (fun _ => true)
  have hfilter :
      List.filter (fun _ : α => true) (xs.filterMap id) = xs.filterMap id :=
    List.filter_eq_self.2 (by intro value hvalue; rfl)
  simp [skipMissingPairs, sourcePairsFromParent, JuliaLean.base.abstractdict.pairsGeneric]
  rw [hvalues, hfilter]

def firstMatchingIndex {α : Type} (predicate : α → Bool) :
    List (Nat × α) → Option Nat
  | [] => none
  | (index, value) :: rest =>
      if predicate value then some index else firstMatchingIndex predicate rest

private theorem findfirstPairsSpec {α : Type} (predicate : α → Bool) :
    ∀ pairs : List (Nat × α),
      JuliaLean.base.array.findfirst (m := Id) (fun value => pure (predicate value)) pairs =
        firstMatchingIndex predicate pairs := by
  intro pairs
  induction pairs with
  | nil =>
      rw [JuliaLean.Proofs.base.array.findfirst_nil]
      rfl
  | cons pair rest ih =>
      rcases pair with ⟨index, value⟩
      rw [JuliaLean.Proofs.base.array.findfirst_cons]
      by_cases h : predicate value
      · simp [firstMatchingIndex, h]
      · simp [firstMatchingIndex, h, ih]

def SkipMissingFindFirst : Prop :=
  ∀ {α : Type} (xs : List (Option α)) (predicate : α → Bool),
    JuliaLean.base.array.findfirst (m := Id) (fun value => pure (predicate value))
      (skipMissingPairs xs) =
        firstMatchingIndex predicate (sourcePairsFromParent xs)

theorem skipMissingFindFirst_proven : SkipMissingFindFirst := by
  intro α xs predicate
  rw [findfirstPairsSpec, skipMissingPairsSourceSpec]


inductive AbstractNumber where
  | ordinary
  | bigFloat
  | bigInteger
  deriving Repr, DecidableEq

inductive FloatNumber where
  | ordinaryFloat
  | bigFloatExact
  | bigIntegerFloat
  | roundedBigFloat
  | infinity
  deriving Repr, DecidableEq

def floatAbstractNumber : AbstractNumber → FloatNumber
  | .ordinary => .ordinaryFloat
  | .bigFloat => .bigFloatExact
  | .bigInteger => .bigIntegerFloat

def floatAbstractArray (xs : List (Option AbstractNumber)) : List (Option FloatNumber) :=
  xs.map fun item =>
    match item with
    | none => none
    | some .ordinary => some .ordinaryFloat
    | some .bigFloat => some .roundedBigFloat
    | some .bigInteger => some .infinity

def FloatArrayElementwise : Prop :=
  ∀ xs : List (Option AbstractNumber),
    floatArrayMissing (ArrayLike := List) (T := AbstractNumber) (U := FloatNumber)
      (fun _ => .ordinary) floatAbstractNumber (fun _ => ⟨()⟩) floatAbstractArray xs =
        xs.map (Option.map floatAbstractNumber)

theorem floatArrayExact_refuted : ¬ FloatArrayElementwise := by
  intro h
  have hbig := h [some .bigFloat]
  simp [floatArrayMissing, floatAbstractNumber, floatAbstractArray, Id.run] at hbig

theorem floatArrayBigIntOverflow :
    floatArrayMissing (ArrayLike := List) (T := AbstractNumber) (U := FloatNumber)
      (fun _ => .ordinary) floatAbstractNumber (fun _ => ⟨()⟩) floatAbstractArray
      [some .bigInteger] = [some .infinity] := by
  rfl
def arrayGetindexVector (xs : List (Option Unit)) (indices : List Nat) :
    Except Unit (Option (List (Option Unit))) :=
  .ok (some (indices.map fun i => xs.getD (i - 1) none))

def SkipMissingGetindexNoMissing : Prop :=
  ∀ (xs : List (Option Unit)) (indices : List Nat) (values : List (Option Unit)),
    getindexSkipMissing arrayGetindexVector Option.isNone (fun _ => "missing")
        (skipmissing xs) indices = .ok (some values) →
    ∀ value ∈ values, value.isSome

theorem skipMissingGetindexNoMissing_refuted : ¬ SkipMissingGetindexNoMissing := by
  intro h
  have hresult := h [some (), none] [2] [none] (by rfl)
  have hmissing := hresult none (by simp)
  simp at hmissing

def missingFallsThrough {α : Type} (result : Option α) (fallback : α) : Prop :=
  coalesce [optionJuliaValue result, .value fallback] = .value fallback

def ArithmeticPropagation : Prop :=
  ∀ {Result Number Integer Mode : Type} (number : Number) (integer : Integer)
      (mode : Mode) (fallback : Result),
    missingFallsThrough
      (generatedBinaryMissingBoth (α := Result) .missing .missing) fallback ∧
    missingFallsThrough
      (generatedBinaryMissingNumber (α := Result) .missing number) fallback ∧
    missingFallsThrough
      (generatedBinaryNumberMissing (α := Result) number .missing) fallback ∧
    missingFallsThrough
      (divMissingMissing (α := Result) .missing .missing mode) fallback ∧
    missingFallsThrough
      (divMissingNumber (α := Result) .missing number mode) fallback ∧
    missingFallsThrough
      (divNumberMissing (α := Result) number .missing mode) fallback ∧
    missingFallsThrough
      (powerMissingInteger (α := Result) .missing integer) fallback

theorem arithmeticPropagation_proven : ArithmeticPropagation := by
  intro Result Number Integer Mode number integer mode fallback
  simp [missingFallsThrough, optionJuliaValue, coalesce, generatedBinaryMissingBoth,
    generatedBinaryMissingNumber, generatedBinaryNumberMissing, divMissingMissing,
    divMissingNumber, divNumberMissing, powerMissingInteger]

def MissingPredicates : Prop :=
  ∀ {α K : Type} (value : α) (kwargs : List K) (fallback : Bool),
    missingFallsThrough ispositiveMissing fallback ∧
    missingFallsThrough isnegativeMissing fallback ∧
    missingFallsThrough (isapproxMissingMissing kwargs) fallback ∧
    missingFallsThrough (isapproxMissingAny value kwargs) fallback ∧
    missingFallsThrough (isapproxAnyMissing value kwargs) fallback

theorem missingPredicates_proven : MissingPredicates := by
  intro α K value kwargs fallback
  simp [missingFallsThrough, optionJuliaValue, coalesce, ispositiveMissing,
    isnegativeMissing, isapproxMissingMissing, isapproxMissingAny, isapproxAnyMissing]

def MissingOperatorPropagation : Prop :=
  ∀ {Result Integer Mode AbstractString AbstractChar Lower Upper : Type}
      (integer : Integer) (mode : Mode) (text : Sum AbstractString AbstractChar)
      (lower : Lower) (upper : Upper) (sigdigits digits base : Integer)
      (fallback : Result),
    missingFallsThrough (generatedUnaryMissing (α := Result) .missing) fallback ∧
    missingFallsThrough (andMissingInteger (α := Result) .missing integer) fallback ∧
    missingFallsThrough (andIntegerMissing (α := Result) integer .missing) fallback ∧
    missingFallsThrough (orMissingInteger (α := Result) .missing integer) fallback ∧
    missingFallsThrough (orIntegerMissing (α := Result) integer .missing) fallback ∧
    missingFallsThrough (xorMissingInteger (α := Result) .missing integer) fallback ∧
    missingFallsThrough (xorIntegerMissing (α := Result) integer .missing) fallback ∧
    missingFallsThrough (multiplyMissingText (α := Result) .missing text) fallback ∧
    missingFallsThrough (multiplyTextMissing (α := Result) text .missing) fallback ∧
    missingFallsThrough (clampMissing (α := Result) .missing lower upper) fallback ∧
    missingFallsThrough (roundMissing (α := Result) .missing mode sigdigits digits base)
      fallback ∧
    missingFallsThrough (roundMissingToSupertype (α := Result) .missing .missing mode)
      fallback

theorem missingOperatorPropagation_proven : MissingOperatorPropagation := by
  intro Result Integer Mode AbstractString AbstractChar Lower Upper
    integer mode text lower upper sigdigits digits base fallback
  simp [missingFallsThrough, optionJuliaValue, coalesce, generatedUnaryMissing,
    andMissingInteger, andIntegerMissing, orMissingInteger, orIntegerMissing,
    xorMissingInteger, xorIntegerMissing, multiplyMissingText, multiplyTextMissing,
    clampMissing, roundMissing, roundMissingToSupertype]
def renderLazyStringParts {α : Type} (render : α → String) :
    List (Sum String α) → String
  | [] => ""
  | .inl text :: parts => text ++ renderLazyStringParts render parts
  | .inr value :: parts => render value ++ renderLazyStringParts render parts

def MissingRounding : Prop :=
  (∀ {α Message Mode : Type}
      (missingException : Message → MissingException Message)
      (lazyString : List (Sum String α) → Message) (T : α)
      (value : MissingValue) (mode : Mode),
    roundMissingToType missingException lazyString T value mode =
      .error (missingException (missingConversionMessage lazyString T))) ∧
  (∀ {α Mode : Type} (render : α → String) (T : α) (mode : Mode),
    roundMissingToType (fun message => ⟨message⟩)
        (renderLazyStringParts render) T .missing mode =
      .error ⟨"cannot convert a missing value to type " ++ render T ++
        ": use Union{" ++ render T ++ ", Missing} instead"⟩)

theorem missingRounding_proven : MissingRounding := by
  refine ⟨?_, ?_⟩
  · intro α Message Mode missingException lazyString T value mode
    simp [roundMissingToType, missingConversionMessage]
  · intro α Mode render T mode
    simp [roundMissingToType, missingConversionMessage, renderLazyStringParts,
      String.append_assoc]

def capturePrintText (output : List String) (text : String) : List String :=
  output ++ [text]

def capturePrintException (output : List String) (lead message : String) : List String :=
  output ++ [lead ++ message]

def capturePrintArgument (output : List String) : PrintArgument String → List String
  | .text text => output ++ [text]
  | .message message => output ++ [message]
  | .character character => output ++ [String.ofList [character]]

def MissingDisplay : Prop :=
  (∀ output, showMissing capturePrintText output .missing = output ++ ["missing"]) ∧
  (∀ output message,
    showMissingException capturePrintException output ⟨message⟩ =
      output ++ ["MissingException: " ++ message]) ∧
  (∀ {Itr : Type} (showValue : List String → Itr → List String)
      (output : List String) (itr : SkipMissing Itr),
    showSkipMissing capturePrintArgument showValue output itr =
      showValue (output ++ ["skipmissing("]) itr.x ++ [")"])

theorem missingDisplay_proven : MissingDisplay := by
  refine ⟨?_, ?_, ?_⟩
  · intro output
    rfl
  · intro output message
    rfl
  · intro Itr showValue output itr
    simp [showSkipMissing, capturePrintArgument]
    rfl



def SkipMissingMapreduce : Prop :=
  ∀ {Index α β : Type}
      (indexStyle : TypeRef (AbstractArrayModel Index α) → IndexStyleModel)
      (eltypeIncludesMissing : AbstractArrayModel Index α → Bool)
      (mapreduceRaw : IndexStyleModel → (α → β) → (β → β → β) →
        AbstractArrayModel Index α → β)
      (mapfoldl : (α → β) → (β → β → β) →
        SkipMissing (AbstractArrayModel Index α) → β)
      (indexOps : IntegerIndexOps Index)
      (typesplit : JuliaType α → JuliaType α → JuliaType α)
      (eltype : TypeRef (AbstractArrayModel Index α) → JuliaType α)
      (ismissing : Option α → Bool) (assertNonmissing : Option α → α)
      (mapreduceEmpty : (α → β) → (β → β → β) → JuliaType α → β)
      (mapreduceFirst : (α → β) → (β → β → β) → α → β)
      (pairwiseBlocksize : (α → β) → (β → β → β) → JInt64)
      (something : Option β → β) (f : α → β) (op : β → β → β)
      (itr : SkipMissing (AbstractArrayModel Index α)),
    (eltypeIncludesMissing itr.x = false →
      mapreduceSkipMissing indexStyle eltypeIncludesMissing mapreduceRaw mapfoldl
        indexOps typesplit eltype ismissing assertNonmissing mapreduceEmpty
        mapreduceFirst pairwiseBlocksize something f op itr =
      mapreduceRaw (indexStyle ⟨()⟩) f op itr.x) ∧
    (eltypeIncludesMissing itr.x = true →
      indexStyle ⟨()⟩ = .linear →
      mapreduceSkipMissing indexStyle eltypeIncludesMissing mapreduceRaw mapfoldl
        indexOps typesplit eltype ismissing assertNonmissing mapreduceEmpty
        mapreduceFirst pairwiseBlocksize something f op itr =
      mapreduceIndexLinear indexOps typesplit eltype ismissing assertNonmissing
        mapreduceEmpty mapreduceFirst pairwiseBlocksize something f op itr) ∧
    (eltypeIncludesMissing itr.x = true →
      indexStyle ⟨()⟩ = .cartesian →
      mapreduceSkipMissing indexStyle eltypeIncludesMissing mapreduceRaw mapfoldl
        indexOps typesplit eltype ismissing assertNonmissing mapreduceEmpty
        mapreduceFirst pairwiseBlocksize something f op itr =
      mapreduceIndexCartesian mapfoldl f op itr)

theorem skipMissingMapreduce_proven : SkipMissingMapreduce := by
  intro Index α β indexStyle eltypeIncludesMissing mapreduceRaw mapfoldl
    indexOps typesplit eltype ismissing assertNonmissing mapreduceEmpty
    mapreduceFirst pairwiseBlocksize something f op itr
  refine ⟨?_, ?_, ?_⟩
  · intro hmissing
    cases hstyle : indexStyle ⟨()⟩ <;>
      simp [mapreduceSkipMissing, hmissing, hstyle]
  · intro hmissing hstyle
    simp [mapreduceSkipMissing, hmissing, hstyle]
  · intro hmissing hstyle
    simp [mapreduceSkipMissing, hmissing, hstyle]

/-- The reversed `pairs(skipmissing(x))` iterator fails when its input sizes are unknown. -/
inductive SkipMissingReversePairs (α : Type) where
  | failed (error : JuliaLean.JlError)
  | values (pairs : List (Nat × α))

instance skipMissingReversePairsForIn {α : Type} :
    ForIn JuliaLean.Jl (SkipMissingReversePairs α) (Nat × α) where
  forIn source initial step :=
    match source with
    | .failed error => .error error
    | .values pairs => ForIn.forIn pairs initial step

def unknownSizeIterator (size : JuliaLean.base.iterators.IteratorSizeTag) :
    JuliaLean.base.iterators.IteratorModel Unit Unit where
  run := fun _ => .ok none
  isdone := fun _ => .ok (some true)
  iteratorSize := size
  iteratorEltype := .eltypeUnknown
  length := .ok 0
  size := .ok []

def skipMissingIteratorSizeTag : JuliaLean.base.iterators.IteratorSizeTag :=
  match JuliaLean.base.missing.iteratorSizeSkipMissing (Itr := Unit) ⟨()⟩ with
  | .sizeUnknown => .sizeUnknown

def skipMissingPairIteratorSizes :
    List (JuliaLean.base.iterators.IteratorModel Unit Unit) :=
  [unknownSizeIterator JuliaLean.base.iterators.filterIteratorSize,
    unknownSizeIterator skipMissingIteratorSizeTag]

def skipMissingReversePairs {α : Type} (pairs : List (Nat × α)) :
    SkipMissingReversePairs α :=
  match JuliaLean.base.iterators.reverseZipModel
      (fun i => i.iteratorSize) (fun i => i.length) (fun i => pure i)
      ⟨skipMissingPairIteratorSizes⟩ with
  | .error error => .failed error
  | .ok _ => .values pairs.reverse

def lastMatchingIndex {α : Type} (predicate : α → Bool)
    (pairs : List (Nat × α)) : Option Nat :=
  (pairs.reverse.find? (fun pair => predicate pair.2)).map Prod.fst

def SkipMissingFindLast : Prop :=
  ∀ {α : Type} (xs : List (Option α)) (predicate : α → Bool),
    JuliaLean.base.array.findlast (m := JuliaLean.Jl) skipMissingReversePairs
      (fun value => pure (predicate value)) (skipMissingPairs xs) =
        .ok (lastMatchingIndex predicate (skipMissingPairs xs))

theorem skipMissingReversePairsError {α : Type} (pairs : List (Nat × α)) :
    skipMissingReversePairs pairs =
      .failed (.argumentError
        "Cannot reverse zipped iterators of unknown, infinite, or unequal lengths") := by
  simp [skipMissingReversePairs, JuliaLean.base.iterators.reverseZipModel,
    JuliaLean.base.iterators.zipLengthsFiniteEqualOn, skipMissingPairIteratorSizes,
    skipMissingIteratorSizeTag, unknownSizeIterator,
    JuliaLean.base.iterators.filterIteratorSize,
    JuliaLean.base.missing.iteratorSizeSkipMissing]

@[simp] private theorem skipMissingReversePairsFailedForIn {α β : Type}
    (error : JuliaLean.JlError) (initial : β)
    (step : Nat × α → β → JuliaLean.Jl (ForInStep β)) :
    ForIn.forIn (SkipMissingReversePairs.failed error) initial step = .error error := by
  rfl

theorem skipMissingFindLast_refuted : ¬ SkipMissingFindLast := by
  intro h
  have hresult := h [some ()] (fun _ => true)
  simp [JuliaLean.base.array.findlast, skipMissingReversePairsError,
    skipMissingReversePairs, JuliaLean.base.iterators.reverseZipModel,
    JuliaLean.base.iterators.zipLengthsFiniteEqualOn, skipMissingPairIteratorSizes,
    skipMissingIteratorSizeTag, unknownSizeIterator,
    JuliaLean.base.iterators.filterIteratorSize,
    JuliaLean.base.missing.iteratorSizeSkipMissing,
    lastMatchingIndex, Bind.bind, Pure.pure, Except.bind, Except.pure] at hresult

/-!
Nothing to promise: promote_rule(::Type{Missing}, ::Type)@48: registers the Missing promotion case and delegates union construction to the type system.
Nothing to promise: promote_rule(::Type{Union{Nothing,Missing}}, ::Type)@49: registers the Nothing-and-Missing promotion case and delegates union construction to the type system.
Nothing to promise: promote_rule(::Type{>:Union{Nothing,Missing}}, ::Type)@50: extracts the non-Nothing member and delegates the remaining promotion to the type system.
Nothing to promise: promote_rule(::Type{>:Missing}, ::Type)@60: extracts the non-Missing member and delegates the remaining promotion to the type system.
Nothing to promise: convert(::Type{T}, ::T) where T>:Missing@68: returns its argument unchanged as the generic conversion identity.
Nothing to promise: convert(::Type{T}, ::T) where T>:Union{Missing,Nothing}@69: returns its argument unchanged as the generic conversion identity.
Nothing to promise: convert(::Type{T}, x) where T>:Missing@70: forwards conversion after checked removal of Missing from the target type.
Nothing to promise: convert(::Type{T}, x) where T>:Union{Missing,Nothing}@71: forwards conversion after checked removal of Nothing and Missing from the target type.
Nothing to promise: round(::Type{T}, x::Any, ::RoundingMode) where T>:Missing@147: forwards rounding after checked removal of Missing from the target type.
Nothing to promise: round(::Type{T}, x::Real, ::RoundingMode) where T>:Missing@149: forwards rounding after checked removal of Missing from the target type.
Nothing to promise: round(::Type{T}, x::Rational, ::RoundingMode) where T>:Missing@150: forwards rounding after checked removal of Missing from the target type.
Nothing to promise: round(::Type{T}, x::Rational{Bool}, ::RoundingMode) where T>:Missing@151: forwards rounding after checked removal of Missing from the target type.
Nothing to promise: skipmissing@231: constructs the wrapper around the input iterator.
-/

/-! ## Registry -/

private def entry (id : String) (fns : List String) (statement source : String)
    (prop thm : Lean.Name) (status : Status := .proven) (issue : String := "") : Entry :=
  { id, juliaFile := "base/missing.jl", juliaFns := fns, statement, source, status,
    prop, thm := some thm, issue }

def entries : List Entry := [
  entry "missingchar-three-valued-logic" ["&(::Missing, ::Bool)", "|(::Missing, ::Bool)",
      "xor(::Missing, ::Bool)", "generated !(::Missing)", "nand", "nor"]
    "On Union{Bool,Missing}, &, |, xor, !, and the derived nand/nor forms follow three-valued logic. In particular, missing & false is false, missing | true is true, and a result is missing exactly when changing a missing operand can change its Boolean value."
    "doc/src/manual/missing.md:49-50,105-201; base/missing.jl:96-103,157-169"
    ``ThreeValuedLogic ``threeValuedLogic_proven,
  entry "missingchar-logic-algebra" ["&(::Missing, ::Bool)", "|(::Missing, ::Bool)"]
    "Three-valued &, |, and ! satisfy commutativity, associativity, De Morgan's laws, and distributivity on Union{Bool,Missing}."
    "doc/src/manual/missing.md:105-201; base/missing.jl:96-103,157-164"
    ``LogicAlgebra ``logicAlgebra_proven,
  entry "missingchar-comparison-propagates"
    ["==(::Missing, ::Missing)", "==(::Missing, ::Any)", "==(::Any, ::Missing)",
      "==(::Missing, ::WeakRef)", "==(::WeakRef, ::Missing)", "<(::Missing, ::Missing)",
      "<(::Missing, ::Any)", "<(::Any, ::Missing)", "!=", "<=", ">", ">="]
    "==, !=, <, <=, >, and >= return missing when either operand is missing; with two ordinary values they use the ordinary comparison methods."
    "doc/src/manual/missing.md:49-50; base/missing.jl:74-85; base/operators.jl:338,389,397,405,414"
    ``ComparisonPropagates ``comparisonPropagates_proven,
  entry "missingchar-isless-strict-weak" ["isless(::Missing, ::Any)", "isless(::Any, ::Missing)"]
    "isless on values that may be missing is a strict weak order whenever isless on ordinary values is a strict weak order."
    "base/operators.jl:206-217; base/missing.jl:86-88"
    ``IslessStrictWeak ``islessStrictWeak_proven,
  entry "missingchar-isless-missing-last" ["isless(::Missing, ::Missing)", "isless(::Missing, ::Any)", "isless(::Any, ::Missing)"]
    "isless(missing, x) is false for every x; isless(x, missing) is true for every non-missing x."
    "doc/src/manual/missing.md:90-92; base/missing.jl:86-88"
    ``MissingLast ``missingLast_proven,
  entry "missingchar-isless-trichotomy" ["isless(::Missing, ::Any)", "isequal(::Missing, ::Any)"]
    "For any two possibly-missing values, exactly one of isless(x,y), isless(y,x), or isequal(x,y) is true whenever that trichotomy holds for ordinary values."
    "base/operators.jl:206-217; base/missing.jl:80-88"
    ``IslessTrichotomy ``islessTrichotomy_proven,
  entry "missingchar-isequal-missing" ["isequal(::Missing, ::Missing)", "isequal(::Missing, ::Any)"]
    "isequal treats missing as equal only to missing, and extends any ordinary equivalence relation to values that may be missing."
    "doc/src/manual/missing.md:71-74; base/missing.jl:80-82"
    ``IsequalMissing ``isequalMissing_proven,
  entry "missingchar-minmax-missing" ["min(::Missing, ::Any)", "max(::Missing, ::Any)", "minmax(::Missing, ::Any)"]
    "min and max return missing if either argument is missing, and minmax returns the pair (min(x,y), max(x,y))."
    "base/operators.jl:540-588; base/missing.jl:129-136"
    ``MinMaxMissing ``minMaxMissing_proven,
  entry "missingchar-coalesce-first" ["coalesce", "@coalesce"]
    "coalesce returns its first non-missing argument, or missing if none exists; @coalesce returns the first non-missing evaluated argument, or missing."
    "doc/src/manual/missing.md:71-74; base/missing.jl:420-422,451-457"
    ``CoalesceFirst ``coalesceFirst_proven,
  entry "missing-arithmetic-propagation"
    ["+", "-", "*", "/", "^", "mod", "rem", "div"]
    "When either arithmetic operand is missing, or the base of an integer power is missing, coalesce skips the result and returns its next non-missing value."
    "base/missing.jl:116-127,154"
    ``ArithmeticPropagation ``arithmeticPropagation_proven,
  entry "missing-nonmissingtype-union"
    ["nonmissingtype(::Type)", "eltype(::Type{SkipMissing{T}})"]
    "For ordinary type members A and B, nonmissingtype(Union{Missing,A,B}) and eltype(SkipMissing{Union{Missing,A,B}}) are Union{A,B}; nonmissingtype(Any) remains Any."
    "nonmissingtype docstring; base/missing.jl:39,238; base/promotion.jl:166-177"
    ``NonmissingTypeUnion ``nonmissingTypeUnion_proven,
  entry "missingchar-skipmissing-iterate" ["iterate(::SkipMissing)"]
    "For a finite list-backed iterator, each iterate(::SkipMissing) call returns the first non-missing value from its remaining state and the suffix after that value; repeated calls yield non-missing values in order."
    "skipmissing docstring; base/missing.jl:185-193,240-250"
    ``SkipMissingIterate ``skipMissingIterate_proven,
  entry "missing-skipmissing-length" ["iterate(::SkipMissing)"]
    "For a finite list-backed parent iterator, a successful iterate(skipmissing(x)) yields one non-missing value and leaves a suffix whose non-missing count is the remaining number of outputs; exhaustion occurs exactly when the suffix has no non-missing values."
    "skipmissing docstring; base/missing.jl:240-250"
    ``SkipMissingLength ``skipMissingLength_proven,
  entry "missingchar-skipmissing-keys" ["keys(::SkipMissing)", "eachindex(::SkipMissing)",
      "getindex(::SkipMissing, ::Int)"]
    "keys(skipmissing(x)) and eachindex(skipmissing(x)) contain exactly the indices whose parent values are non-missing; indexing at such a key returns its value, while indexing an in-bounds missing value throws MissingException."
    "skipmissing docstring, base/missing.jl:186-188,252-261"
    ``SkipMissingKeys ``skipMissingKeys_proven,
  entry "missingchar-skipmissing-filter" ["filter(::Any, ::SkipMissing{<:AbstractArray})"]
    "filter(f, skipmissing(x)) returns exactly the non-missing elements of x for which f returns true, in order."
    "filter docstring; base/missing.jl:365-393"
    ``SkipMissingFilter ``skipMissingFilter_proven,
  entry "missingchar-skipmissing-getindex-nonscalar" ["getindex(::SkipMissing, I...)"]
    "Indexing skipmissing with a vector of indices never returns a missing value."
    "skipmissing docstring; base/missing.jl:257-261"
    ``SkipMissingGetindexNoMissing ``skipMissingGetindexNoMissing_refuted .refuted
    "none found (queries: skipmissing getindex range, skipmissing indexing vector, SkipMissing getindex, skipmissing index range missing); related #30606 (open)",
  entry "missingchar-skipmissing-findfirst" ["findfirst(::Function, ::SkipMissing)"]
    "findfirst returns the key of the first non-missing key/value pair whose value satisfies the predicate."
    "doc/src/manual/missing.md:356-360; base/missing.jl:253-256; base/abstractdict.jl:178; base/array.jl:2518-2523"
    ``SkipMissingFindFirst ``skipMissingFindFirst_proven,
  entry "missingchar-skipmissing-findlast" ["findlast(::Function, ::SkipMissing)"]
    "findlast over skipmissing returns the last parent index whose non-missing value satisfies the predicate."
    "doc/src/manual/missing.md:356-360; base/missing.jl:236,253-256; base/array.jl:2711-2716; base/iterators.jl:401-411,521-526"
    ``SkipMissingFindLast ``skipMissingFindLast_refuted .refuted
    "none found (queries: skipmissing findlast, findnext skipmissing, findprev skipmissing, skipmissing nextind, Cannot reverse zipped iterators); related #37014 (open)",
  entry "missingchar-skipmissing-mapreduce"
    ["mapreduce(::Any, ::Any, ::SkipMissing{<:AbstractArray})",
      "_mapreduce(::Any, ::Any, ::IndexLinear, ::SkipMissing{<:AbstractArray})",
      "_mapreduce(::Any, ::Any, ::IndexCartesian, ::SkipMissing)",
      "_mapreduce_impl_skipmissing(::Any, ::Any, ::SkipMissing, ::Integer, ::Integer)",
      "_mapreduce_impl_skipmissing(::Any, ::Any, ::SkipMissing{<:AbstractArray}, ::Integer, ::Integer, ::Int)"]
    "For arrays whose element type excludes Missing, mapreduce uses the raw reducer selected by the parent IndexStyle. If the element type includes Missing, linear arrays use the SkipMissing reducer and Cartesian arrays use mapfoldl."
    "doc/src/manual/missing.md:318-326; base/missing.jl:272-362"
    ``SkipMissingMapreduce ``skipMissingMapreduce_proven,
  entry "reducecov-float-missing-abstract" ["float(::AbstractArray{Union{T,Missing}})"]
    "float preserves every non-missing element up to the element's own float conversion."
    "float docstring; base/missing.jl:176-179"
    ``FloatArrayElementwise ``floatArrayExact_refuted .refuted
    "related #29693; none found for abstract Union element types",
  entry "missing-nonmissingtype-checked" ["nonmissingtype_checked(::Type)"]
    "On the source-backed type model, nonmissingtype_checked rejects Any and Missing, and removes Missing from Union{Missing,T} to return T."
    "base/missing.jl:41-46"
    ``NonmissingTypeChecked ``nonmissingTypeChecked_proven,
  entry "missing-predicates-propagate" ["ispositive(::Missing)", "isnegative(::Missing)",
      "isapprox(::Missing, ::Missing)", "isapprox(::Missing, ::Any)", "isapprox(::Any, ::Missing)"]
    "When ispositive, isnegative, or isapprox receives a missing operand, coalesce skips its result and returns the next non-missing value."
    "base/missing.jl:89-93"
    ``MissingPredicates ``missingPredicates_proven,
  entry "missing-operator-propagation" ["generated unary f(::Missing)",
      "clamp(::Missing, lo, hi)", "&(::Missing, ::Integer)", "&(::Integer, ::Missing)",
      "|(::Missing, ::Integer)", "|(::Integer, ::Missing)", "xor(::Missing, ::Integer)",
      "xor(::Integer, ::Missing)", "*(::Missing, ::Union{AbstractString,AbstractChar})",
      "*(::Union{AbstractString,AbstractChar}, ::Missing)",
      "round(::Missing, ::RoundingMode)", "round(::Type{>:Missing}, ::Missing, ::RoundingMode)"]
    "A missing unary operand, integer Boolean operand, text-multiplication operand, or round input is skipped by coalesce in favor of its next non-missing value."
    "base/missing.jl:96-104,137,143-144,160-166,170-174"
    ``MissingOperatorPropagation ``missingOperatorPropagation_proven,
  entry "missing-rounding-error" ["missing_conversion_msg",
      "round(::Type{T}, ::Missing, ::RoundingMode)"]
    "Rounding a missing value into a concrete target type raises MissingException with the message recommending Union{T,Missing}."
    "base/missing.jl:139-146"
    ``MissingRounding ``missingRounding_proven,
  entry "missing-display" ["show(::IO, ::Missing)", "showerror(::IO, ::MissingException)",
      "show(::IO, ::SkipMissing)"]
    "show prints `missing`, showerror prints `MissingException: ` followed by its message, and show on SkipMissing wraps the parent display in `skipmissing(...)`."
    "base/missing.jl:5,18-19,263-267"
    ``MissingDisplay ``missingDisplay_proven,
  entry "missing-type-functions" ["generated zero/one/oneunit(::Type{Any})",
      "generated zero/one/oneunit(::Type{Missing})",
      "generated zero/one/oneunit(::Type{T}) where T>:Missing",
      "generated float/real/complex(::Type{Any})",
      "generated float/real/complex(::Type{T}) where T>:Missing"]
    "The type-level zero, one, and oneunit methods return missing for Missing and select the underlying type for Union{Missing,T}; Any methods raise MethodError with argument tuple (Any,). Float, real, and complex on Any raise the same error, and on Union{Missing,T} they transform the non-missing type and preserve Missing."
    "base/missing.jl:106-112"
    ``MissingTypeFunctions ``missingTypeFunctions_proven,
]


end JuliaLean.Proofs.base.missing
