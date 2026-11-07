import JuliaLean.base.anyall
import JuliaLean.Registry.Types

/-!
# Properties of `base/anyall.jl`

The specification uses the sequence visited by iteration and records predicate outcomes without
using the implementation's accumulator. `Option.none` denotes `missing`; callback exceptions and
non-boolean predicate results remain distinct errors in the model.
-/

namespace JuliaLean.Proofs.base.anyall

open JuliaLean.Registry JuliaLean.base.anyall

def validPredicates {ε α : Type} (f : α → Except ε PredicateValue) (xs : List α) : Prop :=
  ∀ x ∈ xs, ∃ value, f x = .ok value ∧ value ≠ .other

def observed {ε α : Type} (f : α → Except ε PredicateValue) (xs : List α) :
    List PredicateValue :=
  xs.map (fun x => match f x with | .ok value => value | .error _ => .other)

def anyExpected (values : List PredicateValue) : Option Bool :=
  if values.any (fun value => match value with | .bool true => true | _ => false) then
    some true
  else if values.any (fun value => match value with | .missing => true | _ => false) then
    none
  else
    some false

def allExpected (values : List PredicateValue) : Option Bool :=
  if values.any (fun value => match value with | .bool false => true | _ => false) then
    some false
  else if values.any (fun value => match value with | .missing => true | _ => false) then
    none
  else
    some true

def AnyAllThreeValued : Prop :=
  (∀ {ε I α : Type} (items : I → List α) (f : α → Except ε PredicateValue) (itr : I),
    validPredicates f (items itr) →
      anyPredicate anyAny items f itr = .ok (anyExpected (observed f (items itr))) ∧
      allPredicate allAny items f itr = .ok (allExpected (observed f (items itr)))) ∧
  (∀ {ε α : Type} (f : α → Except ε PredicateValue) (itr : List α),
    validPredicates f itr →
      anyTupleLoop f itr .colon = .ok (anyExpected (observed f itr)) ∧
      allTupleLoop f itr .colon = .ok (allExpected (observed f itr))) ∧
  (∀ {ε α : Type} (f : α → Except ε PredicateValue) (isNTuple : Bool) (itr : List α),
    validPredicates f itr →
      anyTupleMethod anyTupleLoop anyTupleStep anyTupleDone f isNTuple itr =
        .ok (anyExpected (observed f itr)) ∧
      allTupleMethod allTupleLoop allTupleStep allTupleDone f isNTuple itr =
        .ok (allExpected (observed f itr))) ∧
  (∀ xs : List Bool,
    (anyBoolTuple xs .colon = true ↔ ∃ x ∈ xs, x = true) ∧
    (allBoolTuple xs .colon = true ↔ ∀ x ∈ xs, x = true)) ∧
  (∀ (ε : Type) (xs : List PredicateValue),
    (∀ x ∈ xs, x ≠ .other) →
      anyIdentity (anyValueCall (ε := ε) (I := List PredicateValue) id) xs =
        .ok (anyExpected xs) ∧
      allIdentity (allValueCall (ε := ε) (I := List PredicateValue) id) xs =
        .ok (allExpected xs)) ∧
  (∀ {ε : Type} (f : Bool → Except ε PredicateValue) (xs : List Bool),
    (∀ b, f b = .ok (.bool b)) →
      anyTupleMethod anyBoolTupleCall anyTupleStep anyTupleDone f true xs =
        .ok (anyExpected (observed f xs)) ∧
      allTupleMethod allBoolTupleCall allTupleStep allTupleDone f true xs =
        .ok (allExpected (observed f xs))) ∧
  (∀ {ε : Type} (f : Unit → Except ε PredicateValue),
    f () = .ok .other →
      anyPredicate anyAny id f [()] = .error (.typeError : AnyAllError ε) ∧
      allPredicate allAny id f [()] = .error (.typeError : AnyAllError ε) ∧
      anyTupleLoop f [()] .colon = .error (.typeError : AnyAllError ε) ∧
      allTupleLoop f [()] .colon = .error (.typeError : AnyAllError ε) ∧
      anyTupleStep anyTupleDone f false [()] = .error (.typeError : AnyAllError ε) ∧
      allTupleStep allTupleDone f false [()] = .error (.typeError : AnyAllError ε) ∧
      anyTupleMethod anyTupleLoop anyTupleStep anyTupleDone f false [()] =
        .error (.typeError : AnyAllError ε) ∧
      allTupleMethod allTupleLoop allTupleStep allTupleDone f false [()] =
        .error (.typeError : AnyAllError ε)) ∧
  (∀ {ε : Type} (f : Unit → Except ε PredicateValue) (e : ε),
    f () = .error e →
      anyPredicate anyAny id f [()] = .error (.predicate e) ∧
      allPredicate allAny id f [()] = .error (.predicate e) ∧
      anyTupleLoop f [()] .colon = .error (.predicate e) ∧
      allTupleLoop f [()] .colon = .error (.predicate e) ∧
      anyTupleStep anyTupleDone f false [()] = .error (.predicate e) ∧
      allTupleStep allTupleDone f false [()] = .error (.predicate e) ∧
      anyTupleMethod anyTupleLoop anyTupleStep anyTupleDone f false [()] =
        .error (.predicate e) ∧
      allTupleMethod allTupleLoop allTupleStep allTupleDone f false [()] =
        .error (.predicate e))

def AnyAllShortCircuit : Prop :=
  (∀ {ε α : Type} (f : α → Except ε PredicateValue) (before : List α) (decisive : α)
      (after : List α),
    (∀ x ∈ before, f x = .ok (.bool false) ∨ f x = .ok .missing) →
    f decisive = .ok (.bool true) →
    (∀ x ∈ after, ∃ e, f x = .error e) →
      anyPredicate anyAny id f (before ++ decisive :: after) = .ok (some true) ∧
      anyTupleMethod anyTupleLoop anyTupleStep anyTupleDone f false
        (before ++ decisive :: after) = .ok (some true)) ∧
  (∀ {ε α : Type} (f : α → Except ε PredicateValue) (before : List α) (decisive : α)
      (after : List α),
    (∀ x ∈ before, f x = .ok (.bool true) ∨ f x = .ok .missing) →
    f decisive = .ok (.bool false) →
    (∀ x ∈ after, ∃ e, f x = .error e) →
      allPredicate allAny id f (before ++ decisive :: after) = .ok (some false) ∧
      allTupleMethod allTupleLoop allTupleStep allTupleDone f false
        (before ++ decisive :: after) = .ok (some false))

def AnyAllSpec : Prop := AnyAllThreeValued ∧ AnyAllShortCircuit

/-! Nothing to promise: _any_tuple(_, anymissing::Bool)@168: the recursive terminal case is plumbing covered by the public three-valued result. -/
/-! Nothing to promise: _all_tuple(_, anymissing::Bool)@257: the recursive terminal case is plumbing covered by the public three-valued result. -/

end JuliaLean.Proofs.base.anyall

namespace JuliaLean.ChatGPT.Batch4.Group23
open JuliaLean.Proofs.base.anyall JuliaLean.base.anyall

def anyAllTrue : PredicateValue → Bool
  | .bool true => true
  | _ => false

def anyAllFalse : PredicateValue → Bool
  | .bool false => true
  | _ => false

def anyAllMissing : PredicateValue → Bool
  | .missing => true
  | _ => false

def anyExpectedWith (seen : Bool) (values : List PredicateValue) : Option Bool :=
  if values.any anyAllTrue then some true
  else if seen || values.any anyAllMissing then none
  else some false

def allExpectedWith (seen : Bool) (values : List PredicateValue) : Option Bool :=
  if values.any anyAllFalse then some false
  else if seen || values.any anyAllMissing then none
  else some true

theorem anyStepExpected {ε α : Type} (f : α → Except ε PredicateValue)
    (xs : List α) (hvalid : validPredicates f xs) (seen : Bool) :
    anyTupleStep anyTupleDone f seen xs = .ok (anyExpectedWith seen (observed f xs)) := by
  induction xs generalizing seen with
  | nil => cases seen <;> rfl
  | cons x xs ih =>
      have hx := hvalid x (List.mem_cons_self)
      have ht : validPredicates f xs := by
        intro y hy
        exact hvalid y (List.mem_cons_of_mem x hy)
      rcases hx with ⟨value, hvalue, hother⟩
      cases value with
      | bool b =>
          cases b <;>
            simp [anyTupleStep, hvalue, observed, anyExpectedWith,
              anyAllTrue, anyAllMissing, ih ht]
      | missing =>
          simp [anyTupleStep, hvalue, observed, anyExpectedWith,
            anyAllTrue, anyAllMissing, ih ht]
      | other => exact False.elim (hother rfl)

theorem allStepExpected {ε α : Type} (f : α → Except ε PredicateValue)
    (xs : List α) (hvalid : validPredicates f xs) (seen : Bool) :
    allTupleStep allTupleDone f seen xs = .ok (allExpectedWith seen (observed f xs)) := by
  induction xs generalizing seen with
  | nil => cases seen <;> rfl
  | cons x xs ih =>
      have hx := hvalid x (List.mem_cons_self)
      have ht : validPredicates f xs := by
        intro y hy
        exact hvalid y (List.mem_cons_of_mem x hy)
      rcases hx with ⟨value, hvalue, hother⟩
      cases value with
      | bool b =>
          cases b <;>
            simp [allTupleStep, hvalue, observed, allExpectedWith,
              anyAllFalse, anyAllMissing, ih ht]
      | missing =>
          simp [allTupleStep, hvalue, observed, allExpectedWith,
            anyAllFalse, anyAllMissing, ih ht]
      | other => exact False.elim (hother rfl)


theorem anyTupleLoopStepEq {ε α : Type} (f : α → Except ε PredicateValue)
    (xs : List α) (seen : Bool) :
    anyTupleLoop.loop f seen xs = anyTupleStep anyTupleDone f seen xs := by
  induction xs generalizing seen with
  | nil => rfl
  | cons x xs ih =>
      cases h : f x with
      | error e => simp only [anyTupleLoop.loop, anyTupleStep, h]
      | ok value =>
          cases value with
          | bool b => cases b <;> simp only [anyTupleLoop.loop, anyTupleStep, h, ih]
          | missing => simp only [anyTupleLoop.loop, anyTupleStep, h, ih]
          | other => simp only [anyTupleLoop.loop, anyTupleStep, h]


theorem anyAnyStepEq {ε α : Type} (f : α → Except ε PredicateValue)
    (xs : List α) (seen : Bool) :
    anyAny.loop f seen xs = anyTupleStep anyTupleDone f seen xs := by
  induction xs generalizing seen with
  | nil => rfl
  | cons x xs ih =>
      cases h : f x with
      | error e => simp only [anyAny.loop, anyTupleStep, h]
      | ok value =>
          cases value with
          | bool b => cases b <;> simp only [anyAny.loop, anyTupleStep, h, ih]
          | missing => simp only [anyAny.loop, anyTupleStep, h, ih]
          | other => simp only [anyAny.loop, anyTupleStep, h]


theorem allTupleLoopStepEq {ε α : Type} (f : α → Except ε PredicateValue)
    (xs : List α) (seen : Bool) :
    allTupleLoop.loop f seen xs = allTupleStep allTupleDone f seen xs := by
  induction xs generalizing seen with
  | nil => rfl
  | cons x xs ih =>
      cases h : f x with
      | error e => simp only [allTupleLoop.loop, allTupleStep, h]
      | ok value =>
          cases value with
          | bool b => cases b <;> simp only [allTupleLoop.loop, allTupleStep, h, ih]
          | missing => simp only [allTupleLoop.loop, allTupleStep, h, ih]
          | other => simp only [allTupleLoop.loop, allTupleStep, h]


theorem allAnyStepEq {ε α : Type} (f : α → Except ε PredicateValue)
    (xs : List α) (seen : Bool) :
    allAny.loop f seen xs = allTupleStep allTupleDone f seen xs := by
  induction xs generalizing seen with
  | nil => rfl
  | cons x xs ih =>
      cases h : f x with
      | error e => simp only [allAny.loop, allTupleStep, h]
      | ok value =>
          cases value with
          | bool b => cases b <;> simp only [allAny.loop, allTupleStep, h, ih]
          | missing => simp only [allAny.loop, allTupleStep, h, ih]
          | other => simp only [allAny.loop, allTupleStep, h]


theorem anyTupleMethodStepEq {ε α : Type} (f : α → Except ε PredicateValue)
    (xs : List α) (homogeneous : Bool) :
    anyTupleMethod anyTupleLoop anyTupleStep anyTupleDone f homogeneous xs =
      anyTupleStep anyTupleDone f false xs := by
  unfold anyTupleMethod
  split
  · exact anyTupleLoopStepEq f xs false
  · rfl

theorem allTupleMethodStepEq {ε α : Type} (f : α → Except ε PredicateValue)
    (xs : List α) (homogeneous : Bool) :
    allTupleMethod allTupleLoop allTupleStep allTupleDone f homogeneous xs =
      allTupleStep allTupleDone f false xs := by
  unfold allTupleMethod
  split
  · exact allTupleLoopStepEq f xs false
  · rfl

theorem anyPredicateExpected {ε I α : Type} (items : I → List α)
    (f : α → Except ε PredicateValue) (itr : I)
    (hvalid : validPredicates f (items itr)) :
    anyPredicate anyAny items f itr = .ok (anyExpected (observed f (items itr))) := by
  unfold anyPredicate anyAny
  rw [anyAnyStepEq, anyStepExpected f (items itr) hvalid false]
  rfl

theorem allPredicateExpected {ε I α : Type} (items : I → List α)
    (f : α → Except ε PredicateValue) (itr : I)
    (hvalid : validPredicates f (items itr)) :
    allPredicate allAny items f itr = .ok (allExpected (observed f (items itr))) := by
  unfold allPredicate allAny
  rw [allAnyStepEq, allStepExpected f (items itr) hvalid false]
  rfl

theorem anyBoolFold (xs : List Bool) (initial : Bool) :
    xs.foldl (fun r value => r || value) initial = (initial || xs.any id) := by
  induction xs generalizing initial with
  | nil => cases initial <;> rfl
  | cons b xs ih =>
      simp only [List.foldl_cons, ih, List.any_cons, id_eq]
      cases initial <;> cases b <;> rfl

theorem allBoolFold (xs : List Bool) (initial : Bool) :
    xs.foldl (fun r value => r && value) initial = (initial && xs.all id) := by
  induction xs generalizing initial with
  | nil => cases initial <;> rfl
  | cons b xs ih =>
      simp only [List.foldl_cons, ih, List.all_cons, id_eq]
      cases initial <;> cases b <;> rfl

theorem anyBoolTupleResult (xs : List Bool) : anyBoolTuple xs .colon = xs.any id := by
  exact anyBoolFold xs false

theorem allBoolTupleResult (xs : List Bool) : allBoolTuple xs .colon = xs.all id := by
  exact allBoolFold xs true


theorem anyExpectedBool (xs : List Bool) :
    anyExpected (xs.map PredicateValue.bool) = some (xs.any id) := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      cases b with
      | false => simpa [anyExpected] using ih
      | true => simp [anyExpected]

theorem allExpectedBool (xs : List Bool) :
    allExpected (xs.map PredicateValue.bool) = some (xs.all id) := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      cases b with
      | false => simp [allExpected]
      | true => simpa [allExpected] using ih

theorem observedBool {ε : Type} (f : Bool → Except ε PredicateValue)
    (xs : List Bool) (hf : ∀ b, f b = .ok (.bool b)) :
    observed f xs = xs.map PredicateValue.bool := by
  simp only [observed, hf]

theorem anyShortCircuitStep {ε α : Type} (f : α → Except ε PredicateValue)
    (before : List α) (decisive : α) (after : List α)
    (hbefore : ∀ x ∈ before, f x = .ok (.bool false) ∨ f x = .ok .missing)
    (hdecisive : f decisive = .ok (.bool true)) (seen : Bool) :
    anyTupleStep anyTupleDone f seen (before ++ decisive :: after) = .ok (some true) := by
  induction before generalizing seen with
  | nil => simp only [List.nil_append, anyTupleStep, hdecisive]
  | cons x before ih =>
      have hx := hbefore x List.mem_cons_self
      have ht : ∀ y ∈ before, f y = .ok (.bool false) ∨ f y = .ok .missing := by
        intro y hy
        exact hbefore y (List.mem_cons_of_mem x hy)
      rcases hx with hx | hx <;>
        simp only [List.cons_append, anyTupleStep, hx, ih ht]

theorem allShortCircuitStep {ε α : Type} (f : α → Except ε PredicateValue)
    (before : List α) (decisive : α) (after : List α)
    (hbefore : ∀ x ∈ before, f x = .ok (.bool true) ∨ f x = .ok .missing)
    (hdecisive : f decisive = .ok (.bool false)) (seen : Bool) :
    allTupleStep allTupleDone f seen (before ++ decisive :: after) = .ok (some false) := by
  induction before generalizing seen with
  | nil => simp only [List.nil_append, allTupleStep, hdecisive]
  | cons x before ih =>
      have hx := hbefore x List.mem_cons_self
      have ht : ∀ y ∈ before, f y = .ok (.bool true) ∨ f y = .ok .missing := by
        intro y hy
        exact hbefore y (List.mem_cons_of_mem x hy)
      rcases hx with hx | hx <;>
        simp only [List.cons_append, allTupleStep, hx, ih ht]


theorem anyAllThreeValuedProof : AnyAllThreeValued := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ε I α items f itr hvalid
    exact ⟨anyPredicateExpected items f itr hvalid,
      allPredicateExpected items f itr hvalid⟩
  · intro ε α f itr hvalid
    constructor
    · unfold anyTupleLoop
      rw [anyTupleLoopStepEq, anyStepExpected f itr hvalid false]
      rfl
    · unfold allTupleLoop
      rw [allTupleLoopStepEq, allStepExpected f itr hvalid false]
      rfl
  · intro ε α f isNTuple itr hvalid
    constructor
    · rw [anyTupleMethodStepEq, anyStepExpected f itr hvalid false]
      rfl
    · rw [allTupleMethodStepEq, allStepExpected f itr hvalid false]
      rfl
  · intro xs
    constructor
    · rw [anyBoolTupleResult]
      exact List.any_eq_true
    · rw [allBoolTupleResult]
      exact List.all_eq_true
  · intro ε xs hxs
    have hv : validPredicates
        (fun x : PredicateValue => (.ok (JuliaLean.base.operators.identity x) :
          Except ε PredicateValue)) xs := by
      intro x hx
      exact ⟨x, rfl, hxs x hx⟩
    constructor
    · have hs := anyPredicateExpected (I := List PredicateValue) id
        (fun x => (.ok (JuliaLean.base.operators.identity x) : Except ε PredicateValue)) xs hv
      simpa [anyIdentity, anyValueCall, observed, JuliaLean.base.operators.identity] using hs
    · have hs := allPredicateExpected (I := List PredicateValue) id
        (fun x => (.ok (JuliaLean.base.operators.identity x) : Except ε PredicateValue)) xs hv
      simpa [allIdentity, allValueCall, observed, JuliaLean.base.operators.identity] using hs
  · intro ε f xs hf
    constructor
    · change Except.ok (some (anyBoolTuple xs .colon)) =
        Except.ok (anyExpected (observed f xs))
      rw [observedBool f xs hf, anyExpectedBool, anyBoolTupleResult]
    · change Except.ok (some (allBoolTuple xs .colon)) =
        Except.ok (allExpected (observed f xs))
      rw [observedBool f xs hf, allExpectedBool, allBoolTupleResult]
  · intro ε f hf
    simp [anyPredicate, anyAny, anyAny.loop, allPredicate, allAny, allAny.loop,
      anyTupleLoop, anyTupleLoop.loop, allTupleLoop, allTupleLoop.loop,
      anyTupleStep, allTupleStep, anyTupleMethod, allTupleMethod, hf]
  · intro ε f e hf
    simp [anyPredicate, anyAny, anyAny.loop, allPredicate, allAny, allAny.loop,
      anyTupleLoop, anyTupleLoop.loop, allTupleLoop, allTupleLoop.loop,
      anyTupleStep, allTupleStep, anyTupleMethod, allTupleMethod, hf]

theorem anyAllShortCircuitProof : AnyAllShortCircuit := by
  constructor
  · intro ε α f before decisive after hbefore hdecisive _hafter
    constructor
    · unfold anyPredicate anyAny
      rw [anyAnyStepEq]
      exact anyShortCircuitStep f before decisive after hbefore hdecisive false
    · rw [anyTupleMethodStepEq]
      exact anyShortCircuitStep f before decisive after hbefore hdecisive false
  · intro ε α f before decisive after hbefore hdecisive _hafter
    constructor
    · unfold allPredicate allAny
      rw [allAnyStepEq]
      exact allShortCircuitStep f before decisive after hbefore hdecisive false
    · rw [allTupleMethodStepEq]
      exact allShortCircuitStep f before decisive after hbefore hdecisive false

/-- Three-valued results, callback errors, invalid Boolean-context results,
    tuple dispatch and prefix-based short-circuiting of the installed model. -/
theorem ReduceAnyall3vl_proven : JuliaLean.Proofs.base.anyall.AnyAllSpec := by
  exact ⟨anyAllThreeValuedProof, anyAllShortCircuitProof⟩

end JuliaLean.ChatGPT.Batch4.Group23

namespace JuliaLean.Proofs.base.anyall
open JuliaLean.Registry
def entries : List Entry := [
  { id := "reduce-anyall-3vl", juliaFile := "base/anyall.jl",
    juliaFns := ["any(itr)", "all(itr)", "any(f, itr)", "_any(f, itr::Tuple, ::Colon)",
      "_any(f, itr::Any, ::Colon)", "_any(::typeof(identity), itr::Tuple{Vararg{Bool}}, ::Colon)",
      "any(f, itr::Tuple)", "_any_tuple(f, anymissing::Bool, x, rest...)",
      "_any_tuple(_, anymissing::Bool)", "all(f, itr)", "_all(f, itr::Tuple, ::Colon)",
      "_all(f, itr::Any, ::Colon)", "_all(::typeof(identity), itr::Tuple{Vararg{Bool}}, ::Colon)",
      "all(f, itr::Tuple)", "_all_tuple(f, anymissing::Bool, x, rest...)",
      "_all_tuple(_, anymissing::Bool)"],
    statement := "any and all implement documented three-valued Bool/missing results, propagate errors, and stop after the first decisive true or false without evaluating later elements.",
    source := "base/anyall.jl:6-14, 44-52, 83-91, 171-179 (docstrings); non-Bool TypeError at base/anyall.jl:249",
    status := .proven, prop := ``AnyAllSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group23.ReduceAnyall3vl_proven }
]

end JuliaLean.Proofs.base.anyall
