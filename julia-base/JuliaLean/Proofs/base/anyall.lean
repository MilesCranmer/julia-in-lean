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
    status := .todo, prop := ``AnyAllSpec, thm := none }
]

end JuliaLean.Proofs.base.anyall
