import JuliaLean.IteratorsCov.Base

/-!
# Three-valued `any` and `all` (`base/anyall.jl`)

Predicate results are represented explicitly so that the model includes the
Julia boolean-context `TypeError` for values other than `Bool` and `missing`.
-/

namespace JuliaLean.IteratorsCov

inductive Truth where
  | false_ | true_ | missing | other
  deriving Repr, DecidableEq

abbrev TruthResult := R (Option Bool)

/-- The generated `_any(f, itr, :)` loop at `base/anyall.jl:120-132`. -/
def anyLoop : Bool → List Truth → TruthResult
  | anymissing, [] => .ok (if anymissing then none else some false)
  | _, .true_ :: _ => .ok (some true)
  | anymissing, .false_ :: rest => anyLoop anymissing rest
  | _, .other :: _ => .error .typeError
  | _, .missing :: rest => anyLoop true rest

/-- The recursive `_any_tuple` methods at `base/anyall.jl:159-168`. -/
def anyTuple : Bool → List Truth → TruthResult
  | anymissing, [] => .ok (if anymissing then none else some false)
  | _, .true_ :: _ => .ok (some true)
  | anymissing, .false_ :: rest => anyTuple anymissing rest
  | _, .other :: _ => .error .typeError
  | _, .missing :: rest => anyTuple true rest

/-- The side-effect-free Bool tuple specialization at `base/anyall.jl:137-147`. -/
def anyBoolTuple : List Bool → Bool
  | [] => false
  | x :: xs => x || anyBoolTuple xs

/-- `any(itr) = any(identity, itr)` (41) and `any(f, itr) = _any(f, itr, :)`
(115), after applying the predicate. -/
def anyIdentity (xs : List Truth) : TruthResult := anyLoop false xs
def anyPred (f : α → Truth) (xs : List α) : TruthResult := anyLoop false (xs.map f)

/-- The generated `_all(f, itr, :)` loop at `base/anyall.jl:207-219`. -/
def allLoop : Bool → List Truth → TruthResult
  | anymissing, [] => .ok (if anymissing then none else some true)
  | _, .false_ :: _ => .ok (some false)
  | anymissing, .true_ :: rest => allLoop anymissing rest
  | _, .other :: _ => .error .typeError
  | _, .missing :: rest => allLoop true rest

/-- The recursive `_all_tuple` methods at `base/anyall.jl:245-257`. -/
def allTuple : Bool → List Truth → TruthResult
  | anymissing, [] => .ok (if anymissing then none else some true)
  | _, .false_ :: _ => .ok (some false)
  | anymissing, .true_ :: rest => allTuple anymissing rest
  | _, .other :: _ => .error .typeError
  | _, .missing :: rest => allTuple true rest

/-- The side-effect-free Bool tuple specialization at `base/anyall.jl:224-234`. -/
def allBoolTuple : List Bool → Bool
  | [] => true
  | x :: xs => x && allBoolTuple xs

/-- `all(itr) = all(identity, itr)` (80) and `all(f, itr) = _all(f, itr, :)`
(202), after applying the predicate. -/
def allIdentity (xs : List Truth) : TruthResult := allLoop false xs
def allPred (f : α → Truth) (xs : List α) : TruthResult := allLoop false (xs.map f)

/-- Every implementation path has the documented three-valued result; the
tuple recursion agrees with the generated loop, the Bool specializations are
ordinary disjunction/conjunction, and the public methods delegate exactly as
their one-line bodies state. -/
def AnyAllSemantics : Prop :=
  (∀ xs, anyIdentity xs = anyLoop false xs) ∧
  (∀ (α : Type) (f : α → Truth) xs, anyPred f xs = anyLoop false (xs.map f)) ∧
  (∀ seen xs, anyTuple seen xs = anyLoop seen xs) ∧
  (∀ xs, anyBoolTuple xs = xs.any id) ∧
  (∀ xs, allIdentity xs = allLoop false xs) ∧
  (∀ (β : Type) (f : β → Truth) xs, allPred f xs = allLoop false (xs.map f)) ∧
  (∀ seen xs, allTuple seen xs = allLoop seen xs) ∧
  (∀ xs, allBoolTuple xs = xs.all id)

theorem anyTuple_loop : ∀ seen xs, anyTuple seen xs = anyLoop seen xs := by
  intro seen xs
  induction xs generalizing seen with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [anyTuple, anyLoop, ih]

theorem allTuple_loop : ∀ seen xs, allTuple seen xs = allLoop seen xs := by
  intro seen xs
  induction xs generalizing seen with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [allTuple, allLoop, ih]

theorem anyBoolTuple_any : ∀ xs, anyBoolTuple xs = xs.any id := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [anyBoolTuple, ih, List.any]

theorem allBoolTuple_all : ∀ xs, allBoolTuple xs = xs.all id := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [allBoolTuple, ih, List.all]

theorem anyAllSemantics : AnyAllSemantics := by
  refine ⟨fun _ => rfl, fun _ _ _ => rfl, anyTuple_loop, anyBoolTuple_any,
    fun _ => rfl, fun _ _ _ => rfl, allTuple_loop, allBoolTuple_all⟩

end JuliaLean.IteratorsCov
