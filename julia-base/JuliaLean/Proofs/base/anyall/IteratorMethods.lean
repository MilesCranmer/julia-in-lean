import JuliaLean.base.anyall

namespace JuliaLean.IteratorsCov

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
