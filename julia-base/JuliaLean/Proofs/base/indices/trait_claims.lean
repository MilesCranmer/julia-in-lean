import JuliaLean.base.indices

namespace JuliaLean.ReduceCov

open JuliaLean



/-- The `IndexStyle` docstring, `base/indices.jl:66-93`: the default is
`IndexCartesian()`, `Array`s and ranges are `IndexLinear`, an array has the style of
its type, and several arrays share `IndexLinear` exactly when every one of them is
`IndexLinear` (otherwise the common style is `IndexCartesian`). -/
def IndexStyleSpec : Prop :=
  indexStyle1 .plain = .cartesian ∧ indexStyle1 .array = .linear ∧ indexStyle1 .range = .linear ∧
  indexStyle1 .linearIndices = .linear ∧ indexStyle1 .bottom = .linear ∧
  (∀ s, indexStyle1 (.custom s) = s) ∧
  (∀ a rest, indexStyleN a rest = if (a :: rest).all (fun b => indexStyle1 b == .linear)
    then .linear else .cartesian) ∧
  (∃ f, indexStyleBottomSlurp = .error (.methodError f))

theorem indexStyleCombine_if (x : IndexStyleV) (c : Bool) :
    indexStyleCombine x (if c = true then .linear else .cartesian) =
      if (x == .linear && c) = true then .linear else .cartesian := by
  cases x <;> cases c <;> rfl

theorem indexStyleSpec_proven : IndexStyleSpec := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl, ?_, ⟨_, rfl⟩⟩
  intro a rest
  induction rest generalizing a with
  | nil =>
    simp only [indexStyleN, List.all_cons, List.all_nil, Bool.and_true]
    cases indexStyle1 a <;> rfl
  | cons b rest ih =>
    rw [indexStyleN, ih b]
    simp only [List.all_cons]
    exact indexStyleCombine_if _ _

end JuliaLean.ReduceCov
