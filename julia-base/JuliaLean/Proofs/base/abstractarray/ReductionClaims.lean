import JuliaLean.base.abstractarray

namespace JuliaLean.Reduce

/-- `reduce(vcat, vs)` concatenates a nonempty vector of vectors; `reduce(hcat, vs)` puts
them side by side as columns when they have equal lengths and throws
`DimensionMismatch` otherwise. -/
def ReduceCatSpec : Prop :=
  ∀ vs : List (List Int), vs ≠ [] →
    Cat.reduceVcat vs = .ok vs.flatten ∧
    (∀ v1 rest, vs = v1 :: rest →
      ((∀ v ∈ vs, v.length = v1.length) → Cat.reduceHcat vs = .ok (v1.length, vs.length, vs.flatten)) ∧
      ((∃ v ∈ vs, v.length ≠ v1.length) → Cat.reduceHcat vs = .error .dimensionMismatch))

theorem foldl_append_acc {α : Type} :
    ∀ (vs : List (List α)) (acc : List α), vs.foldl (fun a v => a ++ v) acc = acc ++ vs.flatten
  | [], acc => by simp
  | v :: vs, acc => by
    rw [List.foldl_cons, foldl_append_acc vs, List.flatten_cons, List.append_assoc]

theorem reduceCatSpec_proven : ReduceCatSpec := by
  intro vs hne
  refine ⟨?_, ?_⟩
  · unfold Cat.reduceVcat
    simp only [hne, ite_false, foldl_append_acc, List.nil_append]
  · intro v1 rest hvs
    subst hvs
    refine ⟨?_, ?_⟩
    · intro hall
      simp only [Cat.reduceHcat]
      have : ((v1 :: rest).all fun v => decide (v.length = v1.length)) = true := by
        simp only [List.all_eq_true, decide_eq_true_eq]; exact hall
      simp only [this, ite_true, foldl_append_acc, List.nil_append]
    · intro ⟨v, hv, hlen⟩
      simp only [Cat.reduceHcat]
      have : ¬ ((v1 :: rest).all fun v => decide (v.length = v1.length)) = true := by
        simp only [List.all_eq_true, decide_eq_true_eq]
        intro hall; exact hlen (hall v hv)
      simp only [this, Bool.false_eq_true, ite_false]

end JuliaLean.Reduce
