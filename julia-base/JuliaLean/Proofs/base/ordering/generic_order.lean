import JuliaLean.base.ordering
import JuliaLean.Proofs.base.ordering.value_order
/-! Generic coverage models for the `base/ordering.jl` overloads whose input
may contain user-defined `Ordering` subtypes.  The existing executable model
covers Base's concrete constructors; these wrappers retain an arbitrary
underlying order and its callbacks. -/

namespace JuliaLean.SortTuplesCov

open JuliaLean.Tuples (R Err)

def GenericReverseConstructorsCorrect : Prop :=
  (∀ (O : Type) (r : GenericReverse O), reverseUnwrap r = r.fwd) ∧
  (∀ (O : Type) isOrdering (o : O), isOrdering o = true →
    reverseWrap isOrdering o = .ok ⟨o⟩) ∧
  (∀ (O : Type) isOrdering (o : O), isOrdering o = false →
    reverseWrap isOrdering o = .error .typeError) ∧
  (∀ (F O : Type) reverse (o : GenericBy F O),
    reverseBy reverse o = do pure ⟨o.key, (← reverse o.order)⟩) ∧
  (∀ (O D : Type) reverse (o : GenericPerm O D),
    reversePerm reverse o = ⟨reverse o.order, o.data⟩) ∧
  (∀ (O R : Type) reverseOrdering (o : O),
    reverseMethod (R := R) reverseOrdering o = reverseOrdering o)

theorem genericReverseConstructorsCorrect : GenericReverseConstructorsCorrect := by
  refine ⟨fun _ _ => rfl, ?_, ?_, fun _ _ _ _ => rfl,
    fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩
  · intro O isOrdering o h
    simp [reverseWrap, h]
  · intro O isOrdering o h
    simp [reverseWrap, h]

def PermLtEvaluationCorrect : Prop :=
  ∀ (V : Type) get compare a b, permLtExact (V := V) get compare a b = do
    let da ← get a
    let db ← get b
    let ab ← compare da db >>= assertBool
    let ba ← compare db da >>= assertBool
    pure (ab || (!ba && decide (a < b)))

theorem permLtEvaluationCorrect : PermLtEvaluationCorrect := by
  unfold PermLtEvaluationCorrect
  intros
  rfl

def GenericOrdCorrect : Prop :=
  (∀ (O V : Type) (identity rev : Bool) (keyFn : V → V) (lt : V → V → Bool)
      (o : ExistingOrder O V),
    genericOrd true identity rev keyFn lt o =
      .ok (if rev then .reverse (genericBy identity keyFn o) else genericBy identity keyFn o)) ∧
  (∀ (O V : Type) (identity rev : Bool) (keyFn : V → V) (lt : V → V → Bool),
    genericOrd (O := O) false identity rev keyFn lt .forward =
      .ok (if rev then .reverse (genericBy identity keyFn (.lt lt))
        else genericBy identity keyFn (.lt lt))) ∧
  (∀ (O V : Type) (identity rev : Bool) (keyFn : V → V) (lt : V → V → Bool)
      (o : O),
    genericOrd false identity rev keyFn lt (.existing o) =
      .error "Passing both lt= and order= arguments is ambiguous; please pass order=Forward or order=Reverse (or leave default)")

theorem genericOrdCorrect : GenericOrdCorrect := by
  refine ⟨?_, ?_, ?_⟩
  · intro O V identity rev keyFn lt o
    cases rev <;> simp [genericOrd]
  · intro O V identity rev keyFn lt
    cases rev <;> simp [genericOrd]
  · intro O V identity rev keyFn lt o
    change Except.error _ = Except.error _
    rfl

def GenericOrdtypeCorrect : Prop :=
  (∀ (O V T : Type) ordtype (o : GenericReverse O) (vs : List V),
    ordtypeReverseGeneric (T := T) ordtype o vs = ordtype o.fwd vs) ∧
  (∀ (O V T : Type) ordtype (o : GenericPerm O (List V)) (vs : List V),
    ordtypePermGeneric (T := T) ordtype o vs = ordtype o.order o.data) ∧
  (∀ (V T : Type) (keyFn : V → R T) (anyT : T),
    ordtypeByGeneric (V := V) keyFn anyT [] = anyT) ∧
  (∀ (V T : Type) (keyFn : V → R T) (anyT : T) x xs (e : Err), keyFn x = .error e →
    ordtypeByGeneric (V := V) keyFn anyT (x :: xs) = anyT)

theorem genericOrdtypeCorrect : GenericOrdtypeCorrect := by
  refine ⟨fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl, by intros; rfl, ?_⟩
  intro V T keyFn anyT x xs e h
  simp [ordtypeByGeneric, h]

end JuliaLean.SortTuplesCov
