import JuliaLean.SortTuplesCov.Ordering

/-! Generic coverage models for the `base/ordering.jl` overloads whose input
may contain user-defined `Ordering` subtypes.  The existing executable model
covers Base's concrete constructors; these wrappers retain an arbitrary
underlying order and its callbacks. -/

namespace JuliaLean.SortTuplesCov

open JuliaLean.Tuples (R Err)

structure GenericReverse (O : Type) where
  fwd : O

structure GenericBy (F O : Type) where
  key : F
  order : O

structure GenericPerm (O D : Type) where
  order : O
  data : D

/-- Constructors at `base/ordering.jl:46-47,110-111`. -/
def reverseUnwrap {O : Type} (rev : GenericReverse O) : O := rev.fwd
def reverseWrap {O : Type} (isOrdering : O → Bool) (o : O) : R (GenericReverse O) :=
  if isOrdering o then .ok ⟨o⟩ else .error .typeError
def reverseBy {F O : Type} (reverse : O → R O) (o : GenericBy F O) : R (GenericBy F O) := do
  pure ⟨o.key, (← reverse o.order)⟩
def reversePerm {O D : Type} (reverse : O → O) (o : GenericPerm O D) : GenericPerm O D :=
  ⟨reverse o.order, o.data⟩

/-- `reverse(o::Ordering) = ReverseOrdering(o)`, `base/ordering.jl:56`. -/
def reverseMethod {O R : Type} (reverseOrdering : O → R) (o : O) : R := reverseOrdering o

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

inductive Compared where
  | bool (value : Bool)
  | other

def assertBool : Compared → R Bool
  | .bool b => .ok b
  | .other => .error .typeError

/-- `lt(p::Perm,a,b)`, `base/ordering.jl:123-127`.  Both order comparisons
are evaluated and asserted Bool before eager `|` and `&` combine them. -/
def permLtExact {V : Type} (get : Int → R V) (compare : V → V → R Compared)
    (a b : Int) : R Bool := do
  let da ← get a
  let db ← get b
  let ab ← compare da db >>= assertBool
  let ba ← compare db da >>= assertBool
  pure (ab || (!ba && decide (a < b)))

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

inductive ExistingOrder (O V : Type) where
  | existing (o : O)
  | forward
  | reverseForward
  | by (f : V → V) (order : ExistingOrder O V)
  | lt (f : V → V → Bool)
  | reverse (order : ExistingOrder O V)

def genericBy {O V : Type} (identity : Bool) (f : V → V)
    (o : ExistingOrder O V) : ExistingOrder O V := if identity then o else .by f o

/-- `_ord`, `_by`, and `ord`, `base/ordering.jl:130-160`, retaining arbitrary
existing order values for the isless path. -/
def genericOrd {O V : Type} (islessArg identityBy reverseResult : Bool)
    (keyFn : V → V) (lt : V → V → Bool) (o : ExistingOrder O V) : Except String (ExistingOrder O V) :=
  let base : Except String (ExistingOrder O V) :=
    if islessArg then Except.ok (genericBy identityBy keyFn o) else
    match o with
    | .forward => Except.ok (genericBy identityBy keyFn (.lt lt))
    | .reverseForward => Except.ok (.reverse (genericBy identityBy keyFn (.lt lt)))
    | _ => Except.error "Passing both lt= and order= arguments is ambiguous; please pass order=Forward or order=Reverse (or leave default)"
  match base with
  | .error e => .error e
  | .ok result => .ok (if reverseResult then .reverse result else result)

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

/-- Generic `ordtype` overloads, `base/ordering.jl:170-174`. -/
def ordtypeReverseGeneric {O V T : Type} (ordtype : O → List V → T)
    (o : GenericReverse O) (vs : List V) : T := ordtype o.fwd vs
def ordtypePermGeneric {O V T : Type} (ordtype : O → List V → T)
    (o : GenericPerm O (List V)) (_ : List V) : T := ordtype o.order o.data
def ordtypeByGeneric {V T : Type} (keyFn : V → R T) (anyT : T) (vs : List V) : T :=
  match vs with
  | [] => anyT
  | x :: _ => match keyFn x with | .ok t => t | .error _ => anyT

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
