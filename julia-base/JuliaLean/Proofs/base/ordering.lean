import JuliaLean.base.ordering
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.ordering

open JuliaLean.Registry
open JuliaLean.base.ordering

/-! The expected comparisons below are stated directly from ordering semantics. -/

def applyKey {A K : Type} (key : KeyArg A K) : A → OrderingResult K :=
  match key with
  | .identity => fun a => .ok a
  | .transform fn apply => fun a => apply fn a

def directOrderArg {A : Type} (reversed : Bool)
    (isless : A → A → OrderingResult Bool) : OrderArg A :=
  if reversed then .reverseForward Reverse isless else .forward Forward isless

def expectedOrdCompare {A K : Type}
    (lt : Sum (K → K → OrderingResult Bool) (K → K → OrderingResult Bool))
    (key : KeyArg A K) (orderReversed rev : Bool) (a b : A) : OrderingResult Bool :=
  match applyKey key a with
  | .error e => .error e
  | .ok ka =>
    match applyKey key b with
    | .error e => .error e
    | .ok kb =>
      if rev != orderReversed then
        (match lt with | .inl f => f | .inr f => f) kb ka
      else
        (match lt with | .inl f => f | .inr f => f) ka kb

def StrictWeak {A : Type} (lt : A → A → Bool) : Prop :=
  (∀ a, lt a a = false) ∧
  (∀ a b c, lt a b = true → lt b c = true → lt a c = true) ∧
  (∀ a b c, lt a b = false → lt b a = false → lt b c = false → lt c b = false →
    lt a c = false ∧ lt c a = false)

def resultBool : OrderingResult Bool → Bool
  | .ok value => value
  | .error _ => false

def ReverseCancellation : Prop :=
  ∀ (O A : Type) [Ordering O] (o : O)
    (lt : O → A → A → OrderingResult Bool) (less : A → A → Bool),
    (∀ a b, lt o a b = .ok (less a b)) →
    StrictWeak less →
    StrictWeak (fun a b => resultBool (lt
      (reverseOrdering_unwrap (reverseOrdering_unwrap
        (reverseOrdering (reverseOrdering o)))) a b))

def PermStability : Prop :=
  ∀ (O V K : Type) [Ordering O] (p : Perm O V)
    (lt : O → K → K → OrderingResult (Option Bool))
    (get : V → Int → OrderingResult K) (i j : Int) (x y : K),
    get p.data i = .ok x →
    get p.data j = .ok y →
    lt p.order x y = .ok (some false) →
    lt p.order y x = .ok (some false) →
    ltPerm p lt get (fun a b => .ok (decide (a < b))) i j =
      .ok (decide (i < j))

def ReverseOrderingPermLtSwap : Prop :=
  ∀ (O V I K : Type) [Ordering O] (p : Perm O V)
    (lt : O → K → K → OrderingResult (Option Bool)) (get : V → I → OrderingResult K)
    (indexLess : I → I → OrderingResult Bool) (i j : I) (x y : K),
    get p.data i = .ok x →
    get p.data j = .ok y →
    ltPerm (reverseOrdering_perm p)
      (fun o a b => ltReverse o lt a b) get indexLess i j =
    ltPerm p lt get indexLess j i

def ReverseOrderingCorrect : Prop :=
  (∀ (O A : Type) [Ordering O] (o : O)
      (lt : O → A → A → OrderingResult Bool) (less : A → A → Bool),
    (∀ a b, lt o a b = .ok (less a b)) →
    StrictWeak less →
    StrictWeak (fun a b => resultBool (ltReverse (reverseOrdering o) lt a b))) ∧
  (∀ (T O A K : Type) [Ordering O] (byValue : By T O)
      (apply : T → A → OrderingResult K)
      (compare : O → K → K → OrderingResult Bool) (less : K → K → Bool),
    (∀ a, ∃ key, apply byValue.callable a = .ok key) →
    (∀ a b, compare byValue.order a b = .ok (less a b)) →
    StrictWeak less →
    StrictWeak (fun a b =>
      match ltBy (reverseOrdering_by byValue) apply
        (fun reversed x y => ltReverse reversed compare x y) a b with
      | .ok result => result
      | .error _ => false))


def StrictWeakOn {A : Type} (valid : A → Prop) (lt : A → A → Bool) : Prop :=
  (∀ a, valid a → lt a a = false) ∧
  (∀ a b c, valid a → valid b → valid c → lt a b = true → lt b c = true → lt a c = true) ∧
  (∀ a b c, valid a → valid b → valid c →
    lt a b = false → lt b a = false → lt b c = false → lt c b = false →
    lt a c = false ∧ lt c a = false)

def StrictTotalOn {A : Type} (valid : A → Prop) (lt : A → A → Bool) : Prop :=
  (∀ a, valid a → lt a a = false) ∧
  (∀ a b c, valid a → valid b → valid c → lt a b = true → lt b c = true → lt a c = true) ∧
  (∀ a b, valid a → valid b → a ≠ b → lt a b = true ∨ lt b a = true) ∧
  (∀ a b, valid a → valid b → ¬ (lt a b = true ∧ lt b a = true))

def indexLessValue {I : Type} (lt : I → I → OrderingResult Bool) : I → I → Bool :=
  fun i j => match lt i j with | .ok result => result | .error _ => false

def dataLess {O K : Type} (lt : O → K → K → OrderingResult (Option Bool))
    (order : O) : K → K → Bool :=
  fun a b => match lt order a b with
    | .ok (.some result) => result
    | .ok .none | .error _ => false

def permLess {O V I K : Type} [Ordering O] (p : Perm O V)
    (lt : O → K → K → OrderingResult (Option Bool)) (get : V → I → OrderingResult K)
    (indexLess : I → I → OrderingResult Bool) : I → I → Bool :=
  fun i j => match ltPerm p lt get indexLess i j with
    | .ok result => result
    | .error _ => false

def PermLtCorrect : Prop :=
  (∀ (O V K : Type) [Ordering O] (p : Perm O V)
    (lt : O → K → K → OrderingResult (Option Bool)) (get : V → Int → OrderingResult K)
    (i j : Int) (x y : K) (ab ba : Bool),
    get p.data i = .ok x →
    get p.data j = .ok y →
    lt p.order x y = .ok (some ab) →
    lt p.order y x = .ok (some ba) →
    ltPerm p lt get (fun a b => .ok (decide (a < b))) i j =
      .ok (if ab then true else if ba then false else decide (i < j))) ∧
  (∀ (O V K : Type) [Ordering O] (p : Perm O V)
    (lt : O → K → K → OrderingResult (Option Bool)) (get : V → Int → OrderingResult K)
    (valid : Int → Prop),
    (∀ i, valid i → ∃ x, get p.data i = .ok x) →
    (∀ x y, ∃ result, lt p.order x y = .ok (some result)) →
    StrictWeak (dataLess lt p.order) →
    StrictWeakOn valid (permLess p lt get
      (fun i j => .ok (decide (i < j))))) ∧
  PermStability

def PermLtEvaluationCorrect : Prop :=
  ∀ (O V I K : Type) [Ordering O] (p : Perm O V)
    (lt : O → K → K → OrderingResult (Option Bool)) (get : V → I → OrderingResult K)
    (indexLess : I → I → OrderingResult Bool) (i j : I),
    (∀ e, get p.data i = .error e →
      ltPerm p lt get indexLess i j = .error e) ∧
    (∀ x e, get p.data i = .ok x → get p.data j = .error e →
      ltPerm p lt get indexLess i j = .error e) ∧
    (∀ x y e, get p.data i = .ok x → get p.data j = .ok y → lt p.order x y = .error e →
      ltPerm p lt get indexLess i j = .error e) ∧
    (∀ x y, get p.data i = .ok x → get p.data j = .ok y →
      lt p.order x y = .ok .none →
      ltPerm p lt get indexLess i j = .error .typeError) ∧
    (∀ x y ab e, get p.data i = .ok x → get p.data j = .ok y →
      lt p.order x y = .ok (some ab) → lt p.order y x = .error e →
      ltPerm p lt get indexLess i j = .error e) ∧
    (∀ x y ab, get p.data i = .ok x → get p.data j = .ok y →
      lt p.order x y = .ok (some ab) → lt p.order y x = .ok .none →
      ltPerm p lt get indexLess i j = .error .typeError) ∧
    (∀ x y ab ba e, get p.data i = .ok x → get p.data j = .ok y →
      lt p.order x y = .ok (some ab) → lt p.order y x = .ok (some ba) →
      indexLess i j = .error e →
      ltPerm p lt get indexLess i j = .error e)


def reverseComparison {O A : Type} [Ordering O] (o : ReverseOrdering O)
    (lt : O → A → A → OrderingResult Bool) : A → A → Bool :=
  fun a b => resultBool (ltReverse o lt a b)

def byComparison {T O A K : Type} (o : By T O)
    (apply : T → A → OrderingResult K) (lt : O → K → K → OrderingResult Bool) :
    A → A → Bool :=
  fun a b => resultBool (ltBy o apply lt a b)

def LtMethodsCorrect : Prop :=
  (∀ (A : Type) (o : ForwardOrdering) (isless : A → A → OrderingResult Bool)
    (less : A → A → Bool),
    (∀ a b, isless a b = .ok (less a b)) →
    StrictWeak less →
    StrictWeak (fun a b => resultBool (ltForward o isless a b))) ∧
  (∀ (O A : Type) [Ordering O] (o : ReverseOrdering O)
    (lt : O → A → A → OrderingResult Bool) (less : A → A → Bool),
    (∀ a b, lt o.fwd a b = .ok (less a b)) →
    StrictWeak less →
    StrictWeak (reverseComparison o lt)) ∧
  (∀ (T O A K : Type) (o : By T O) (apply : T → A → OrderingResult K)
    (lt : O → K → K → OrderingResult Bool) (less : K → K → Bool),
    (∀ a, ∃ key, apply o.callable a = .ok key) →
    (∀ a b, lt o.order a b = .ok (less a b)) →
    StrictWeak less →
    StrictWeak (byComparison o apply lt)) ∧
  (∀ (A : Type) (o : Lt A) (less : A → A → Bool),
    (∀ a b, o.lt a b = .ok (less a b)) →
    StrictWeak less →
    StrictWeak (fun a b => resultBool (ltLt o a b)))

def ByDefaultUsesForward : Prop :=
  (∀ (A K : Type) (key : A → K), (byDefault key).order = Forward) ∧
  (∀ (A K : Type) (key : A → K)
      (isless : K → K → OrderingResult Bool) (less : K → K → Bool),
    (∀ a b, isless a b = .ok (less a b)) →
    StrictWeak less →
    StrictWeak (fun a b => resultBool
      (ltBy (byDefault key) (fun fn x => .ok (fn x))
        (fun order x y => ltForward order isless x y) a b)))

def ReverseDefaultUsesIsless : Prop :=
  reverseOrdering_default.fwd = Forward ∧
  (∀ (A : Type) (isless : A → A → OrderingResult Bool) (less : A → A → Bool),
    (∀ a b, isless a b = .ok (less a b)) →
    StrictWeak less →
    StrictWeak (reverseComparison reverseOrdering_default (fun _ x y => isless x y)))

def OrdCombinations : Prop :=
  (∀ (A K : Type)
    (isless custom : K → K → OrderingResult Bool) (key : KeyArg A K)
    (useCustom orderReversed : Bool) (a b : A),
    let lt : Sum (K → K → OrderingResult Bool) (K → K → OrderingResult Bool) :=
      if useCustom then .inr custom else .inl isless
    let order := directOrderArg orderReversed isless
    Except.bind (ordNothing lt key () order) (fun o => ordCompare o a b) =
      expectedOrdCompare lt key orderReversed false a b ∧
    (∀ rev : Bool,
      Except.bind (ordBool lt key rev order) (fun o => ordCompare o a b) =
        expectedOrdCompare lt key orderReversed rev a b)) ∧
  (∀ (A K O : Type) [Ordering O] (isless : K → K → OrderingResult Bool)
    (key : KeyArg A K) (order : O) (compare : O → K → K → OrderingResult Bool)
    (a b : A),
    let lt : Sum (K → K → OrderingResult Bool) (K → K → OrderingResult Bool) :=
      .inl (fun x y => compare order x y)
    Except.bind (ordNothing (.inl isless) key () (.other order compare))
      (fun o => ordCompare o a b) = expectedOrdCompare lt key false false a b ∧
    ∀ rev : Bool,
      Except.bind (ordBool (.inl isless) key rev (.other order compare))
        (fun o => ordCompare o a b) =
          expectedOrdCompare lt key false rev a b)

def OrdCorrect : Prop := OrdCombinations

def OrdRejects : Prop :=
  ∀ (A K O : Type) [Ordering O] (custom : K → K → OrderingResult Bool)
    (key : KeyArg A K) (order : O) (compare : O → K → K → OrderingResult Bool)
    (rev : Bool),
    ordNothing (.inr custom) key () (.other order compare) =
      .error (.errorException
        "Passing both lt= and order= arguments is ambiguous; please pass order=Forward or order=Reverse (or leave default)") ∧
    ordBool (.inr custom) key rev (.other order compare) =
      .error (.errorException
        "Passing both lt= and order= arguments is ambiguous; please pass order=Forward or order=Reverse (or leave default)")
def OrdtypeCorrect : Prop :=
  (∀ (T A K O V : Type) (getFirst : V → OrderingResult A)
      (apply : T → A → OrderingResult K) (typeof : K → TypeToken) (byValue : By T O)
      (vs ws : V),
    getFirst vs = getFirst ws →
    ordtypeBy getFirst apply typeof byValue vs =
      ordtypeBy getFirst apply typeof byValue ws) ∧
  (∀ (T A K O V : Type) (getFirst : V → OrderingResult A)
      (apply : T → A → OrderingResult K) (typeof : K → TypeToken) (byValue : By T O)
      (vs : V) (x : A) (key : K),
    getFirst vs = .ok x →
    apply byValue.callable x = .ok key →
    ordtypeBy getFirst apply typeof byValue vs = typeof key) ∧
  (∀ (T A K O V : Type) (getFirst : V → OrderingResult A)
      (apply : T → A → OrderingResult K) (typeof : K → TypeToken) (byValue : By T O)
      (vs : V) (e : OrderingError),
    getFirst vs = .error e →
    ordtypeBy getFirst apply typeof byValue vs = anyType) ∧
  (∀ (T A K O V : Type) (getFirst : V → OrderingResult A)
      (apply : T → A → OrderingResult K) (typeof : K → TypeToken) (byValue : By T O)
      (vs : V) (x : A) (e : OrderingError),
    getFirst vs = .ok x →
    apply byValue.callable x = .error e →
    ordtypeBy getFirst apply typeof byValue vs = anyType)

/-! ## Proofs -/

theorem reverseCancellation_proven : ReverseCancellation := by
  intro O A _ o lt less hcmp hsw
  have hfn :
      (fun a b => resultBool (lt
        (reverseOrdering_unwrap (reverseOrdering_unwrap
          (reverseOrdering (reverseOrdering o)))) a b)) = less := by
    funext a b
    simp [resultBool, reverseOrdering_unwrap, reverseOrdering,
      reverseOrdering_wrap, hcmp]
  rw [hfn]
  exact hsw

theorem reverseOrderingCorrect_proven : ReverseOrderingCorrect := by
  refine ⟨?_, ?_⟩
  · intro O A _ o lt less hcmp hsw
    have hfn : (fun a b => resultBool (ltReverse (reverseOrdering o) lt a b)) =
        fun a b => less b a := by
      funext a b
      simp [resultBool, ltReverse, reverseOrdering, reverseOrdering_wrap, hcmp]
    rw [hfn]
    rcases hsw with ⟨hirr, htrans, hincomp⟩
    refine ⟨?_, ?_, ?_⟩
    · intro a
      exact hirr a
    · intro a b c hab hbc
      exact htrans c b a hbc hab
    · intro a b c hab hba hbc hcb
      exact hincomp c b a hbc hcb hab hba
  · intro T O A K _ byValue apply compare less happly hcmp hsw
    classical
    let key : A → K := fun a => Classical.choose (happly a)
    have hkey : ∀ a, apply byValue.callable a = .ok (key a) := by
      intro a
      exact Classical.choose_spec (happly a)
    have hfn :
        (fun a b => match ltBy (reverseOrdering_by byValue) apply
          (fun reversed x y => ltReverse reversed compare x y) a b with
          | .ok result => result
          | .error _ => false) =
        fun a b => less (key b) (key a) := by
      funext a b
      simp [ltBy, reverseOrdering_by, reverseOrdering_wrap, hkey, ltReverse, hcmp]
    rw [hfn]
    have hrev : StrictWeak (fun x y => less y x) := by
      rcases hsw with ⟨hirr, htrans, hincomp⟩
      refine ⟨?_, ?_, ?_⟩
      · intro x
        exact hirr x
      · intro x y z hxy hyz
        exact htrans z y x hyz hxy
      · intro x y z hxy hyx hyz hzy
        exact hincomp z y x hyz hzy hxy hyx
    rcases hrev with ⟨hirr, htrans, hincomp⟩
    refine ⟨?_, ?_, ?_⟩
    · intro a
      exact hirr (key a)
    · intro a b c hab hbc
      exact htrans (key a) (key b) (key c) hab hbc
    · intro a b c hab hba hbc hcb
      exact hincomp (key a) (key b) (key c) hab hba hbc hcb

private theorem strictWeakReverse {A : Type} {less : A → A → Bool}
    (h : StrictWeak less) : StrictWeak (fun a b => less b a) := by
  rcases h with ⟨hirr, htrans, hincomp⟩
  refine ⟨?_, ?_, ?_⟩
  · intro a
    exact hirr a
  · intro a b c hab hbc
    exact htrans c b a hbc hab
  · intro a b c hab hba hbc hcb
    exact hincomp c b a hbc hcb hab hba

private theorem strictWeakComap {A K : Type} (key : A → K) {less : K → K → Bool}
    (h : StrictWeak less) : StrictWeak (fun a b => less (key a) (key b)) := by
  rcases h with ⟨hirr, htrans, hincomp⟩
  refine ⟨?_, ?_, ?_⟩
  · intro a
    exact hirr (key a)
  · intro a b c hab hbc
    exact htrans (key a) (key b) (key c) hab hbc
  · intro a b c hab hba hbc hcb
    exact hincomp (key a) (key b) (key c) hab hba hbc hcb

theorem ltMethodsCorrect_proven : LtMethodsCorrect := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A o isless less hcmp hsw
    have hfn : (fun a b => resultBool (ltForward o isless a b)) = less := by
      funext a b
      simp [resultBool, ltForward, hcmp]
    rw [hfn]
    exact hsw
  · intro O A _ o lt less hlt hsw
    have hcmp : ∀ a b, reverseComparison o lt a b = less b a := by
      intro a b
      simp [reverseComparison, resultBool, ltReverse, hlt]
    have hfn : reverseComparison o lt = fun a b => less b a := by
      funext a b
      exact hcmp a b
    rw [hfn]
    exact strictWeakReverse hsw
  · intro T O A K o apply lt less happly hlt hsw
    classical
    let key : A → K := fun a => Classical.choose (happly a)
    have hkey : ∀ a, apply o.callable a = .ok (key a) := by
      intro a
      exact Classical.choose_spec (happly a)
    have hcmp : ∀ a b, byComparison o apply lt a b = less (key a) (key b) := by
      intro a b
      simp [byComparison, resultBool, ltBy, hkey, hlt]
    have hfn : byComparison o apply lt = fun a b => less (key a) (key b) := by
      funext a b
      exact hcmp a b
    rw [hfn]
    exact strictWeakComap key hsw
  · intro A o less hcmp hsw
    have hfn : (fun a b => resultBool (ltLt o a b)) = less := by
      funext a b
      simp [resultBool, ltLt, hcmp]
    rw [hfn]
    exact hsw

theorem byDefaultUsesForward_proven : ByDefaultUsesForward := by
  refine ⟨?_, ?_⟩
  · intro A K key
    rfl
  · intro A K key isless less hcmp hsw
    have hfn : (fun a b => resultBool
        (ltBy (byDefault key) (fun fn x => .ok (fn x))
          (fun order x y => ltForward order isless x y) a b)) =
        fun a b => less (key a) (key b) := by
      funext a b
      simp [resultBool, ltBy, byDefault, Forward, ltForward, hcmp]
    rw [hfn]
    exact strictWeakComap key hsw

theorem reverseDefaultUsesIsless_proven : ReverseDefaultUsesIsless := by
  constructor
  · rfl
  · intro A isless less hcmp hsw
    have hfn : reverseComparison reverseOrdering_default
        (fun _ x y => isless x y) = fun a b => less b a := by
      funext a b
      simp [reverseComparison, resultBool, ltReverse, hcmp]
    rw [hfn]
    exact strictWeakReverse hsw

theorem ordRejects_proven : OrdRejects := by
  intro A K O _ custom key order compare rev
  constructor <;> rfl

theorem ordtypeCorrect_proven : OrdtypeCorrect := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro T A K O V getFirst apply typeof byValue vs ws h
    simp [ordtypeBy, h]
  · intro T A K O V getFirst apply typeof byValue vs x key hget happly
    simp [ordtypeBy, hget, happly]
  · intro T A K O V getFirst apply typeof byValue vs e h
    simp [ordtypeBy, h]
  · intro T A K O V getFirst apply typeof byValue vs x e hget happly
    simp [ordtypeBy, hget, happly]

theorem permStability_proven : PermStability := by
  intro O V K _ p lt get i j x y h1 h2 h3 h4
  simp [ltPerm, assertBool, h1, h2, h3, h4]

theorem permLtEvaluationCorrect_proven : PermLtEvaluationCorrect := by
  intro O V I K _ p lt get indexLess i j
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e h
    simp [ltPerm, h]
  · intro x e h1 h2
    simp [ltPerm, h1, h2]
  · intro x y e h1 h2 h3
    simp [ltPerm, h1, h2, h3]
  · intro x y h1 h2 h3
    simp [ltPerm, assertBool, h1, h2, h3]
  · intro x y ab e h1 h2 h3 h4
    simp [ltPerm, assertBool, h1, h2, h3, h4]
  · intro x y ab h1 h2 h3 h4
    simp [ltPerm, assertBool, h1, h2, h3, h4]
  · intro x y ab ba e h1 h2 h3 h4 h5
    simp [ltPerm, assertBool, h1, h2, h3, h4, h5]
private def lexLess {K : Type} (less : K → K → Bool) (key : Int → K) (i j : Int) : Bool :=
  less (key i) (key j) || (!less (key j) (key i) && decide (i < j))

private theorem lexTrueIff {K : Type} (less : K → K → Bool) (key : Int → K) (i j : Int) :
    lexLess less key i j = true ↔
      less (key i) (key j) = true ∨
        (less (key i) (key j) = false ∧ less (key j) (key i) = false ∧ i < j) := by
  cases hxy : less (key i) (key j) <;> cases hyx : less (key j) (key i) <;>
    simp [lexLess, hxy, hyx, decide_eq_true_eq]

private theorem lexFalseBoth {K : Type} (less : K → K → Bool)
    (key : Int → K) (i j : Int)
    (hij : lexLess less key i j = false) (hji : lexLess less key j i = false) :
    less (key i) (key j) = false ∧ less (key j) (key i) = false ∧ i = j := by
  cases hab : less (key i) (key j) <;> cases hba : less (key j) (key i) <;>
    simp [lexLess, hab, hba, decide_eq_false_iff_not] at hij hji ⊢ <;> omega

private theorem lessPreserveRight {K : Type} {less : K → K → Bool}
    (hsw : StrictWeak less) {x y z : K}
    (hxy : less x y = true) (hyz : less y z = false) (hzy : less z y = false) :
    less x z = true := by
  rcases hsw with ⟨_, htrans, hincomp⟩
  cases hxz : less x z with
  | true => rfl
  | false =>
    by_cases hzx : less z x = true
    · have hzy' := htrans z x y hzx hxy
      rw [hzy] at hzy'
      cases hzy'
    · have hzx' : less z x = false := Bool.eq_false_iff.mpr hzx
      have hEq := hincomp x z y hxz hzx' hzy hyz
      have hcontra : less x y = false := hEq.1
      rw [hxy] at hcontra
      cases hcontra

private theorem lessPreserveLeft {K : Type} {less : K → K → Bool}
    (hsw : StrictWeak less) {x y z : K}
    (hxy : less x y = false) (hyx : less y x = false) (hyz : less y z = true) :
    less x z = true := by
  rcases hsw with ⟨_, htrans, hincomp⟩
  cases hxz : less x z with
  | true => rfl
  | false =>
    by_cases hzx : less z x = true
    · have hyx' := htrans y z x hyz hzx
      rw [hyx] at hyx'
      cases hyx'
    · have hzx' : less z x = false := Bool.eq_false_iff.mpr hzx
      have hEq := hincomp y x z hyx hxy hxz hzx'
      have hcontra : less y z = false := hEq.1
      rw [hyz] at hcontra
      cases hcontra

private theorem lexStrictWeak {K : Type} (less : K → K → Bool)
    (hsw : StrictWeak less) (key : Int → K) : StrictWeak (lexLess less key) := by
  have hsw' := hsw
  rcases hsw with ⟨hirr, htrans, hincomp⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simp [lexLess, hirr (key i)]
  · intro i j k hij hjk
    have hij' := (lexTrueIff less key i j).mp hij
    have hjk' := (lexTrueIff less key j k).mp hjk
    rcases hij' with hab | ⟨hab, hba, hijlt⟩
    · rcases hjk' with hbc | ⟨hbc, hcb, hjklt⟩
      · apply (lexTrueIff less key i k).2
        exact Or.inl (htrans (key i) (key j) (key k) hab hbc)
      · apply (lexTrueIff less key i k).2
        exact Or.inl (lessPreserveRight hsw' hab hbc hcb)
    · rcases hjk' with hbc | ⟨hbc, hcb, hjklt⟩
      · apply (lexTrueIff less key i k).2
        exact Or.inl (lessPreserveLeft hsw' hab hba hbc)
      · apply (lexTrueIff less key i k).2
        right
        refine ⟨?_, ?_, ?_⟩
        · exact (hincomp (key i) (key j) (key k) hab hba hbc hcb).1
        · exact (hincomp (key i) (key j) (key k) hab hba hbc hcb).2
        · omega
  · intro i j k hij hji hjk hkj
    have heqij := lexFalseBoth less key i j hij hji
    have heqjk := lexFalseBoth less key j k hjk hkj
    have hik : i = k := heqij.2.2.trans heqjk.2.2
    subst k
    constructor <;> simp [lexLess, hirr]

theorem permLtCorrect_proven : PermLtCorrect := by
  refine ⟨?_, ?_, ?_⟩
  · intro O V K _ p lt get i j x y ab ba hgeti hgetj hltab hltba
    cases ab <;> cases ba <;> simp [ltPerm, assertBool, hgeti, hgetj, hltab, hltba]
  · intro O V K _ p lt get valid hget hlt hsw
    classical
    by_cases hany : ∃ i, valid i
    · obtain ⟨i0, hi0⟩ := hany
      obtain ⟨x0, hx0⟩ := hget i0 hi0
      let key : Int → K := fun i =>
        if hi : valid i then Classical.choose (hget i hi) else x0
      have hkey : ∀ i, valid i → get p.data i = .ok (key i) := by
        intro i hi
        simpa [key, hi] using (Classical.choose_spec (hget i hi))
      have hperm : ∀ i j, valid i → valid j →
          permLess p lt get (fun a b => .ok (decide (a < b))) i j =
            lexLess (dataLess lt p.order) key i j := by
        intro i j hi hj
        have hgeti := hkey i hi
        have hgetj := hkey j hj
        obtain ⟨ab, hltab⟩ := hlt (key i) (key j)
        obtain ⟨ba, hltba⟩ := hlt (key j) (key i)
        simp [permLess, lexLess, ltPerm, assertBool, dataLess, hgeti, hgetj, hltab, hltba]
      have hlex := lexStrictWeak (dataLess lt p.order) hsw key
      rcases hlex with ⟨hirr, htrans, hincomp⟩
      refine ⟨?_, ?_, ?_⟩
      · intro i hi
        rw [hperm i i hi hi]
        exact hirr i
      · intro i j k hi hj hk hij hjk
        have hij' : lexLess (dataLess lt p.order) key i j = true := by
          rw [← hperm i j hi hj]
          exact hij
        have hjk' : lexLess (dataLess lt p.order) key j k = true := by
          rw [← hperm j k hj hk]
          exact hjk
        have hik' := htrans i j k hij' hjk'
        rw [hperm i k hi hk]
        exact hik'
      · intro i j k hi hj hk hij hji hjk hkj
        have hij' : lexLess (dataLess lt p.order) key i j = false := by
          rw [← hperm i j hi hj]
          exact hij
        have hji' : lexLess (dataLess lt p.order) key j i = false := by
          rw [← hperm j i hj hi]
          exact hji
        have hjk' : lexLess (dataLess lt p.order) key j k = false := by
          rw [← hperm j k hj hk]
          exact hjk
        have hkj' : lexLess (dataLess lt p.order) key k j = false := by
          rw [← hperm k j hk hj]
          exact hkj
        have hik' := hincomp i j k hij' hji' hjk' hkj'
        constructor
        · rw [hperm i k hi hk]
          exact hik'.1
        · rw [hperm k i hk hi]
          exact hik'.2
    · refine ⟨?_, ?_, ?_⟩
      · intro i hi
        exact False.elim (hany ⟨i, hi⟩)
      · intro i j k hi hj hk hij hjk
        exact False.elim (hany ⟨i, hi⟩)
      · intro i j k hi hj hk hij hji hjk hkj
        exact False.elim (hany ⟨i, hi⟩)
  · intro O V K _ p lt get i j x y hgeti hgetj hltab hltba
    simp [JuliaLean.base.ordering.ltPerm, JuliaLean.base.ordering.assertBool,
      hgeti, hgetj, hltab, hltba]


theorem ordCombinations_proven : OrdCombinations := by
  constructor
  · intro A K isless custom key useCustom orderReversed a b
    refine ⟨?_, ?_⟩
    · cases useCustom <;> cases orderReversed <;> cases key <;>
        simp [ordNothing, ordDispatch, packageOrd, ordIslessForward,
          ordIslessReverseForward, ordCustomForward, ordCustomReverseForward,
          reverseKeyedOrdering, _by, byGeneric, byIdentity, directOrderArg,
          ltForward, ltReverse, ltBy, ltLt, ordCompare, reverseOrdering,
          reverseOrdering_wrap, reverseOrdering_by, expectedOrdCompare, applyKey,
          Pure.pure, Except.bind, Except.pure] <;> rfl
    · intro rev
      cases useCustom <;> cases orderReversed <;> cases rev <;> cases key <;>
        simp [ordBool, ordDispatch, packageOrd, ordIslessForward,
          ordIslessReverseForward, ordCustomForward, ordCustomReverseForward,
          reverseKeyedOrdering, _by, byGeneric, byIdentity, directOrderArg,
          ltForward, ltReverse, ltBy, ltLt, ordCompare, ordResultReverse,
          reverseOrdering, reverseOrdering_wrap, reverseOrdering_by,
          expectedOrdCompare, applyKey, Pure.pure, Except.bind, Except.pure] <;> rfl
  · intro A K O _ isless key order compare a b
    let lt : Sum (K → K → OrderingResult Bool) (K → K → OrderingResult Bool) :=
      .inl (fun x y => compare order x y)
    refine ⟨?_, ?_⟩
    · cases key <;>
        simp [ordNothing, ordDispatch, packageOrd, ordIslessGeneric, _by,
          byGeneric, byIdentity, ltBy, ordCompare, expectedOrdCompare,
          applyKey, Except.bind, Except.pure, Pure.pure] <;> rfl
    · intro rev
      cases rev <;> cases key <;>
        simp [ordBool, ordDispatch, packageOrd, ordIslessGeneric, _by,
          byGeneric, byIdentity, ltBy, ltReverse, ordCompare, ordResultReverse,
          reverseOrdering, reverseOrdering_wrap, reverseOrdering_by,
          expectedOrdCompare, applyKey, Except.bind, Except.pure, Pure.pure] <;> rfl

theorem ordCorrect_proven : OrdCorrect := ordCombinations_proven


/-! ## Refutation: reversing a Perm keeps the ascending index tie-break -/

theorem reverseOrderingPermLtSwap_refuted : ¬ ReverseOrderingPermLtSwap := by
  intro h
  have hs := h (O := ForwardOrdering) (V := Bool → Unit) (I := Bool) (K := Unit)
    (p := ⟨ForwardOrdering.mk, fun _ => ()⟩)
    (lt := fun _ _ _ => (Except.ok (some false) : OrderingResult (Option Bool)))
    (get := fun (v : Bool → Unit) (i : Bool) => (Except.ok (v i) : OrderingResult Unit))
    (indexLess := fun i j : Bool => (Except.ok (!i && j) : OrderingResult Bool))
    (i := false) (j := true) (x := ()) (y := ()) rfl rfl
  have hs' : (Except.ok true : OrderingResult Bool) = Except.ok false := hs
  simp at hs'

namespace JuliaLean.ChatGPT.Batch3.Group5
open JuliaLean.Proofs.base.ordering

/-- ordering-reverse-default: The default Reverse wraps Forward and preserves strict weakness when it reverses the arguments to isless. -/
theorem OrderingReverseDefault_proven : JuliaLean.Proofs.base.ordering.ReverseDefaultUsesIsless := by
  exact JuliaLean.Proofs.base.ordering.reverseDefaultUsesIsless_proven

end JuliaLean.ChatGPT.Batch3.Group5

end JuliaLean.Proofs.base.ordering

namespace JuliaLean.ChatGPT.Batch4.Group14
open JuliaLean.Proofs.base.ordering
open JuliaLean.base.ordering

/-- sort-order-reverse-cancellation. -/
theorem SortOrderReverseCancellation_proven : JuliaLean.Proofs.base.ordering.ReverseCancellation := by
  intro O A inst o lt less h hs
  simpa only [reverseOrdering, reverseOrdering_wrap, reverseOrdering_unwrap,
    h, resultBool] using hs

/-- sort-order-perm-stability. -/
theorem SortOrderPermStability_proven : JuliaLean.Proofs.base.ordering.PermStability := by
  intro O V K inst p lt get i j x y hi hj hxy hyx
  simp only [ltPerm, hi, hj, hxy, hyx, assertBool, Bool.not_false,
    Bool.true_and, Bool.false_or]

end JuliaLean.ChatGPT.Batch4.Group14

namespace JuliaLean.Proofs.base.ordering

open JuliaLean.Registry

def entries : List Entry := [
  { id := "sort-order-reverse-cancellation", juliaFile := "base/ordering.jl"
    juliaFns := ["ReverseOrdering", "reverse(::Ordering)"]
    statement := "Reversing twice and unwrapping both layers preserves the strict weak behavior of the original comparator."
    source := "base/ordering.jl:33-48 (ReverseOrdering construction)"
    status := .proven
    prop := ``ReverseCancellation, thm := some ``JuliaLean.ChatGPT.Batch4.Group14.SortOrderReverseCancellation_proven },
  { id := "sort-order-perm-stability", juliaFile := "base/ordering.jl"
    juliaFns := ["Perm", "lt(::Perm, a, b)"]
    statement := "When both wrapped comparisons are false, Perm compares the indices by mathematical integer order."
    source := "base/ordering.jl:98-103 (Perm docstring)"
    status := .proven
    prop := ``PermStability, thm := some ``JuliaLean.ChatGPT.Batch4.Group14.SortOrderPermStability_proven },
  { id := "sorttuplescov-reverseordering-perm-lt", juliaFile := "base/ordering.jl"
    juliaFns := ["ReverseOrdering(perm::Perm)", "lt(::Perm, a, b)"]
    statement := "Reversing a Perm ordering swaps every pair of valid indices in its comparison result."
    source := "base/ordering.jl:33-41 (ReverseOrdering docstring)"
    status := .refuted
    prop := ``ReverseOrderingPermLtSwap
    thm := some ``reverseOrderingPermLtSwap_refuted
    issue := "related: #46732 (merged)"
    notes := "ReverseOrdering(perm::Perm) = Perm(ReverseOrdering(perm.order), perm.data) keeps the ascending index tie-break, so with Perm(Forward, [0, 0]) lt(ReverseOrdering(p), 1, 2) is true while lt(p, 2, 1) is false. The Lean model refutes through the same index asymmetry; retained reproducer repro/sorttuplescov-reverseordering-perm-lt.jl." },
  { id := "sorttuplescov-reverse-ordering", juliaFile := "base/ordering.jl"
    juliaFns := ["ReverseOrdering(rev::ReverseOrdering)", "ReverseOrdering(fwd::Fwd)",
      "ReverseOrdering()", "ReverseOrdering(by::By)", "By(by)"]
    statement := "Reverse comparisons preserve strict weakness, and reversing a By ordering reverses key comparisons when key evaluation succeeds."
    source := "base/ordering.jl:33-48, 86, 110 (ReverseOrdering and By docstrings)"
    status := .proven
    prop := ``ReverseOrderingCorrect, thm := some ``reverseOrderingCorrect_proven },
  { id := "sorttuplescov-perm-lt", juliaFile := "base/ordering.jl"
    juliaFns := ["lt(::Perm, a::Integer, b::Integer)"]
    statement := "Perm compares indexed data, breaks equal-value ties by numeric index, propagates failed reads and comparisons, and forms a strict weak order on valid indices when its element order is strict weak."
    source := "base/ordering.jl:98-103 (Perm docstring), 123-127"
    status := .proven
    prop := ``PermLtCorrect, thm := some ``permLtCorrect_proven },
  { id := "sorttuplescov-ord", juliaFile := "base/ordering.jl"
    juliaFns := ["_ord", "_by", "ord(lt, by, rev::Nothing, order)", "ord(lt, by, rev::Bool, order)"]
    statement := "ord's returned ordering compares transformed values with the selected comparator and reverses exactly when rev=true differs from order=Reverse."
    source := "base/ordering.jl:139-153 (ord docstring), 130-160"
    status := .proven
    prop := ``OrdCorrect, thm := some ``ordCorrect_proven },
  { id := "ordering-lt-methods", juliaFile := "base/ordering.jl"
    juliaFns := ["lt(::ForwardOrdering)", "lt(::ReverseOrdering)", "lt(::By)", "lt(::Lt)"]
    statement := "Forward and Lt retain a strict weak comparator, Reverse preserves strict weakness when swapping arguments, and By preserves it through a total key function."
    source := "base/ordering.jl:88-96, 113-121"
    status := .proven
    prop := ``LtMethodsCorrect, thm := some ``ltMethodsCorrect_proven },
  { id := "ordering-by-default", juliaFile := "base/ordering.jl"
    juliaFns := ["By(by)"]
    statement := "By(by) stores Forward, and strict weak ordering of keys yields strict weak ordering of inputs."
    source := "base/ordering.jl:74-86 (By docstring and default constructor)"
    status := .proven
    prop := ``ByDefaultUsesForward, thm := some ``byDefaultUsesForward_proven },
  { id := "ordering-reverse-default", juliaFile := "base/ordering.jl"
    juliaFns := ["ReverseOrdering()", "Reverse"]
    statement := "The default Reverse wraps Forward and preserves strict weakness when it reverses the arguments to isless."
    source := "base/ordering.jl:68-72 (Reverse docstring and default constructor)"
    status := .proven
    prop := ``ReverseDefaultUsesIsless, thm := some ``JuliaLean.ChatGPT.Batch3.Group5.OrderingReverseDefault_proven },
  { id := "ordering-ord-combinations", juliaFile := "base/ordering.jl"
    juliaFns := ["_ord", "_by", "ord"]
    statement := "For rev=nothing and rev::Bool, ord applies the selected isless or custom comparator to transformed values and reverses exactly when rev=true differs from order=Reverse."
    source := "base/ordering.jl:139-153 (ord docstring)"
    status := .proven
    prop := ``OrdCombinations, thm := some ``ordCombinations_proven
    notes := "The source-compatible reversal keeps key evaluation in left-to-right argument order for every rev/order combination." },
  { id := "ordering-ord-rejects", juliaFile := "base/ordering.jl"
    juliaFns := ["_ord(lt, by, order::Ordering)", "ord"]
    statement := "Supplying both a custom lt and an explicit order outside Forward and Reverse raises the documented ErrorException for rev=nothing and rev::Bool."
    source := "base/ordering.jl:135, 150-151"
    status := .proven
    prop := ``OrdRejects, thm := some ``ordRejects_proven },
]

/-! Nothing to promise: `ordtype(::ReverseOrdering)`@170: forwards type metadata to the wrapped ordering. -/
/-! Nothing to promise: `ordtype(::Perm)`@171: forwards type metadata to the wrapped ordering and its data. -/
/-! Nothing to promise: `ordtype(::Ordering)`@174: returns the array's element-type metadata unchanged. -/
/-! Nothing to promise: `ordtype(::By)`@173: Base marks this inference helper as unused; its inferred type is not a public contract. -/
end JuliaLean.Proofs.base.ordering
