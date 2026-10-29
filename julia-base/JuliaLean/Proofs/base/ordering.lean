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

def ReverseCancellation : Prop :=
  ∀ (O : Type) [Ordering O] (o : O),
    reverseOrdering_unwrap (reverseOrdering_unwrap (reverseOrdering (reverseOrdering o))) = o

def PermStability : Prop :=
  ∀ (O V I K : Type) [Ordering O] (p : Perm O V)
    (lt : O → K → K → OrderingResult (Option Bool)) (get : V → I → OrderingResult K)
    (indexLess : I → I → OrderingResult Bool) (i j : I) (x y : K) (result : Bool),
    get p.data i = .ok x →
    get p.data j = .ok y →
    lt p.order x y = .ok (some false) →
    lt p.order y x = .ok (some false) →
    indexLess i j = .ok result →
    ltPerm p lt get indexLess i j = .ok result

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
  (∀ (O A : Type) [Ordering O] (o : O) (lt : O → A → A → OrderingResult Bool) (a b : A),
    ltReverse (reverseOrdering o) lt a b = lt o b a) ∧
  (∀ (O : Type) [Ordering O] (o : O), reverseOrdering_unwrap (reverseOrdering o) = o) ∧
  (∀ (T O : Type) [Ordering O] (byValue : By T O),
    (reverseOrdering_by byValue).callable = byValue.callable ∧
    reverseOrdering_unwrap (reverseOrdering_by byValue).order = byValue.order) ∧
  (∀ (O V : Type) [Ordering O] (perm : Perm O V),
    (reverseOrdering_perm perm).data = perm.data ∧
    reverseOrdering_unwrap (reverseOrdering_perm perm).order = perm.order)

def StrictWeak {A : Type} (lt : A → A → Bool) : Prop :=
  (∀ a, lt a a = false) ∧
  (∀ a b c, lt a b = true → lt b c = true → lt a c = true) ∧
  (∀ a b c, lt a b = false → lt b a = false → lt b c = false → lt c b = false →
    lt a c = false ∧ lt c a = false)

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
  (∀ (O V I K : Type) [Ordering O] (p : Perm O V)
    (lt : O → K → K → OrderingResult (Option Bool)) (get : V → I → OrderingResult K)
    (indexLess : I → I → OrderingResult Bool) (i j : I) (x y : K)
    (ab ba indexResult : Bool),
    get p.data i = .ok x →
    get p.data j = .ok y →
    lt p.order x y = .ok (some ab) →
    lt p.order y x = .ok (some ba) →
    ¬ (ab = true ∧ ba = true) →
    indexLess i j = .ok indexResult →
    ltPerm p lt get indexLess i j =
      .ok (if ab then true else if ba then false else indexResult)) ∧
  (∀ (O V I K : Type) [Ordering O] (p : Perm O V)
    (lt : O → K → K → OrderingResult (Option Bool)) (get : V → I → OrderingResult K)
    (indexLess : I → I → OrderingResult Bool) (valid : I → Prop),
    (∀ i, valid i → ∃ x, get p.data i = .ok x) →
    (∀ i j, valid i → valid j → ∃ result, indexLess i j = .ok result) →
    (∀ x y, ∃ result, lt p.order x y = .ok (some result)) →
    StrictWeak (dataLess lt p.order) →
    StrictTotalOn valid (indexLessValue indexLess) →
    StrictWeakOn valid (permLess p lt get indexLess))

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

def LtMethodsCorrect : Prop :=
  (∀ (A : Type) (o : ForwardOrdering) (isless : A → A → OrderingResult Bool) (a b : A),
    ltForward o isless a b = isless a b) ∧
  (∀ (O A : Type) [Ordering O] (o : ReverseOrdering O)
    (lt : O → A → A → OrderingResult Bool) (a b : A),
    ltReverse o lt a b = lt o.fwd b a) ∧
  (∀ (T O A K : Type) (o : By T O) (apply : T → A → OrderingResult K)
    (lt : O → K → K → OrderingResult Bool) (a b : A),
    ltBy o apply lt a b =
      (match apply o.callable a with
      | .error e => .error e
      | .ok ka =>
        match apply o.callable b with
        | .error e => .error e
        | .ok kb => lt o.order ka kb)) ∧
  (∀ (A : Type) (o : Lt A) (a b : A), ltLt o a b = o.lt a b)

def ByDefaultUsesForward : Prop :=
  ∀ (T : Type) (fn : T),
    (byDefault fn).callable = fn ∧ (byDefault fn).order = Forward

def ReverseDefaultUsesIsless : Prop :=
  (∀ (A : Type) (isless : A → A → OrderingResult Bool) (a b : A),
    ltReverse Reverse (fun _ x y => isless x y) a b = isless b a) ∧
  reverseOrdering_default.fwd = Forward

def OrdCombinations : Prop :=
  (∀ (A K : Type)
    (isless custom : K → K → OrderingResult Bool) (key : KeyArg A K)
    (useCustom orderReversed : Bool) (a b : A),
    let lt : Sum (K → K → OrderingResult Bool) (K → K → OrderingResult Bool) :=
      if useCustom then .inr custom else .inl isless
    let order := directOrderArg orderReversed isless
    (do
      let o ← ordNothing lt key () order
      ordCompare o a b) = expectedOrdCompare lt key orderReversed false a b ∧
    (∀ rev : Bool,
      (do
        let o ← ordBool lt key rev order
        ordCompare o a b) = expectedOrdCompare lt key orderReversed rev a b)) ∧
  (∀ (A K O : Type) (isless : K → K → OrderingResult Bool) (key : KeyArg A K)
    (order : O) (compare : O → K → K → OrderingResult Bool) (rev : Bool) (a b : A),
    let lt : Sum (K → K → OrderingResult Bool) (K → K → OrderingResult Bool) :=
      .inl (fun x y => compare order x y)
    (do
      let o ← ordBool (.inl isless) key rev (.other order compare)
      ordCompare o a b) = expectedOrdCompare lt key false rev a b)

def OrdCorrect : Prop := OrdCombinations

def OrdRejects : Prop :=
  ∀ (A K O : Type) (custom : K → K → OrderingResult Bool) (key : KeyArg A K)
    (order : O) (compare : O → K → K → OrderingResult Bool) (rev : Bool),
    ordBool (.inr custom) key rev (.other order compare) =
      .error (.errorException
        "Passing both lt= and order= arguments is ambiguous; please pass order=Forward or order=Reverse (or leave default)")

def OrdtypeCorrect : Prop :=
  ∀ (O V W : Type) [Ordering O] (ordtype : OrdtypeCall O)
    (reverse : ReverseOrdering O) (perm : Perm O V) (vs : W),
    ordtypeReverse ordtype reverse vs = ordtype.call reverse.fwd vs ∧
    ordtypePerm ordtype perm vs = ordtype.call perm.order perm.data ∧
    (∀ (T A K O' : Type) (getFirst : W → OrderingResult A)
      (apply : T → A → OrderingResult K) (typeof : K → TypeToken) (byValue : By T O'),
      ordtypeBy getFirst apply typeof byValue vs =
        match getFirst vs with
        | .error _ => anyType
        | .ok x => match apply byValue.callable x with
          | .error _ => anyType
          | .ok key => typeof key) ∧
    (∀ (eltype : W → TypeToken) (o : O), ordtypeOrdering eltype o vs = eltype vs)

/-! ## Proofs -/

theorem reverseCancellation_proven : ReverseCancellation := by
  intro O _ o
  rfl

theorem reverseOrderingCorrect_proven : ReverseOrderingCorrect := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro O A _ o lt a b
    rfl
  · intro O _ o
    rfl
  · intro T O _ byValue
    exact ⟨rfl, rfl⟩
  · intro O V _ perm
    exact ⟨rfl, rfl⟩

theorem ltMethodsCorrect_proven : LtMethodsCorrect := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A o isless a b
    rfl
  · intro O A _ o lt a b
    rfl
  · intro T O A K o apply lt a b
    rfl
  · intro A o a b
    rfl

theorem byDefaultUsesForward_proven : ByDefaultUsesForward := by
  intro T fn
  exact ⟨rfl, rfl⟩

theorem reverseDefaultUsesIsless_proven : ReverseDefaultUsesIsless := by
  refine ⟨?_, ?_⟩
  · intro A isless a b
    rfl
  · rfl

theorem ordRejects_proven : OrdRejects := by
  intro A K O custom key order compare rev
  rfl

theorem ordtypeCorrect_proven : OrdtypeCorrect := by
  intro O V W _ ordtype reverse perm vs
  refine ⟨?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · intro T A K O' getFirst apply typeof byValue
    rfl
  · intro eltype o
    rfl

theorem permStability_proven : PermStability := by
  intro O V I K _ p lt get indexLess i j x y result h1 h2 h3 h4 h5
  simp [ltPerm, assertBool, h1, h2, h3, h4, h5]

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

theorem ordCombinations_proven : OrdCombinations := by
  constructor
  · intro A K isless custom key useCustom orderReversed a b
    refine ⟨?_, ?_⟩
    · show
        (do
          let o ← ordNothing (if useCustom then Sum.inr custom else Sum.inl isless) key ()
              (directOrderArg orderReversed isless)
          ordCompare o a b) =
          expectedOrdCompare (if useCustom then Sum.inr custom else Sum.inl isless) key
            orderReversed false a b
      cases useCustom <;> cases orderReversed <;> cases key <;> rfl
    · intro rev
      show
        (do
          let o ← ordBool (if useCustom then Sum.inr custom else Sum.inl isless) key rev
              (directOrderArg orderReversed isless)
          ordCompare o a b) =
          expectedOrdCompare (if useCustom then Sum.inr custom else Sum.inl isless) key
            orderReversed rev a b
      cases useCustom <;> cases orderReversed <;> cases rev <;> cases key <;> rfl
  · intro A K O isless key order compare rev a b
    show
      (do
        let o ← ordBool (Sum.inl isless) key rev (OrderArg.other order compare)
        ordCompare o a b) =
        expectedOrdCompare (Sum.inl (fun x y => compare order x y)) key false rev a b
    cases rev <;> cases key <;> rfl

theorem ordCorrect_proven : OrdCorrect := ordCombinations_proven

theorem permLtCorrect_proven : PermLtCorrect := by
  refine ⟨?_, ?_⟩
  · intro O V I K _ p lt get indexLess i j x y ab ba indexResult h1 h2 h3 h4 _h5 h6
    simp [ltPerm, assertBool, h1, h2, h3, h4, h6]
  · intro O V I K _ p lt get indexLess valid hget hidx hlt hsw hto
    obtain ⟨hirr, htrans, hincomp⟩ := hsw
    obtain ⟨ihirr, itrans, itotal, _ine⟩ := hto
    have orElim : ∀ (u v : Bool), (u || v) = true → u = true ∨ (u = false ∧ v = true) := by
      intro u v h
      cases u with
      | true => exact Or.inl rfl
      | false =>
        rw [Bool.false_or] at h
        exact Or.inr ⟨rfl, h⟩
    have andElim : ∀ (u v : Bool), (u && v) = true → u = true ∧ v = true := by
      intro u v h
      cases u with
      | true =>
        rw [Bool.true_and] at h
        exact ⟨rfl, h⟩
      | false =>
        rw [Bool.false_and] at h
        exact absurd h (by decide)
    have notElim : ∀ (u : Bool), (!u) = true → u = false := by
      intro u h
      cases u with
      | true =>
        rw [Bool.not_true] at h
        exact absurd h (by decide)
      | false => exact rfl
    have orFalse : ∀ (u v : Bool), (u || v) = false → u = false ∧ v = false := by
      intro u v h
      cases u with
      | true =>
        rw [Bool.true_or] at h
        exact absurd h (by decide)
      | false =>
        cases v with
        | true =>
          rw [Bool.false_or] at h
          exact absurd h (by decide)
        | false => exact ⟨rfl, rfl⟩
    have hF3 : ∀ x y z : K, dataLess lt p.order x y = true → dataLess lt p.order x z = false →
        dataLess lt p.order z x = false →
        dataLess lt p.order y z = true ∨ dataLess lt p.order z y = true := by
      intro x y z hAxy hAxz hAzx
      cases hAyz : dataLess lt p.order y z with
      | true => exact Or.inl rfl
      | false =>
        cases hAzy : dataLess lt p.order z y with
        | true => exact Or.inr rfl
        | false =>
          obtain ⟨hxy, _⟩ := hincomp x z y hAxz hAzx hAzy hAyz
          rw [hxy] at hAxy
          exact absurd hAxy (by decide)
    have expand : ∀ (i j : I) (x y : K) (t : Bool), get p.data i = .ok x →
        get p.data j = .ok y → indexLess i j = .ok t →
        permLess p lt get indexLess i j =
          (dataLess lt p.order x y || (!(dataLess lt p.order y x) && t)) := by
      intro i j x y t hx hy ht
      obtain ⟨r, hr⟩ := hlt x y
      obtain ⟨s, hs⟩ := hlt y x
      have e1 : dataLess lt p.order x y = r := by simp only [dataLess, hr]
      have e2 : dataLess lt p.order y x = s := by simp only [dataLess, hs]
      simp only [permLess, ltPerm, assertBool, hx, hy, hr, hs, ht, e1, e2]
    have hPval : ∀ (i j : I) (x y : K), valid i → valid j →
        get p.data i = .ok x → get p.data j = .ok y →
        permLess p lt get indexLess i j =
          (dataLess lt p.order x y || (!(dataLess lt p.order y x) && indexLessValue indexLess i j)) := by
      intro i j x y hi hj hx hy
      obtain ⟨t, ht⟩ := hidx i j hi hj
      rw [expand i j x y t hx hy ht]
      simp only [indexLessValue, ht]
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      obtain ⟨x, hx⟩ := hget i hi
      rw [hPval i i x x hi hi hx hx, hirr x, ihirr i hi]
      rfl
    · intro i j k hi hj hk hPij hPjk
      obtain ⟨x, hx⟩ := hget i hi
      obtain ⟨y, hy⟩ := hget j hj
      obtain ⟨z, hz⟩ := hget k hk
      rw [hPval i j x y hi hj hx hy] at hPij
      rw [hPval j k y z hj hk hy hz] at hPjk
      rw [hPval i k x z hi hk hx hz]
      rcases orElim _ _ hPij with hAxy | hRestij
      · rcases orElim _ _ hPjk with hAyz | hRestjk
        · rw [htrans x y z hAxy hAyz]
          rfl
        · obtain ⟨hAyzf, hAndjk⟩ := hRestjk
          obtain ⟨hAzyNot, _hIjk⟩ := andElim _ _ hAndjk
          have hAzyf : dataLess lt p.order z y = false := notElim _ hAzyNot
          cases hAxz : dataLess lt p.order x z with
          | true => rfl
          | false =>
            cases hAzx : dataLess lt p.order z x with
            | true =>
              rw [htrans z x y hAzx hAxy] at hAzyf
              exact absurd hAzyf (by decide)
            | false =>
              rcases hF3 x y z hAxy hAxz hAzx with hAyz2 | hAzy2
              · rw [hAyz2] at hAyzf
                exact absurd hAyzf (by decide)
              · rw [hAzy2] at hAzyf
                exact absurd hAzyf (by decide)
      · obtain ⟨hAxyf, hAndij⟩ := hRestij
        obtain ⟨hAyxNot, hIij⟩ := andElim _ _ hAndij
        have hAyxf : dataLess lt p.order y x = false := notElim _ hAyxNot
        rcases orElim _ _ hPjk with hAyz | hRestjk
        · cases hAxz : dataLess lt p.order x z with
          | true => rfl
          | false =>
            rcases hF3 y z x hAyz hAyxf hAxyf with hAzxT | hAxzT2
            · rw [htrans y z x hAyz hAzxT] at hAyxf
              exact absurd hAyxf (by decide)
            · rw [hAxzT2] at hAxz
              exact absurd hAxz (by decide)
        · obtain ⟨hAyzf, hAndjk⟩ := hRestjk
          obtain ⟨hAzyNot, hIjk⟩ := andElim _ _ hAndjk
          have hAzyf : dataLess lt p.order z y = false := notElim _ hAzyNot
          obtain ⟨hAxzf, hAzxf⟩ := hincomp x y z hAxyf hAyxf hAyzf hAzyf
          have hIikT : indexLessValue indexLess i k = true := itrans i j k hi hj hk hIij hIjk
          rw [hAxzf, hAzxf, hIikT]
          rfl
    · intro i j k hi hj hk h1 h2 h3 h4
      obtain ⟨x, hx⟩ := hget i hi
      obtain ⟨y, hy⟩ := hget j hj
      obtain ⟨z, hz⟩ := hget k hk
      rw [hPval i j x y hi hj hx hy] at h1
      rw [hPval j i y x hj hi hy hx] at h2
      rw [hPval j k y z hj hk hy hz] at h3
      rw [hPval k j z y hk hj hz hy] at h4
      rw [hPval i k x z hi hk hx hz]
      rw [hPval k i z x hk hi hz hx]
      obtain ⟨hAxyf, hSecij⟩ := orFalse _ _ h1
      obtain ⟨hAyxf, hSecji⟩ := orFalse _ _ h2
      obtain ⟨hAyzf, hSecjk⟩ := orFalse _ _ h3
      obtain ⟨hAzyf, hSectkj⟩ := orFalse _ _ h4
      rw [hAyxf, Bool.not_false, Bool.true_and] at hSecij
      rw [hAxyf, Bool.not_false, Bool.true_and] at hSecji
      rw [hAzyf, Bool.not_false, Bool.true_and] at hSecjk
      rw [hAyzf, Bool.not_false, Bool.true_and] at hSectkj
      obtain ⟨hAxzf, hAzxf⟩ := hincomp x y z hAxyf hAyxf hAyzf hAzyf
      have hjk : j = k := by
        refine Classical.byContradiction fun hne => ?_
        rcases itotal j k hj hk hne with hc | hc
        · rw [hSecjk] at hc
          exact absurd hc (by decide)
        · rw [hSectkj] at hc
          exact absurd hc (by decide)
      subst hjk
      refine ⟨?_, ?_⟩
      · rw [hAxzf, hAzxf, Bool.not_false, Bool.true_and, Bool.false_or]
        exact hSecij
      · rw [hAzxf, hAxzf, Bool.not_false, Bool.true_and, Bool.false_or]
        exact hSecji

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

def entries : List Entry := [
  { id := "sort-order-reverse-cancellation", juliaFile := "base/ordering.jl"
    juliaFns := ["ReverseOrdering", "reverse(::Ordering)"]
    statement := "Wrapping an ordering twice and unwrapping both layers restores the original ordering."
    source := "base/ordering.jl:33-48 (ReverseOrdering construction)"
    status := .proven
    prop := ``ReverseCancellation, thm := some ``reverseCancellation_proven },
  { id := "sort-order-perm-stability", juliaFile := "base/ordering.jl"
    juliaFns := ["Perm", "lt(::Perm, a, b)"]
    statement := "If two data values compare equivalent under the wrapped ordering, Perm compares their indices numerically."
    source := "base/ordering.jl:98-103 (Perm docstring)"
    status := .proven
    prop := ``PermStability, thm := some ``permStability_proven },
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
    statement := "Reverse ordering swaps comparison arguments, preserves the wrapped ordering's value, and retains a By key while reversing its order."
    source := "base/ordering.jl:33-48, 86, 110 (ReverseOrdering and By docstrings)"
    status := .proven
    prop := ``ReverseOrderingCorrect, thm := some ``reverseOrderingCorrect_proven },
  { id := "sorttuplescov-perm-lt", juliaFile := "base/ordering.jl"
    juliaFns := ["lt(::Perm, a::Integer, b::Integer)"]
    statement := "Perm compares indexed data, breaks equivalent-value ties by numeric index, propagates failed reads and comparisons, and forms a strict weak order on valid indices when its element order is strict weak."
    source := "base/ordering.jl:98-103 (Perm docstring), 123-127"
    status := .proven
    prop := ``PermLtCorrect, thm := some ``permLtCorrect_proven },
  { id := "sorttuplescov-ord", juliaFile := "base/ordering.jl"
    juliaFns := ["_ord", "_by", "ord(lt, by, rev::Nothing, order)", "ord(lt, by, rev::Bool, order)"]
    statement := "ord applies the selected key and comparator, reverses for rev=true, and cancels that reversal when order is Reverse."
    source := "base/ordering.jl:139-153 (ord docstring), 130-160"
    status := .proven
    prop := ``OrdCorrect, thm := some ``ordCorrect_proven },
  { id := "sorttuplescov-ordtype", juliaFile := "base/ordering.jl"
    juliaFns := ["ordtype(::ReverseOrdering)", "ordtype(::Perm)", "ordtype(::By)", "ordtype(::Ordering)"]
    statement := "ordtype delegates through ReverseOrdering and Perm, infers the By key type from the first value or Any on failure, and otherwise returns the input element type."
    source := "base/ordering.jl:163-174"
    status := .proven
    prop := ``OrdtypeCorrect, thm := some ``ordtypeCorrect_proven },
  { id := "ordering-lt-methods", juliaFile := "base/ordering.jl"
    juliaFns := ["lt(::ForwardOrdering)", "lt(::ReverseOrdering)", "lt(::By)", "lt(::Lt)"]
    statement := "Each ordering compares the supplied values through isless, the wrapped comparator with reversed arguments, the transformed keys, or the Lt function, respectively."
    source := "base/ordering.jl:88-96, 113-121"
    status := .proven
    prop := ``LtMethodsCorrect, thm := some ``ltMethodsCorrect_proven },
  { id := "ordering-by-default", juliaFile := "base/ordering.jl"
    juliaFns := ["By(by)"]
    statement := "By(by) stores by and defaults its ordering to Forward."
    source := "base/ordering.jl:74-86 (By docstring and default constructor)"
    status := .proven
    prop := ``ByDefaultUsesForward, thm := some ``byDefaultUsesForward_proven },
  { id := "ordering-reverse-default", juliaFile := "base/ordering.jl"
    juliaFns := ["ReverseOrdering()", "Reverse"]
    statement := "The default Reverse ordering swaps the arguments to the default isless comparator."
    source := "base/ordering.jl:68-72 (Reverse docstring and default constructor)"
    status := .proven
    prop := ``ReverseDefaultUsesIsless, thm := some ``reverseDefaultUsesIsless_proven },
  { id := "ordering-ord-combinations", juliaFile := "base/ordering.jl"
    juliaFns := ["_ord", "_by", "ord"]
    statement := "The lt, key, rev, and direct-order options combine so comparisons reverse exactly when one of rev=true and order=Reverse holds."
    source := "base/ordering.jl:139-153 (ord docstring)"
    status := .proven
    prop := ``OrdCombinations, thm := some ``ordCombinations_proven
    notes := "The ord result model carries the key transform outside the reversal (OrdResult), matching Julia's ReverseOrdering(::By) constructor fold at base/ordering.jl:62; a Julia probe confirmed keys are read a-first in every rev/order combination." },
  { id := "ordering-ord-rejects", juliaFile := "base/ordering.jl"
    juliaFns := ["_ord(lt, by, order::Ordering)", "ord"]
    statement := "A custom lt combined with an order other than Forward or Reverse raises the documented ErrorException."
    source := "base/ordering.jl:135, 150-151"
    status := .proven
    prop := ``OrdRejects, thm := some ``ordRejects_proven },
  { id := "ordering-perm-evaluation", juliaFile := "base/ordering.jl"
    juliaFns := ["lt(::Perm, a::Integer, b::Integer)"]
    statement := "Perm reads each indexed value and evaluates the forward then backward comparison, stopping and propagating the first error."
    source := "base/ordering.jl:123-127"
    status := .proven
    prop := ``PermLtEvaluationCorrect, thm := some ``permLtEvaluationCorrect_proven }
]

end JuliaLean.Proofs.base.ordering
