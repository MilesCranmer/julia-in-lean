import JuliaLean.base.pair
import JuliaLean.Registry.Types

/-!
# Properties of `base/pair.jl`

These specifications describe pair iteration and indexing, product equality and lexicographic
ordering, type-preserving conversion, reversal, and componentwise promotion. Generic Julia callees
remain parameters in the model.
-/

namespace JuliaLean.Proofs.base.pair

open JuliaLean
open JuliaLean.base.pair
open JuliaLean.Registry

/-! ## Integer-index instances of the generic iteration method -/

def one64 : JInt .i64 := JInt.lit .i64 1
def two64 : JInt .i64 := JInt.lit .i64 2
def three64 : JInt .i64 := JInt.lit .i64 3
def zero64 : JInt .i64 := JInt.lit .i64 0

@[simp] theorem one64_val : one64.val = 1 := by decide
@[simp] theorem two64_val : two64.val = 2 := by decide
@[simp] theorem three64_val : three64.val = 3 := by decide
@[simp] theorem zero64_val : zero64.val = 0 := by decide
@[simp] theorem litOne64_val : (JInt.lit .i64 1).val = 1 := by decide

theorem litOne64_add_one : JInt.lit .i64 1 + one64 = two64 := by
  apply Subtype.ext
  decide

theorem one64_add_one : one64 + one64 = two64 := by
  apply Subtype.ext
  decide

theorem two64_add_one : two64 + one64 = three64 := by
  apply Subtype.ext
  decide

/-! Proof-internal integer-state reference instances. Each is definitionally equivalent to the
source-mirrored method, with that equivalence recorded below before the reference is used in proofs. -/
def iterateInt {A B : Type} (p : Pair A B) (i : JInt .i64) :
    Jl (Option ((A ⊕ B) × JInt .i64)) :=
  JuliaLean.base.pair.iterate (fun n => .ok (decide (n.val > 2))) JuliaLean.base.pair.getfieldInt
    (fun n => .ok (n + one64)) p i

def iterateDefaultInt {A B : Type} (p : Pair A B) :
    Jl (Option ((A ⊕ B) × JInt .i64)) :=
  JuliaLean.base.pair.iterateDefault (fun n => .ok (decide (n.val > 2))) JuliaLean.base.pair.getfieldInt
    (fun n => .ok (n + one64)) p

def indexedIterateInt {A B S : Type} (p : Pair A B) (i : JInt .i64) (state : S) :
    Jl ((A ⊕ B) × JInt .i64) :=
  JuliaLean.base.pair.indexedIterate JuliaLean.base.pair.getfieldInt (fun n => .ok (n + one64)) p i state

def indexedIterateDefaultInt {A B : Type} (p : Pair A B) (i : JInt .i64) :
    Jl ((A ⊕ B) × JInt .i64) :=
  JuliaLean.base.pair.indexedIterateDefault JuliaLean.base.pair.getfieldInt (fun n => .ok (n + one64)) p i

theorem iterateInt_matches_model {A B : Type} (p : Pair A B) (i : JInt .i64) :
    JuliaLean.base.pair.iterate (fun n => .ok (decide (n.val > 2)))
      JuliaLean.base.pair.getfieldInt (fun n => .ok (n + one64)) p i = iterateInt p i := rfl

theorem iterateDefaultInt_matches_model {A B : Type} (p : Pair A B) :
    JuliaLean.base.pair.iterateDefault (fun n => .ok (decide (n.val > 2)))
      JuliaLean.base.pair.getfieldInt (fun n => .ok (n + one64)) p = iterateDefaultInt p := rfl

theorem indexedIterateInt_matches_model {A B S : Type} (p : Pair A B) (i : JInt .i64)
    (state : S) :
    JuliaLean.base.pair.indexedIterate JuliaLean.base.pair.getfieldInt
      (fun n => .ok (n + one64)) p i state = indexedIterateInt p i state := rfl

theorem indexedIterateDefaultInt_matches_model {A B : Type} (p : Pair A B) (i : JInt .i64) :
    JuliaLean.base.pair.indexedIterateDefault JuliaLean.base.pair.getfieldInt
      (fun n => .ok (n + one64)) p i = indexedIterateDefaultInt p i := rfl

/-! ## Iteration and indexing -/

/-- Pair iteration with the default state and explicit states yields `first`, then `second`, then
ends; a field access below `1` raises `BoundsError` (`base/pair.jl:41`). -/
def PairIterationFields : Prop :=
  ∀ {A B : Type} (p : Pair A B),
    JuliaLean.base.pair.iterate (fun n => .ok (decide (n.val > 2)))
      JuliaLean.base.pair.getfieldInt (fun n => .ok (n + one64)) p one64 =
        .ok (some (.inl p.first, two64)) ∧
    JuliaLean.base.pair.iterate (fun n => .ok (decide (n.val > 2)))
      JuliaLean.base.pair.getfieldInt (fun n => .ok (n + one64)) p two64 =
        .ok (some (.inr p.second, three64)) ∧
    JuliaLean.base.pair.iterate (fun n => .ok (decide (n.val > 2)))
      JuliaLean.base.pair.getfieldInt (fun n => .ok (n + one64)) p three64 = .ok none ∧
    JuliaLean.base.pair.iterate (fun n => .ok (decide (n.val > 2)))
      JuliaLean.base.pair.getfieldInt (fun n => .ok (n + one64)) p zero64 = .error .boundsError ∧
    JuliaLean.base.pair.iterateDefault (fun n => .ok (decide (n.val > 2)))
      JuliaLean.base.pair.getfieldInt (fun n => .ok (n + one64)) p =
        .ok (some (.inl p.first, two64))
theorem pairIterationFields : PairIterationFields := by
  intro A B p
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [iterateInt_matches_model p one64]
    simp [iterateInt, JuliaLean.base.pair.iterate, JuliaLean.base.pair.getfieldInt,
      one64_val, one64_add_one, bind, Except.bind, pure, Except.pure]
  · rw [iterateInt_matches_model p two64]
    simp [iterateInt, JuliaLean.base.pair.iterate, JuliaLean.base.pair.getfieldInt,
      two64_val, two64_add_one, bind, Except.bind, pure, Except.pure]
  · rw [iterateInt_matches_model p three64]
    simp [iterateInt, JuliaLean.base.pair.iterate, three64_val, bind, Except.bind, pure, Except.pure]
  · rw [iterateInt_matches_model p zero64]
    simp [iterateInt, JuliaLean.base.pair.iterate, JuliaLean.base.pair.getfieldInt,
      zero64_val, bind, Except.bind]
  · rw [iterateDefaultInt_matches_model p]
    simp [iterateDefaultInt, JuliaLean.base.pair.iterateDefault,
      JuliaLean.base.pair.iterate, JuliaLean.base.pair.getfieldInt, litOne64_val,
      litOne64_add_one, bind, Except.bind, pure, Except.pure]
/-- Pair integer indexing returns its fields at indices `1` and `2`; every other index raises
`BoundsError`. A `Real` index first converts to `Int`, propagates conversion errors, and then uses
the same field indices (`base/pair.jl:54-55`). -/
def PairGetindexCorrect : Prop :=
  ∀ {A B : Type} (p : Pair A B),
    JuliaLean.base.pair.getindexInt JuliaLean.base.pair.getfieldInt p one64 = .ok (.inl p.first) ∧
    JuliaLean.base.pair.getindexInt JuliaLean.base.pair.getfieldInt p two64 = .ok (.inr p.second) ∧
    (∀ i : JInt .i64, i.val ≠ 1 → i.val ≠ 2 →
      JuliaLean.base.pair.getindexInt JuliaLean.base.pair.getfieldInt p i = .error .boundsError) ∧
    (∀ (X : Type) (convertInt : X → Jl (JInt .i64)) (x : X) (e : JlError),
      convertInt x = .error e → JuliaLean.base.pair.getindexReal convertInt p x = .error e) ∧
    (∀ (X : Type) (isNonIntegral : X → Bool) (convertInt : X → Jl (JInt .i64))
        (x : X) (fn : String),
      isNonIntegral x = true → convertInt x = .error (.inexactError fn) →
        JuliaLean.base.pair.getindexReal convertInt p x = .error (.inexactError fn)) ∧
    (∀ (X : Type) (convertInt : X → Jl (JInt .i64)) (x : X),
      convertInt x = .ok one64 → JuliaLean.base.pair.getindexReal convertInt p x = .ok (.inl p.first)) ∧
    (∀ (X : Type) (convertInt : X → Jl (JInt .i64)) (x : X),
      convertInt x = .ok two64 → JuliaLean.base.pair.getindexReal convertInt p x = .ok (.inr p.second)) ∧
    (∀ (X : Type) (convertInt : X → Jl (JInt .i64)) (x : X) (i : JInt .i64),
      convertInt x = .ok i → i.val ≠ 1 → i.val ≠ 2 →
        JuliaLean.base.pair.getindexReal convertInt p x = .error .boundsError)

theorem pairGetindexCorrect : PairGetindexCorrect := by
  intro A B p
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [JuliaLean.base.pair.getindexInt, JuliaLean.base.pair.getfieldInt, one64_val]
  · simp [JuliaLean.base.pair.getindexInt, JuliaLean.base.pair.getfieldInt, two64_val]
  · intro i h1 h2
    simp [JuliaLean.base.pair.getindexInt, JuliaLean.base.pair.getfieldInt, h1, h2]
  · intro X convertInt x e h
    simp [JuliaLean.base.pair.getindexReal, h, bind, Except.bind]
  · intro X isNonIntegral convertInt x fn _ h
    simp [JuliaLean.base.pair.getindexReal, h, bind, Except.bind]
  · intro X convertInt x h
    simp [JuliaLean.base.pair.getindexReal, h, JuliaLean.base.pair.getfieldInt, one64_val,
      bind, Except.bind]
  · intro X convertInt x h
    simp [JuliaLean.base.pair.getindexReal, h, JuliaLean.base.pair.getfieldInt, two64_val,
      bind, Except.bind]
  · intro X convertInt x i h h1 h2
    simp [JuliaLean.base.pair.getindexReal, h, JuliaLean.base.pair.getfieldInt, h1, h2,
      bind, Except.bind]

/-- `indexed_iterate` returns the selected field and next index for every ignored state; the
optional state defaults to `1`. -/
def PairIndexedIterationCorrect : Prop :=
  ∀ {A B : Type} (p : Pair A B),
    (∀ (S : Type) (state : S),
      JuliaLean.base.pair.indexedIterate JuliaLean.base.pair.getfieldInt
        (fun n => .ok (n + one64)) p one64 state = .ok (.inl p.first, two64)) ∧
    (∀ (S : Type) (state : S),
      JuliaLean.base.pair.indexedIterate JuliaLean.base.pair.getfieldInt
        (fun n => .ok (n + one64)) p two64 state = .ok (.inr p.second, three64)) ∧
    (∀ (S : Type) (state : S) (i : JInt .i64), i.val ≠ 1 → i.val ≠ 2 →
      JuliaLean.base.pair.indexedIterate JuliaLean.base.pair.getfieldInt
        (fun n => .ok (n + one64)) p i state = .error .boundsError) ∧
    JuliaLean.base.pair.indexedIterateDefault JuliaLean.base.pair.getfieldInt
      (fun n => .ok (n + one64)) p one64 = .ok (.inl p.first, two64) ∧
    JuliaLean.base.pair.indexedIterateDefault JuliaLean.base.pair.getfieldInt
      (fun n => .ok (n + one64)) p two64 = .ok (.inr p.second, three64)

theorem pairIndexedIterationCorrect : PairIndexedIterationCorrect := by
  intro A B p
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro S state
    rw [indexedIterateInt_matches_model p one64 state]
    simp [indexedIterateInt, JuliaLean.base.pair.indexedIterate,
      JuliaLean.base.pair.getfieldInt, one64_val, one64_add_one,
      bind, Except.bind, pure, Except.pure]
  · intro S state
    rw [indexedIterateInt_matches_model p two64 state]
    simp [indexedIterateInt, JuliaLean.base.pair.indexedIterate,
      JuliaLean.base.pair.getfieldInt, two64_val, two64_add_one,
      bind, Except.bind, pure, Except.pure]
  · intro S state i h1 h2
    rw [indexedIterateInt_matches_model p i state]
    simp [indexedIterateInt, JuliaLean.base.pair.indexedIterate,
      JuliaLean.base.pair.getfieldInt, h1, h2, bind, Except.bind]
  · rw [indexedIterateDefaultInt_matches_model p one64]
    simp [indexedIterateDefaultInt, JuliaLean.base.pair.indexedIterateDefault,
      JuliaLean.base.pair.indexedIterate, JuliaLean.base.pair.getfieldInt,
      one64_val, one64_add_one, bind, Except.bind, pure, Except.pure]
  · rw [indexedIterateDefaultInt_matches_model p two64]
    simp [indexedIterateDefaultInt, JuliaLean.base.pair.indexedIterateDefault,
      JuliaLean.base.pair.indexedIterate, JuliaLean.base.pair.getfieldInt,
      two64_val, two64_add_one, bind, Except.bind, pure, Except.pure]

/-- Pair indexing metadata and accessors are the fixed one-based tuple values promised by the
`Pair` docstring (`base/pair.jl:5-11,58-62`). -/
def PairAccessorsCorrect : Prop :=
  ∀ {A B : Type} (p : Pair A B),
    JuliaLean.base.pair.firstindex p = one64 ∧ JuliaLean.base.pair.lastindex p = two64 ∧ JuliaLean.base.pair.length p = two64 ∧
    JuliaLean.base.pair.first p = p.first ∧ JuliaLean.base.pair.last p = p.second

theorem pairAccessorsCorrect : PairAccessorsCorrect := by
  intro A B p
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Iteration, indexing, and accessors treat a pair as a two-element collection, while preserving
all conversion behavior of a `Real` index (`base/pair.jl:5-11,41-42,54-62`). -/
def PairIterIndexCorrect : Prop :=
  PairIterationFields ∧ PairIndexedIterationCorrect ∧ PairAccessorsCorrect ∧ PairGetindexCorrect

theorem pairIterIndexCorrect : PairIterIndexCorrect :=
  ⟨pairIterationFields, pairIndexedIterationCorrect, pairAccessorsCorrect, pairGetindexCorrect⟩

/-! ## Comparison laws -/

/-- `isequal` is the equivalence relation associated with a strict weak order. -/
structure WeakOrder (A : Type) where
  equal : A → A → Bool
  less : A → A → Bool
  irreflexive : ∀ a, less a a = false
  transitive : ∀ a b c, less a b = true → less b c = true → less a c = true
  equalIffIncomparable : ∀ a b,
    (less a b = false ∧ less b a = false) ↔ equal a b = true
  equivalentTransitive : ∀ a b c,
    equal a b = true → equal b c = true → equal a c = true

/-! Proof-internal facts about strict weak orders on the pair fields. The Pair method theorem below
uses them only through the proven `pairLess_matches_model` equivalence. -/
private theorem equalSymm {A : Type} (o : WeakOrder A) {a b : A}
    (h : o.equal a b = true) : o.equal b a = true := by
  have hab := (o.equalIffIncomparable a b).2 h
  exact (o.equalIffIncomparable b a).1 ⟨hab.2, hab.1⟩


private theorem lessOfEqLess {A : Type} (o : WeakOrder A) {a b c : A}
    (hab : o.equal a b = true) (hbc : o.less b c = true) : o.less a c = true := by
  cases hac : o.less a c with
  | true => rfl
  | false =>
    have hca : o.less c a = false := by
      cases h : o.less c a with
      | false => rfl
      | true =>
        have hba := o.transitive b c a hbc h
        have hnot := (o.equalIffIncomparable a b).2 hab
        have hless := hnot.2
        rw [hba] at hless
        cases hless
    have hacEq := (o.equalIffIncomparable a c).1 ⟨hac, hca⟩
    have hbaEq := equalSymm o hab
    have hbcEq := o.equivalentTransitive b a c hbaEq hacEq
    have hnot := (o.equalIffIncomparable b c).2 hbcEq
    have hless := hnot.1
    rw [hbc] at hless
    cases hless

private theorem lessOfLessEq {A : Type} (o : WeakOrder A) {a b c : A}
    (hab : o.less a b = true) (hbc : o.equal b c = true) : o.less a c = true := by
  cases hac : o.less a c with
  | true => rfl
  | false =>
    have hca : o.less c a = false := by
      cases h : o.less c a with
      | false => rfl
      | true =>
        have hcb := o.transitive c a b h hab
        have hnot := (o.equalIffIncomparable b c).2 hbc
        have hless := hnot.2
        rw [hcb] at hless
        cases hless
    have hacEq := (o.equalIffIncomparable a c).1 ⟨hac, hca⟩
    have hcbEq := equalSymm o hbc
    have habEq := o.equivalentTransitive a c b hacEq hcbEq
    have hnot := (o.equalIffIncomparable a b).2 habEq
    have hless := hnot.1
    rw [hab] at hless
    cases hless

/-! Three-valued `&` specification supplied to the source model's generic `bitAnd` parameter. -/
def missingAnd (a b : Option Bool) : Option Bool :=
  match a, b with
  | some false, _ => some false
  | _, some false => some false
  | some true, some true => some true
  | _, _ => none


/-! Proof-internal lexicographic reference. The source method equivalence is proved immediately
below; registered statements use `JuliaLean.base.pair.isless` directly. -/
def pairLess {A B : Type} (oA : WeakOrder A) (oB : WeakOrder B)
    (p q : Pair A B) : Bool :=
  if !oA.equal p.first q.first then oA.less p.first q.first else oB.less p.second q.second

theorem pairLess_matches_model {A B : Type} (oA : WeakOrder A) (oB : WeakOrder B)
    (p q : Pair A B) :
    JuliaLean.base.pair.isless (fun a b => .ok (oA.equal a b))
      (fun a b => .ok (oA.less a b)) (fun a b => .ok (oB.less a b)) p q =
        .ok (pairLess oA oB p q) := by
  simp [JuliaLean.base.pair.isless, pairLess, bind, Except.bind, pure, Except.pure]

theorem pairIsequal_matches_model {A B : Type} (oA : WeakOrder A) (oB : WeakOrder B)
    (p q : Pair A B) :
    JuliaLean.base.pair.isequal (fun a b => .ok (.bool (oA.equal a b)))
      (fun a b => .ok (.bool (oB.equal a b))) p q =
        .ok (oA.equal p.first q.first && oB.equal p.second q.second) := by
  simp [JuliaLean.base.pair.isequal, JuliaLean.base.pair.assertBool, bind, Except.bind, pure, Except.pure]


/-! Proof-internal laws for `pairLess`, used only through `pairLess_matches_model`. -/
theorem pairLess_eq {A B : Type} (oA : WeakOrder A) (oB : WeakOrder B)
    (p q : Pair A B) :
    pairLess oA oB p q =
      if oA.equal p.first q.first = true then oB.less p.second q.second
      else oA.less p.first q.first := by
  by_cases h : oA.equal p.first q.first = true <;> simp [pairLess, h]

theorem pairLessIrreflexive {A B : Type} (oA : WeakOrder A) (oB : WeakOrder B)
    (p : Pair A B) : pairLess oA oB p p = false := by
  have heq : oA.equal p.first p.first = true :=
    (oA.equalIffIncomparable p.first p.first).1 ⟨oA.irreflexive _, oA.irreflexive _⟩
  simp [pairLess, heq, oB.irreflexive]

theorem pairLessTransitive {A B : Type} (oA : WeakOrder A) (oB : WeakOrder B)
    (p q r : Pair A B) (hpq : pairLess oA oB p q = true)
    (hqr : pairLess oA oB q r = true) : pairLess oA oB p r = true := by
  rw [pairLess_eq oA oB p q] at hpq
  rw [pairLess_eq oA oB q r] at hqr
  rw [pairLess_eq oA oB p r]
  by_cases e1 : oA.equal p.first q.first = true
  · by_cases e2 : oA.equal q.first r.first = true
    · have e3 := oA.equivalentTransitive p.first q.first r.first e1 e2
      simp [e1, e2, e3] at hpq hqr ⊢
      exact oB.transitive p.second q.second r.second hpq hqr
    · simp [e1, e2] at hpq hqr
      have hFirst := lessOfEqLess oA e1 hqr
      have e3 : ¬ oA.equal p.first r.first = true := by
        intro heq
        have hnot := (oA.equalIffIncomparable p.first r.first).2 heq
        have hless := hnot.1
        rw [hFirst] at hless
        cases hless
      simp [e3] at hpq hqr ⊢
      exact hFirst
  · by_cases e2 : oA.equal q.first r.first = true
    · simp [e1, e2] at hpq hqr
      have hFirst := lessOfLessEq oA hpq e2
      have e3 : ¬ oA.equal p.first r.first = true := by
        intro heq
        have hnot := (oA.equalIffIncomparable p.first r.first).2 heq
        have hless := hnot.1
        rw [hFirst] at hless
        cases hless
      simp [e3] at hpq hqr ⊢
      exact hFirst
    · simp [e1, e2] at hpq hqr
      have hFirst := oA.transitive p.first q.first r.first hpq hqr
      have e3 : ¬ oA.equal p.first r.first = true := by
        intro heq
        have hnot := (oA.equalIffIncomparable p.first r.first).2 heq
        have hless := hnot.1
        rw [hFirst] at hless
        cases hless
      simp [e3] at hpq hqr ⊢
      exact hFirst

theorem pairLessIncomparableIff {A B : Type} (oA : WeakOrder A) (oB : WeakOrder B)
    (p q : Pair A B) :
    (pairLess oA oB p q = false ∧ pairLess oA oB q p = false) ↔
      (oA.equal p.first q.first = true ∧ oB.equal p.second q.second = true) := by
  constructor
  · intro h
    have hpq := h.1
    have hqp := h.2
    rw [pairLess_eq oA oB p q] at hpq
    rw [pairLess_eq oA oB q p] at hqp
    by_cases e1 : oA.equal p.first q.first = true
    · have e2 := equalSymm oA e1
      have l1 : oB.less p.second q.second = false := by simpa [e1] using hpq
      have l2 : oB.less q.second p.second = false := by simpa [e2] using hqp
      exact ⟨e1, (oB.equalIffIncomparable _ _).1 ⟨l1, l2⟩⟩
    · have l1 : oA.less p.first q.first = false := by simpa [e1] using hpq
      have e2 : ¬ oA.equal q.first p.first = true := by
        intro heq
        exact e1 (equalSymm oA heq)
      have l2 : oA.less q.first p.first = false := by simpa [e2] using hqp
      have hEq := (oA.equalIffIncomparable _ _).1 ⟨l1, l2⟩
      exact False.elim (e1 hEq)
  · intro h
    rcases h with ⟨e1, e2⟩
    have e1' := equalSymm oA e1
    have e2' := equalSymm oB e2
    have l1 := (oB.equalIffIncomparable _ _).2 e2
    have l2 := (oB.equalIffIncomparable _ _).2 e2'
    constructor
    · rw [pairLess_eq oA oB p q]
      simp [e1, l1.1]
    · rw [pairLess_eq oA oB q p]
      simp [e1', l2.1]

theorem pairLessWeakOrder {A B : Type} (oA : WeakOrder A) (oB : WeakOrder B) :
    (∀ p : Pair A B, pairLess oA oB p p = false) ∧
    (∀ p q r : Pair A B, pairLess oA oB p q = true → pairLess oA oB q r = true →
      pairLess oA oB p r = true) ∧
    (∀ p q : Pair A B,
      (pairLess oA oB p q = false ∧ pairLess oA oB q p = false) ↔
        (oA.equal p.first q.first = true ∧ oB.equal p.second q.second = true)) := by
  exact ⟨pairLessIrreflexive oA oB, pairLessTransitive oA oB, pairLessIncomparableIff oA oB⟩

theorem pairIslessOrder {A B : Type} (oA : WeakOrder A) (oB : WeakOrder B) :
    (∀ p : Pair A B,
      JuliaLean.base.pair.isless (fun a b => .ok (oA.equal a b))
        (fun a b => .ok (oA.less a b)) (fun a b => .ok (oB.less a b)) p p = .ok false) ∧
    (∀ p q r : Pair A B,
      JuliaLean.base.pair.isless (fun a b => .ok (oA.equal a b))
        (fun a b => .ok (oA.less a b)) (fun a b => .ok (oB.less a b)) p q = .ok true →
      JuliaLean.base.pair.isless (fun a b => .ok (oA.equal a b))
        (fun a b => .ok (oA.less a b)) (fun a b => .ok (oB.less a b)) q r = .ok true →
      JuliaLean.base.pair.isless (fun a b => .ok (oA.equal a b))
        (fun a b => .ok (oA.less a b)) (fun a b => .ok (oB.less a b)) p r = .ok true) ∧
    (∀ p q : Pair A B,
      (JuliaLean.base.pair.isless (fun a b => .ok (oA.equal a b))
          (fun a b => .ok (oA.less a b)) (fun a b => .ok (oB.less a b)) p q = .ok false ∧
        JuliaLean.base.pair.isless (fun a b => .ok (oA.equal a b))
          (fun a b => .ok (oA.less a b)) (fun a b => .ok (oB.less a b)) q p = .ok false) ↔
      JuliaLean.base.pair.isequal (fun a b => .ok (.bool (oA.equal a b)))
        (fun a b => .ok (.bool (oB.equal a b))) p q = .ok true) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p
    rw [pairLess_matches_model]
    exact congrArg Except.ok (pairLessIrreflexive oA oB p)
  · intro p q r hpq hqr
    rw [pairLess_matches_model] at hpq hqr
    injection hpq with hpq'
    injection hqr with hqr'
    rw [pairLess_matches_model]
    exact congrArg Except.ok (pairLessTransitive oA oB p q r hpq' hqr')
  · intro p q
    constructor
    · intro h
      have hpq := h.1
      have hqp := h.2
      rw [pairLess_matches_model] at hpq
      rw [pairLess_matches_model] at hqp
      injection hpq with hpq'
      injection hqp with hqp'
      have hfields := (pairLessIncomparableIff oA oB p q).1 ⟨hpq', hqp'⟩
      rw [pairIsequal_matches_model]
      simp [hfields]
    · intro h
      rw [pairIsequal_matches_model] at h
      injection h with hfields
      simp only [Bool.and_eq_true] at hfields
      have hless := (pairLessIncomparableIff oA oB p q).2 hfields
      constructor
      · rw [pairLess_matches_model]
        exact congrArg Except.ok hless.1
      · rw [pairLess_matches_model]
        exact congrArg Except.ok hless.2

/-- Pair `==` combines both field results with three-valued `&`; `isequal` asserts each field
result is `Bool` in order; equal pairs hash equally; `isless` is lexicographic and eager. -/
def PairCompareCorrect : Prop :=
  (∀ {A B C D : Type} (eqFirst : A → C → Option Bool) (eqSecond : B → D → Option Bool)
      (p : Pair A B) (q : Pair C D),
    JuliaLean.base.pair.eq (fun a c => .ok (eqFirst a c))
      (fun b d => .ok (eqSecond b d)) (fun a b => .ok (missingAnd a b)) p q =
        .ok (missingAnd (eqFirst p.first q.first) (eqSecond p.second q.second))) ∧
  (∀ {A B : Type} (oA : WeakOrder A) (oB : WeakOrder B) (p q : Pair A B),
    JuliaLean.base.pair.isequal (fun a b => .ok (.bool (oA.equal a b)))
      (fun a b => .ok (.bool (oB.equal a b))) p q =
        .ok (oA.equal p.first q.first && oB.equal p.second q.second) ∧
    JuliaLean.base.pair.isless (fun a b => .ok (oA.equal a b))
      (fun a b => .ok (oA.less a b)) (fun a b => .ok (oB.less a b)) p q =
        .ok (if !oA.equal p.first q.first then oA.less p.first q.first
          else oB.less p.second q.second)) ∧
  (∀ {A B : Type} (oA : WeakOrder A) (oB : WeakOrder B) (width : UIntWidth)
      (xor : JInt width.intTy → JInt width.intTy → Jl (JInt width.intTy))
      (hashFirst : A → JInt width.intTy → Jl (JInt width.intTy))
      (hashSecond : B → JInt width.intTy → Jl (JInt width.intTy)),
    (∀ a c h, oA.equal a c = true → hashFirst a h = hashFirst c h) →
    (∀ b d h, oB.equal b d = true → hashSecond b h = hashSecond d h) →
    ∀ (p q : Pair A B) (h : JInt width.intTy),
      oA.equal p.first q.first = true → oB.equal p.second q.second = true →
      JuliaLean.base.pair.hash width xor hashFirst hashSecond p h =
        JuliaLean.base.pair.hash width xor hashFirst hashSecond q h) ∧
  (∀ {A B : Type} (oA : WeakOrder A) (oB : WeakOrder B),
    (∀ p : Pair A B,
      JuliaLean.base.pair.isless (fun a b => .ok (oA.equal a b))
        (fun a b => .ok (oA.less a b)) (fun a b => .ok (oB.less a b)) p p = .ok false) ∧
    (∀ p q r : Pair A B,
      JuliaLean.base.pair.isless (fun a b => .ok (oA.equal a b))
        (fun a b => .ok (oA.less a b)) (fun a b => .ok (oB.less a b)) p q = .ok true →
      JuliaLean.base.pair.isless (fun a b => .ok (oA.equal a b))
        (fun a b => .ok (oA.less a b)) (fun a b => .ok (oB.less a b)) q r = .ok true →
      JuliaLean.base.pair.isless (fun a b => .ok (oA.equal a b))
        (fun a b => .ok (oA.less a b)) (fun a b => .ok (oB.less a b)) p r = .ok true) ∧
    (∀ p q : Pair A B,
      (JuliaLean.base.pair.isless (fun a b => .ok (oA.equal a b))
          (fun a b => .ok (oA.less a b)) (fun a b => .ok (oB.less a b)) p q = .ok false ∧
        JuliaLean.base.pair.isless (fun a b => .ok (oA.equal a b))
          (fun a b => .ok (oA.less a b)) (fun a b => .ok (oB.less a b)) q p = .ok false) ↔
      JuliaLean.base.pair.isequal (fun a b => .ok (.bool (oA.equal a b)))
        (fun a b => .ok (.bool (oB.equal a b))) p q = .ok true)) ∧
  (∀ {A B C D : Type} (p : Pair A B) (q : Pair C D) (e : JlError),
    JuliaLean.base.pair.isequal (fun _ _ => .ok (.bool false))
      (fun _ _ => .error (.julia e)) p q = .error (.julia e) ∧
    JuliaLean.base.pair.isequal (fun _ _ => .ok .other)
      (fun _ _ => .error (.julia e)) p q = .error .typeError ∧
    JuliaLean.base.pair.isequal (fun _ _ => .ok (.bool false))
      (fun _ _ => .ok .other) p q = .error .typeError ∧
    JuliaLean.base.pair.isless (fun _ _ => .ok false) (fun _ _ => .ok true)
      (fun _ _ => .error e) p q = .error e)

theorem pairCompareCorrect : PairCompareCorrect := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro A B C D eqFirst eqSecond p q
    rfl
  · intro A B oA oB p q
    exact ⟨pairIsequal_matches_model oA oB p q,
      by simpa [pairLess] using pairLess_matches_model oA oB p q⟩
  · intro A B oA oB width xor hashFirst hashSecond hFirst hSecond p q h heqFirst heqSecond
    unfold JuliaLean.base.pair.hash
    cases hx : xor (JuliaLean.base.pair.hashSeed width) h with
    | error e => simp [bind, Except.bind]
    | ok salted =>
      simp only [bind, Except.bind]
      rw [hFirst p.first q.first salted heqFirst]
      cases hvalue : hashFirst q.first salted with
      | error e => rfl
      | ok firstHash => simp [hSecond p.second q.second firstHash heqSecond]
  · exact pairIslessOrder
  · intro A B C D p q e
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [JuliaLean.base.pair.isequal, JuliaLean.base.pair.assertBool, bind, Except.bind]
    · simp [JuliaLean.base.pair.isequal, JuliaLean.base.pair.assertBool, bind, Except.bind]
    · simp [JuliaLean.base.pair.isequal, JuliaLean.base.pair.assertBool, bind, Except.bind]
    · simp [JuliaLean.base.pair.isless, bind, Except.bind]

/-! ## Type-level pair methods -/

/-- Pair reversal restores its fields; `eltype` is the coproduct of both field types; conversions
preserve order and target types; `promote_rule` promotes each field independently
(`base/pair.jl:40,56,64-74`). -/
def PairTypesCorrect : Prop :=
  (∀ {A B : Type} (p : Pair A B),
    (JuliaLean.base.pair.reverse p).first = p.second ∧ (JuliaLean.base.pair.reverse p).second = p.first ∧
      JuliaLean.base.pair.reverse (JuliaLean.base.pair.reverse p) = p) ∧
  (∀ (target : PairType) (C : Type) (fromFirst : target.first → C)
      (fromSecond : target.second → C),
    ∃ extend : JuliaLean.base.pair.eltype target → C,
      (∀ a, extend (Sum.inl a) = fromFirst a) ∧
      (∀ b, extend (Sum.inr b) = fromSecond b) ∧
      ∀ other, (∀ a, other (Sum.inl a) = fromFirst a) →
        (∀ b, other (Sum.inr b) = fromSecond b) → other = extend) ∧
  (∀ (target : PairType) (p : Pair target.first target.second), JuliaLean.base.pair.convertSame target p = p) ∧
  (∀ (target : PairType) {X Y : Type}
      (isFirst : X → Bool) (upcastFirst : X → target.first)
      (convertFirst : X → Jl target.first)
      (isSecond : Y → Bool) (upcastSecond : Y → target.second)
      (convertSecond : Y → Jl target.second) (p : Pair X Y),
    (isFirst p.first = true → isSecond p.second = true →
      JuliaLean.base.pair.convert target isFirst upcastFirst convertFirst isSecond upcastSecond convertSecond p =
        .ok ⟨upcastFirst p.first, upcastSecond p.second⟩) ∧
    (∀ e, isFirst p.first = false → convertFirst p.first = .error e →
      JuliaLean.base.pair.convert target isFirst upcastFirst convertFirst isSecond upcastSecond convertSecond p =
        .error e) ∧
    (∀ a e, isFirst p.first = false → convertFirst p.first = .ok a →
      isSecond p.second = false → convertSecond p.second = .error e →
      JuliaLean.base.pair.convert target isFirst upcastFirst convertFirst isSecond upcastSecond convertSecond p =
        .error e) ∧
    (∀ a b,
      (if isFirst p.first then .ok (upcastFirst p.first) else convertFirst p.first) = .ok a →
      (if isSecond p.second then .ok (upcastSecond p.second) else convertSecond p.second) = .ok b →
      JuliaLean.base.pair.convert target isFirst upcastFirst convertFirst isSecond upcastSecond convertSecond p =
        .ok ⟨a, b⟩)) ∧
  (∀ (promoteType : Type → Type → Type) (left right : PairType),
    (JuliaLean.base.pair.promoteRule promoteType left right).first =
      promoteType left.first right.first ∧
    (JuliaLean.base.pair.promoteRule promoteType left right).second =
      promoteType left.second right.second) ∧
  (∀ (promoteType : Type → Type → Type),
    (∀ A B : Type, promoteType A B = promoteType B A) →
    ∀ (left right : PairType), JuliaLean.base.pair.promoteRule promoteType left right =
      JuliaLean.base.pair.promoteRule promoteType right left)

theorem pairTypesCorrect : PairTypesCorrect := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro A B p
    exact ⟨rfl, rfl, rfl⟩
  · intro target C fromFirst fromSecond
    refine ⟨Sum.elim fromFirst fromSecond, ?_, ?_, ?_⟩
    · intro a
      rfl
    · intro b
      rfl
    · intro other hFirst hSecond
      funext value
      cases value with
      | inl a => exact hFirst a
      | inr b => exact hSecond b
  · intro target p
    rfl
  · intro target X Y isFirst upcastFirst convertFirst isSecond upcastSecond convertSecond p
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hFirst hSecond
      simp [JuliaLean.base.pair.convert, hFirst, hSecond, bind, Except.bind, pure, Except.pure]
    · intro e hFirst hConvert
      simp [JuliaLean.base.pair.convert, hFirst, hConvert, bind, Except.bind]
    · intro a e hFirst hConvertFirst hSecond hConvertSecond
      simp [JuliaLean.base.pair.convert, hFirst, hConvertFirst, hSecond, hConvertSecond,
        bind, Except.bind]
    · intro a b hFirst hSecond
      cases h1 : isFirst p.first <;> cases h2 : isSecond p.second <;>
        simp_all [JuliaLean.base.pair.convert, bind, Except.bind, pure, Except.pure]
  · intro promoteType left right
    exact ⟨rfl, rfl⟩
  · intro promoteType hpromote left right
    cases left with
    | mk leftFirst leftSecond =>
      cases right with
      | mk rightFirst rightSecond =>
        simp [JuliaLean.base.pair.promoteRule, hpromote leftFirst rightFirst, hpromote leftSecond rightSecond]

/-! ## Registry entries -/

def entries : List Entry := [
  { id := "sorttuplescov-pair-iter-index",
    juliaFile := "base/pair.jl",
    juliaFns := ["iterate(p::Pair,i)", "indexed_iterate(p::Pair,i,state)",
      "getindex(p::Pair,i::Int)", "getindex(p::Pair,i::Real)", "firstindex(p::Pair)",
      "lastindex(p::Pair)", "length(p::Pair)", "first(p::Pair)", "last(p::Pair)"],
    statement := "Pair iterates its fields in order, converts Real indices to Int (preserving InexactError for non-integral values), and has the documented length, indices, first, and last values.",
    source := "base/pair.jl:5-11,41-42,54-62",
    status := .proven,
    prop := ``PairIterIndexCorrect,
    thm := some ``pairIterIndexCorrect },
  { id := "sorttuplescov-pair-compare",
    juliaFile := "base/pair.jl",
    juliaFns := ["==(p::Pair,q::Pair)", "isequal(p::Pair,q::Pair)", "isless(p::Pair,q::Pair)",
      "hash(p::Pair,h::UInt)"],
    statement := "Pair equality combines both fields, isequal asserts Bool results in order, and hash respects the product equivalence; isless is lexicographic and strict weak for lawful field orders, and eager second-field errors propagate.",
    source := "base/pair.jl:46,49-53; hash/order invariants",
    status := .proven,
    prop := ``PairCompareCorrect,
    thm := some ``pairCompareCorrect },
  { id := "sorttuplescov-pair-types",
    juliaFile := "base/pair.jl",
    juliaFns := ["reverse(p::Pair{A,B})", "eltype(::Type{Pair{A,B}})",
      "convert(::Type{Pair{A,B}},x::Pair{A,B})", "convert(::Type{Pair{A,B}},x::Pair)",
      "promote_rule(::Type{Pair{A1,B1}},::Type{Pair{A2,B2}})"],
    statement := "Pair reverse swaps and restores fields, eltype is the coproduct of both field types, matching conversion preserves the pair, field conversion preserves order and target types, and promotion applies promote_type independently to corresponding fields.",
    source := "base/pair.jl:40,56,64-74",
    status := .proven,
    prop := ``PairTypesCorrect,
    thm := some ``pairTypesCorrect },
  { id := "sorttuplescov-pair-iteration-fields",
    juliaFile := "base/pair.jl",
    juliaFns := ["iterate(p::Pair,i)"],
    statement := "Pair iteration yields first then second, stops after the second field, and raises BoundsError when its initial field index is zero.",
    source := "base/pair.jl:41; Pair docstring",
    status := .proven,
    prop := ``PairIterationFields,
    thm := some ``pairIterationFields },
  { id := "sorttuplescov-pair-generic-index",
    juliaFile := "base/pair.jl",
    juliaFns := ["getindex(p::Pair,i::Int)", "getindex(p::Pair,i::Real)"],
    statement := "Pair indexing reads fields at Int indices 1 and 2; the Real overload converts to Int first, propagates conversion errors, and raises BoundsError for other converted indices.",
    source := "base/pair.jl:54-55",
    status := .proven,
    prop := ``PairGetindexCorrect,
    thm := some ``pairGetindexCorrect }
]

end JuliaLean.Proofs.base.pair
