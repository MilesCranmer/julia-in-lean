import JuliaLean.base.pair
import JuliaLean.Proofs.base.tuple.sort_common
/-!
Model of `base/pair.jl` (master `bbfa0ce4150`).

A `Pair` holds two values of a universe `V`; element comparisons and hashing
are the abstract `Ops` of the tuple model (`none` is `missing` for `==`).
Types are an abstract `T` with `Union{A, B}` (`union`), `promote_type`
(`promote`), `isa` and `convert` (which may throw).
-/

namespace JuliaLean.SortTuplesCov

open JuliaLean
open JuliaLean.Tuples (R Err getfield bounds Ops Idx liftJ)

namespace Pair

variable {V : Type}

end Pair

open Pair

variable {V : Type}

/-! ## Properties -/

/-- Iteration and indexing of a `Pair` (`base/pair.jl:5-11,41-42,54-62`): a pair
iterates `first` then `second` and stops at state 3; `indexed_iterate` returns
the field and the next state; `p[i]` is the field for `i = 1, 2` of every
`Integer` type and every integral `Real`, `InexactError` for a non-integer, and
`BoundsError` otherwise; the index range is `1:2`, the length is 2, and
`first`/`last` return the fields. -/
def PairIterIndexCorrect : Prop :=
  ∀ (V : Type) (p : Pair V),
    iterate p 1 = .ok (some (p.first, 2)) ∧ iterate p 2 = .ok (some (p.second, 3)) ∧
    (∀ i, i > 2 → iterate p i = .ok none) ∧
    indexedIterate p 1 = .ok (p.first, 2) ∧ indexedIterate p 2 = .ok (p.second, 3) ∧
    (∀ i : Int, i ≠ 1 → i ≠ 2 → getindexInt p i = bounds ∧ indexedIterate p i = bounds) ∧
    (∀ ri : RealIdx, getindexReal p ri = (ri.toInt >>= fun j => getindexInt p j)) ∧
    getindexReal p .fractional = .error (.jl (.inexactError "Int64")) ∧
    firstindex p = 1 ∧ lastindex p = length p ∧ length p = 2 ∧
    firstOf p = p.first ∧ lastOf p = p.second

/-- `isless` on pairs is lexicographic (`base/pair.jl:52-53`) and, for elements
whose `isless` is a strict weak order with `isequal` as its equivalence, a
strict weak order whose equivalence is pair `isequal`; `isequal` pairs hash
equally when element `hash` respects `isequal`; `==` is the three-valued
conjunction of the element comparisons (`false` wins over `missing`). -/
def PairCompareCorrect : Prop :=
  ∀ (V : Type) (o : Ops V),
    (∀ p q, isequal o p q = (o.isequal p.first q.first && o.isequal p.second q.second)) ∧
    (∀ p q, eq o p q =
      if o.eq p.first q.first = some false ∨ o.eq p.second q.second = some false then some false
      else if o.eq p.first q.first = some true ∧ o.eq p.second q.second = some true then some true
      else none) ∧
    ((∀ a b h, o.isequal a b = true → o.hash a h = o.hash b h) →
      ∀ p q h, isequal o p q = true → hash o p h = hash o q h) ∧
    (JuliaLean.Tuples.Lawful o →
      (∀ p, isless o p p = false) ∧
      (∀ p q r, isless o p q = true → isless o q r = true → isless o p r = true) ∧
      (∀ p q, (isless o p q = false ∧ isless o q p = false) ↔ isequal o p q = true))

/-- `reverse(p)` swaps the fields and is an involution; the element type of
`Pair{A,B}` is `Union{A,B}`, so each field's type is below it when the union is
an upper bound; `convert(Pair{A,B}, x)` returns `x` for a `Pair{A,B}`, and
otherwise converts the fields that are not already of the target types, first
before second; `promote_rule` is symmetric when `promote_type` is
(`base/pair.jl:40,56,64-74`). -/
def PairTypesCorrect : Prop :=
  ∀ (V T : Type) (sub : T → T → Prop) (union : T → T → T) (promote : T → T → T)
    (isa : V → T → Bool) (conv : T → V → R V) (typeOf : V → T),
    (∀ p : Pair V, (reverse p).first = p.second ∧ (reverse p).second = p.first ∧
      reverse (reverse p) = p) ∧
    ((∀ a b, sub a (union a b) ∧ sub b (union a b)) → (∀ a b c, sub a b → sub b c → sub a c) →
      ∀ (p : Pair V) A B, sub (typeOf p.first) A → sub (typeOf p.second) B →
        sub (typeOf p.first) (Pair.eltype union A B) ∧ sub (typeOf p.second) (Pair.eltype union A B)) ∧
    (∀ A B (x : Pair V), Pair.convert isa conv A B true x = .ok x) ∧
    (∀ A B (x : Pair V), Pair.convert isa conv A B false x =
      match (if isa x.first A then .ok x.first else conv A x.first : R V) with
      | .error e => .error e
      | .ok a => match (if isa x.second B then .ok x.second else conv B x.second : R V) with
        | .error e => .error e
        | .ok b => .ok ⟨a, b⟩) ∧
    ((∀ a b, promote a b = promote b a) → ∀ A1 B1 A2 B2,
      promoteRule promote A1 B1 A2 B2 = promoteRule promote A2 B2 A1 B1)

/-! ## Proofs -/

theorem pairIterIndexCorrect : PairIterIndexCorrect := by
  intro V p
  have g1 : getfield p.fields 1 = .ok p.first := rfl
  have g2 : getfield p.fields 2 = .ok p.second := rfl
  have gn : ∀ i : Int, i ≠ 1 → i ≠ 2 → getfield p.fields i = bounds := by
    intro i h1 h2
    exact getfield_none (by simp only [Pair.fields, List.length_cons, List.length_nil]; omega)
  refine ⟨rfl, rfl, ?_, rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro i hi; simp [iterate, hi]
  · intro i h1 h2
    refine ⟨gn i h1 h2, ?_⟩
    simp [indexedIterate, gn i h1 h2, bind, Except.bind, bounds]
  · intro ri
    cases ri with
    | integer i =>
      cases i with
      | int t v =>
        cases t
        all_goals first
          | rfl
          | (have hc : JInt.convert (IntTy.i64.name) .i64 v.val = .ok v := dif_pos v.property
             show getindexInt p v.val = _
             simp only [RealIdx.toInt, hc, liftJ, bind, Except.bind, pure, Except.pure])
      | bool b => rfl
    | integral n => rfl
    | fractional => rfl

theorem pairCompareCorrect : PairCompareCorrect := by
  intro V o
  refine ⟨fun p q => rfl, ?_, ?_, ?_⟩
  · intro p q
    simp only [eq]
    cases o.eq p.first q.first with
    | none =>
      cases h2 : o.eq p.second q.second with
      | none => rfl
      | some b => cases b <;> rfl
    | some a =>
      cases h2 : o.eq p.second q.second with
      | none => cases a <;> rfl
      | some b => cases a <;> cases b <;> rfl
  · intro hh p q h hq
    simp only [isequal, Bool.and_eq_true] at hq
    unfold Pair.hash
    rw [hh _ _ _ hq.1, hh _ _ _ hq.2]
  · intro hl
    have E : ∀ p q : Pair V, isless o p q =
        if o.isequal p.first q.first = true then o.isless p.second q.second
        else o.isless p.first q.first := by
      intro p q
      unfold isless
      cases o.isequal p.first q.first <;> rfl
    refine ⟨?_, ?_, ?_⟩
    · intro p
      have : o.isequal p.first p.first = true := isequal_of_not hl (hl.irrefl _) (hl.irrefl _)
      rw [E, if_pos this, hl.irrefl]
    · intro p q r hpq hqr
      rw [E] at hpq hqr ⊢
      by_cases e1 : o.isequal p.first q.first = true <;>
        by_cases e2 : o.isequal q.first r.first = true <;>
        simp only [e1, e2, if_true, if_false] at hpq hqr
      · rw [if_pos (hl.incompTrans _ _ _ e1 e2)]
        exact hl.trans _ _ _ hpq hqr
      · have h := isless_of_eq_lt hl e1 hqr
        rw [if_neg (by rw [isequal_of_isless hl h]; simp)]
        exact h
      · have h := isless_of_lt_eq hl hpq e2
        rw [if_neg (by rw [isequal_of_isless hl h]; simp)]
        exact h
      · have h := hl.trans _ _ _ hpq hqr
        rw [if_neg (by rw [isequal_of_isless hl h]; simp)]
        exact h
    · intro p q
      rw [E, E]
      constructor
      · intro ⟨h1, h2⟩
        by_cases e : o.isequal p.first q.first = true
        · have e' : o.isequal q.first p.first = true := by rw [isequal_symm hl]; exact e
          rw [if_pos e] at h1
          rw [if_pos e'] at h2
          simp only [isequal, e, Bool.true_and]
          exact isequal_of_not hl h1 h2
        · have e' : ¬ o.isequal q.first p.first = true := by rw [isequal_symm hl]; exact e
          rw [if_neg e] at h1
          rw [if_neg e'] at h2
          exact absurd (isequal_of_not hl h1 h2) e
      · intro h
        simp only [isequal, Bool.and_eq_true] at h
        have e' : o.isequal q.first p.first = true := by rw [isequal_symm hl]; exact h.1
        rw [if_pos h.1, if_pos e']
        exact isless_of_isequal hl h.2

theorem pairTypesCorrect : PairTypesCorrect := by
  intro V T sub union promote isa conv typeOf
  refine ⟨fun p => ⟨rfl, rfl, rfl⟩, ?_, fun A B x => rfl, ?_, ?_⟩
  · intro hu htr p A B ha hb
    exact ⟨htr _ _ _ ha (hu A B).1, htr _ _ _ hb (hu A B).2⟩
  · intro A B x
    unfold Pair.convert
    cases isa x.first A <;> cases isa x.second B <;> simp only [↓reduceIte, Bool.false_eq_true] <;>
      (try cases conv A x.first) <;> (try cases conv B x.second) <;> rfl
  · intro hs A1 B1 A2 B2
    simp [promoteRule, hs A1 A2, hs B1 B2]

end JuliaLean.SortTuplesCov
