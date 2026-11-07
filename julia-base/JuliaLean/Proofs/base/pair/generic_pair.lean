import JuliaLean.base.pair
import JuliaLean.Proofs.base.pair.value_pair
/-! Generic and effect-aware models for the remaining `base/pair.jl` method
coverage findings. -/

namespace JuliaLean.SortTuplesCov

open JuliaLean.Tuples (R Err)

def PairIterationGenericCorrect : Prop :=
  (∀ (P S V : Type) gt field add (p : P) (s : S),
    pairIterateGeneric (V := V) gt field add p s = do
      if ← gt s then pure none else pure (some ((← field p s), (← add s)))) ∧
  (∀ (P I S V : Type) field add (p : P) (i : I) (state : S),
    pairIndexedIterateGeneric (V := V) field add p i state = do
      pure ((← field p i), (← add i)))

theorem pairIterationGenericCorrect : PairIterationGenericCorrect := by
  exact ⟨fun _ _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ _ => rfl⟩

def PairHashFixedCorrect : Prop :=
  (∀ (A B : Type) hashA hashB (p : HPair A B) h,
    pairHashFixed 64 hashA hashB p h =
      hashB p.second (hashA p.first ((0x94cb2bb20a28ce96 ^^^ h) % 2 ^ 64) % 2 ^ 64) % 2 ^ 64) ∧
  (∀ (A B : Type) hashA hashB (p : HPair A B) h,
    pairHashFixed 32 hashA hashB p h =
      hashB p.second (hashA p.first ((0x1f60a087 ^^^ h) % 2 ^ 32) % 2 ^ 32) % 2 ^ 32)

theorem pairHashFixedCorrect : PairHashFixedCorrect := by
  constructor <;> intros <;> rfl

def PairEagerCompareCorrect : Prop :=
  (∀ (A B : Type) eqA eqB (p q : HPair A B), pairIsequalEager eqA eqB p q = do
    let a ← eqA p.first q.first
    let b ← eqB p.second q.second
    pure (a && b)) ∧
  (∀ (A B : Type) eqA ltA ltB (p q : HPair A B),
    pairIslessEager eqA ltA ltB p q = do
      let eq ← eqA p.first q.first
      let firstLess ← ltA p.first q.first
      let secondLess ← ltB p.second q.second
      pure (if !eq then firstLess else secondLess))

theorem pairEagerCompareCorrect : PairEagerCompareCorrect := by
  exact ⟨fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl⟩

def PairGetindexCorrect : Prop :=
  (∀ (V : Type) (p : HPair V V), pairGetindexInt p 1 = .ok p.first ∧
    pairGetindexInt p 2 = .ok p.second) ∧
  (∀ (X V : Type) convertInt (p : HPair V V) (i : X),
    pairGetindexRealGeneric convertInt p i = do pairGetindexInt p (← convertInt i))

theorem pairGetindexCorrect : PairGetindexCorrect := by
  exact ⟨by simp [pairGetindexInt], fun _ _ _ _ _ => rfl⟩

/-- Pair iteration yields the first and second fields, then terminates;
an invalid state below one produces a bounds error. -/
def PairIterationFields : Prop :=
  ∀ (V : Type) (p : HPair V V),
    let step := pairIterateGeneric (fun i : Int => .ok (decide (i > 2)))
      pairGetindexInt (fun i : Int => .ok (i + 1)) p
    step 1 = .ok (some (p.first, 2)) ∧
    step 2 = .ok (some (p.second, 3)) ∧
    step 3 = .ok none ∧
    step 0 = .error (.jl .boundsError)

theorem pairIterationFields : PairIterationFields := by
  intro V p
  simp [pairIterateGeneric, pairGetindexInt]

def PairTypedReverseCorrect : Prop :=
  ∀ (A B : Type) (p : HPair A B),
    (reverseHPair p).first = p.second ∧ (reverseHPair p).second = p.first ∧
      reverseHPair (reverseHPair p) = p

theorem pairTypedReverseCorrect : PairTypedReverseCorrect := by
  unfold PairTypedReverseCorrect
  intro A B p
  exact ⟨rfl, rfl, rfl⟩

def PairTypedConvertCorrect : Prop :=
  ∀ (T V : Type) (isa : V → T → Bool) (convert : T → V → R V)
      (A B : T) (p : HPair V V), convertTypedPair isa convert A B p = do
    let a ← if isa p.first A then pure p.first else convert A p.first
    let b ← if isa p.second B then pure p.second else convert B p.second
    pure ⟨A, B, a, b⟩

theorem pairTypedConvertCorrect : PairTypedConvertCorrect := by
  unfold PairTypedConvertCorrect
  intros
  rfl

end JuliaLean.SortTuplesCov
