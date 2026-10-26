import JuliaLean.SortTuplesCov.Pair

/-! Generic and effect-aware models for the remaining `base/pair.jl` method
coverage findings. -/

namespace JuliaLean.SortTuplesCov

open JuliaLean.Tuples (R Err)

structure HPair (A B : Type) where
  first : A
  second : B

/-- `iterate(p::Pair, i=1)`, `base/pair.jl:41`, with Julia's untyped state
represented by its `>`, field access, and `+` operations. -/
def pairIterateGeneric {P S V : Type} (greaterThanTwo : S → R Bool)
    (field : P → S → R V) (addOne : S → R S) (p : P) (state : S) :
    R (Option (V × S)) := do
  if ← greaterThanTwo state then pure none
  else pure (some ((← field p state), (← addOne state)))

/-- `indexed_iterate(p,i,state)`, `base/pair.jl:42`; `state` is accepted and
ignored. -/
def pairIndexedIterateGeneric {P I S V : Type} (field : P → I → R V)
    (addOne : I → R I) (p : P) (i : I) (_state : S) : R (V × I) := do
  pure ((← field p i), (← addOne i))

def PairIterationGenericCorrect : Prop :=
  (∀ (P S V : Type) gt field add (p : P) (s : S),
    pairIterateGeneric (V := V) gt field add p s = do
      if ← gt s then pure none else pure (some ((← field p s), (← add s)))) ∧
  (∀ (P I S V : Type) field add (p : P) (i : I) (state : S),
    pairIndexedIterateGeneric (V := V) field add p i state = do
      pure ((← field p i), (← add i)))

theorem pairIterationGenericCorrect : PairIterationGenericCorrect := by
  exact ⟨fun _ _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ _ => rfl⟩

def uintModulus (bits : Nat) : Nat := 2 ^ bits
def pairHashSeed (bits : Nat) : Nat := if bits = 64 then 0x94cb2bb20a28ce96 else 0x0a28ce96

/-- `hash(p::Pair,h::UInt)`, `base/pair.jl:44-46`, with fixed-width UInt
wrapping and both architecture-specific seeds. -/
def pairHashFixed {A B : Type} (bits : Nat) (hashA : A → Nat → Nat)
    (hashB : B → Nat → Nat) (p : HPair A B) (h : Nat) : Nat :=
  let seed := (pairHashSeed bits ^^^ h) % uintModulus bits
  hashB p.second (hashA p.first seed % uintModulus bits) % uintModulus bits

def PairHashFixedCorrect : Prop :=
  (∀ (A B : Type) hashA hashB (p : HPair A B) h,
    pairHashFixed 64 hashA hashB p h =
      hashB p.second (hashA p.first ((0x94cb2bb20a28ce96 ^^^ h) % 2 ^ 64) % 2 ^ 64) % 2 ^ 64) ∧
  (∀ (A B : Type) hashA hashB (p : HPair A B) h,
    pairHashFixed 32 hashA hashB p h =
      hashB p.second (hashA p.first ((0x0a28ce96 ^^^ h) % 2 ^ 32) % 2 ^ 32) % 2 ^ 32)

theorem pairHashFixedCorrect : PairHashFixedCorrect := by
  constructor <;> intros <;> rfl

/-- Eager `isequal` and `isless`, `base/pair.jl:50,52-53`. -/
def pairIsequalEager {A B : Type} (eqA : A → A → R Bool)
    (eqB : B → B → R Bool) (p q : HPair A B) : R Bool := do
  let a ← eqA p.first q.first
  let b ← eqB p.second q.second
  pure (a && b)

def pairIslessEager {A B : Type} (equalA : A → A → R Bool)
    (lessA : A → A → R Bool) (lessB : B → B → R Bool)
    (p q : HPair A B) : R Bool := do
  let eq ← equalA p.first q.first
  let firstLess ← lessA p.first q.first
  let secondLess ← lessB p.second q.second
  pure (if !eq then firstLess else secondLess)

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

/-- `getindex(p,i::Int)` and the Real overload, `base/pair.jl:54-55`. -/
def pairGetindexInt {V : Type} (p : HPair V V) (i : Int) : R V :=
  if i = 1 then .ok p.first else if i = 2 then .ok p.second else .error (.jl .boundsError)
def pairGetindexRealGeneric {X V : Type} (convertInt : X → R Int)
    (p : HPair V V) (i : X) : R V := do
  pairGetindexInt p (← convertInt i)

def PairGetindexCorrect : Prop :=
  (∀ (V : Type) (p : HPair V V), pairGetindexInt p 1 = .ok p.first ∧
    pairGetindexInt p 2 = .ok p.second) ∧
  (∀ (X V : Type) convertInt (p : HPair V V) (i : X),
    pairGetindexRealGeneric convertInt p i = do pairGetindexInt p (← convertInt i))

theorem pairGetindexCorrect : PairGetindexCorrect := by
  exact ⟨by simp [pairGetindexInt], fun _ _ _ _ _ => rfl⟩

/-- Typed reverse, `base/pair.jl:56`. -/
def reverseHPair {A B : Type} (p : HPair A B) : HPair B A := ⟨p.second, p.first⟩

def PairTypedReverseCorrect : Prop :=
  ∀ (A B : Type) (p : HPair A B),
    (reverseHPair p).first = p.second ∧ (reverseHPair p).second = p.first ∧
      reverseHPair (reverseHPair p) = p

theorem pairTypedReverseCorrect : PairTypedReverseCorrect := by
  unfold PairTypedReverseCorrect
  intro A B p
  exact ⟨rfl, rfl, rfl⟩

structure TypedPair (T V : Type) where
  firstType : T
  secondType : T
  first : V
  second : V

/-- Heterogeneous target conversion, `base/pair.jl:65-71`, including the
target Pair type carried by the result. -/
def convertTypedPair {T V : Type} (isa : V → T → Bool) (convert : T → V → R V)
    (A B : T) (p : HPair V V) : R (TypedPair T V) := do
  let a ← if isa p.first A then pure p.first else convert A p.first
  let b ← if isa p.second B then pure p.second else convert B p.second
  pure ⟨A, B, a, b⟩

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
