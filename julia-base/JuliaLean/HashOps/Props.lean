import JuliaLean.HashOps.Model
import JuliaLean.Tuples.Props

namespace JuliaLean.HashOps

open JuliaLean JuliaLean.Promotion

/-- Hashing equal machine integers of any widths through 64 bits makes the same
primitive-call term for every seed. -/
def SmallIntegerHashConsistency : Prop :=
  ∀ (t s : IntTy) (x : JInt t) (y : JInt s) (h : HTerm),
    t ≠ .i128 → t ≠ .u128 → s ≠ .i128 → s ≠ .u128 → x.val = y.val →
    hashNum (.int t x) h = hashNum (.int s y) h

/-- The generic `hash(::Real)` path is consistent whenever `decompose` gives
equal normalized triples and the intermediate integer storage type is the same.
This is the source obligation shared by Int128, UInt128, BigInt, BigFloat and
generic Rational/Real implementations. -/
def DecomposedHashConsistency : Prop :=
  ∀ (α : Type) (eqv : α → α → Bool) (decompose : α → Decomposition)
    (numTy : α → IntTy),
    (∀ x y, eqv x y = true → decompose x = decompose y ∧ numTy x = numTy y) →
    ∀ x y h, eqv x y = true →
      hashDecomposed (numTy x) (decompose x) h =
      hashDecomposed (numTy y) (decompose y) h

/-- Valid byte-backed strings and character-iterated AbstractStrings with the
same character sequence hash equally for every seed. -/
def StringHashConsistency : Prop :=
  ∀ a b : Text, a.Valid → b.Valid → a.chars = b.chars →
    ∀ h, hashText a h = hashText b h

/-- AnnotatedString ordering must use the equivalence classes of isequal. -/
def AnnotatedStringOrder : Prop :=
  ∀ a b : AnnotatedText,
    [annotatedIsless a b, annotatedIsless b a, annotatedIsequal a b].count true = 1

/-- An annotation-free wrapper around a non-UInt8 AbstractString is isequal to
the underlying string and must make the same hash call. -/
def AnnotatedStringHash : Prop :=
  ∀ chars h,
    hashNonByteAnnotated ⟨chars, []⟩ h = hashNonByteUnderlying chars h

/-- All three `hash_shaped` branches depend only on axes, canonical element
isequal classes and the seed. -/
def ArrayHashConsistency : Prop :=
  ∀ a b : CanonArray, a.axes = b.axes → a.values = b.values →
    ∀ h, hashArray a h = hashArray b h

/-- Reuse the complete short/Any32 Tuple and NamedTuple hash proof. -/
def TupleHashConsistency : Prop := JuliaLean.Tuples.HashIsequal

/-- AbstractDict and AbstractSet hashing is independent of iteration order. -/
def UnorderedHashConsistency : Prop :=
  (∀ a b : List (Nat × Nat), a.Perm b → ∀ h, dictHash a h = dictHash b h) ∧
  (∀ a b : List Nat, a.Perm b → ∀ h, setHash a h = setHash b h)

/-- A strict weak order, matching the `isless` contract. -/
def StrictWeak {α : Type} (lt : α → α → Bool) : Prop :=
  (∀ a, lt a a = false) ∧
  (∀ a b c, lt a b = true → lt b c = true → lt a c = true) ∧
  (∀ a b c, lt a b = false → lt b a = false → lt b c = false → lt c b = false →
    lt a c = false ∧ lt c a = false)

/-- `isless(::Real,::Real)` inherits a strict weak order from `<`, and generic
`cmp` returns exactly the sign selected by the two isless calls. -/
def ComparisonFallbacks : Prop :=
  ∀ (α : Type) (o : FallbackOps α), StrictWeak o.lt →
    StrictWeak (islessFallback o) ∧
    ∀ x y, cmpFallback o x y =
      (if islessFallback o x y then -1 else if islessFallback o y x then 1 else 0)

/-- Direct equations promised by the generic operator fallbacks. -/
def OperatorFallbacks : Prop :=
  ∀ (α : Type) (o : FallbackOps α) (x y : α),
    isequalFallback o x y = o.eq x y ∧
    neFallback o x y = !o.eq x y ∧
    leFallback o x y = (o.lt x y || o.eq x y) ∧
    geFallback o x y = (o.lt y x || o.eq y x)

/-- Direct equations promised by `zero`, `one`, `oneunit`, `iszero`, `isone`,
`signbit`, `abs`, `sign`, `muladd`, `fma`, `inv`, and literal powers. -/
def NumberFallbacks : Prop :=
  ∀ (α : Type) (o : FallbackOps α) (pow : α → Int → α) (x y z : α),
    zeroFallback o x = o.zero x ∧ oneFallback o x = o.one x ∧
    oneunitFallback o x = o.castOne (o.one x) ∧
    iszeroFallback o x = o.eq x (o.zero x) ∧ isoneFallback o x = o.eq x (o.one x) ∧
    signbitFallback o x = o.lt x (o.zero x) ∧
    absFallback o x = (if o.lt x (o.zero x) then o.neg x else x) ∧
    signFallback o x = (if o.lt x (o.zero x) then o.neg (o.one x)
      else if o.lt (o.zero x) x then o.one x else x) ∧
    muladdFallback o x y z = o.add (o.mul x y) z ∧
    fmaNumberFallback x y z = .noOperation ∧
    fmaIntegerFallback o x y z = .ok (o.add (o.mul x y) z) ∧
    invFallback o x = o.div (o.one x) x ∧
    literalPowHW o pow x 0 = o.one x ∧ literalPowHW o pow x 1 = x ∧
    literalPowHW o pow x 2 = o.mul x x ∧
    literalPowHW o pow x 3 = o.mul (o.mul x x) x ∧
    literalPowHW o pow x (-1) = o.div (o.one x) x

/-- The widen docstring's guarantee for both addition and subtraction. -/
def WidenNoLoss : Prop :=
  ∀ (t : IntTy) (x y : JInt t),
    widenAdd t x y = x.val + y.val ∧ widenSub t x y = x.val - y.val

end JuliaLean.HashOps
