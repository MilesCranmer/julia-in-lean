import JuliaLean.base.gmp

/-!
`BigInt` at master `bbfa0ce4150` (`base/gmp.jl`).

A `BigInt` is a mathematical integer (`Int`). GMP calls are exact primitives defined by
their documented result (GNU MP 6.3 manual, chapter 5 "Integer Functions"); GMP's
`DIVIDE_BY_ZERO` and `SQRT_OF_NEGATIVE` exceptions raise `SIGFPE`, which Julia reports as
`DivideError`. Julia's wrapper code is mirrored line by line. The limb representation
(`x.size`, `unsafe_load(x.d, i)`) is modelled by `nlimbs` and `limb` with 64-bit limbs.
-/


namespace JuliaLean.BigNums

open JuliaLean JuliaLean.Promotion

/-! ## Properties and refutations -/

/-- The exception type of a `JlError` (messages ignored). -/
def errKind : JlError → Nat
  | .overflowError _ => 0 | .argumentError _ => 1 | .boundsError => 2 | .inexactError _ => 3
  | .divideError => 4 | .domainError _ => 5 | .methodError _ => 6 | .eofError => 7

/-- Two results agree: equal values, or the same exception type. -/
def sameJl {α β : Type} [BEq β] (f : α → β) : Jl α → Jl β → Bool
  | .ok a, .ok b => f a == b
  | .error e, .error g => errKind e == errKind g
  | _, _ => false

/-- A BigInt result and a machine result agree: equal values, or the same exception type. -/
def sameOutcome {t : IntTy} (a : Jl Int) (b : Jl (JInt t)) : Bool :=
  sameJl id a (b.map Subtype.val)

/-- `div`, `rem`, `fld`, `cld` and `mod` on BigInt agree with the same functions on every
`BitInteger` type wherever the machine call does not overflow (only quotients of
`typemin(T) ÷ -1` overflow), including `DivideError` for a zero divisor. -/
def DivisionMatchesInt : Prop :=
  ∀ (t : IntTy) (a b : JInt t),
    rem a.val b.val = (JInt.remInt a b).map Subtype.val ∧
    mod a.val b.val = (JInt.mod a b).map Subtype.val ∧
    (¬ (t.signed = true ∧ a.val = t.min ∧ b.val = -1) →
      div a.val b.val = (JInt.div a b).map Subtype.val ∧
      fld a.val b.val = (JInt.fld a b).map Subtype.val ∧
      cld a.val b.val = (JInt.cld a b).map Subtype.val)

/-- `isqrt(n)` is the largest `m` with `m*m ≤ n` for `n ≥ 0` and throws `DomainError` for
`n < 0`, as for every machine integer type. -/
def IsqrtSpec : Prop :=
  ∀ x : Int,
    (0 ≤ x → ∃ m, isqrt x = .ok m ∧ m * m ≤ x ∧ x < (m + 1) * (m + 1)) ∧
    (x < 0 → ∃ msg, isqrt x = .error (.domainError msg))

theorem isqrtSpec_refuted : ¬ IsqrtSpec := by
  intro h
  obtain ⟨msg, hm⟩ := (h (-4)).2 (by decide)
  simp [isqrt, mpzSqrt] at hm

/-- `powermod(x, p, m)` on BigInt agrees with `powermod` on `Int64` for all Int64 arguments:
same value, or the same exception type. -/
def PowermodMatchesInt : Prop :=
  ∀ x p m : JInt .i64,
    sameOutcome (powermod x.val p.val m.val)
      (IntArith.NumberTheory.powermod IntArith.NumberTheory.gmpGcdx
        IntArith.NumberTheory.gmpPowermod x p m) = true

theorem powermodMatchesInt_refuted : ¬ PowermodMatchesInt := by
  intro h
  have := h (JInt.lit .i64 2) (JInt.lit .i64 (-1)) (JInt.lit .i64 4)
  revert this
  decide +kernel

/-- For `p ≥ 0` and `m ≠ 0`, `powermod(x, p, m) == mod(x^p, m)` (floored, sign of `m`). -/
def PowermodFlooredMod : Prop :=
  ∀ x p m : Int, 0 ≤ p → m ≠ 0 → powermod x p m = .ok ((x ^ p.toNat).fmod m)

/-- `invmod(x, y)`'s documented postcondition (`base/gmp.jl:533`, `base/intfuncs.jl:290-294`):
when it returns `z`, `mod(z*x, y) == mod(1, y)` and `div(z, y) == 0`. -/
def InvmodPostcondition : Prop :=
  ∀ x y z : Int, invmod x y = .ok z → (z * x).fmod y = (1 : Int).fmod y ∧ z.tdiv y = 0

/-- `T(x::BigInt)` returns `x` when it is representable in `T` and throws `InexactError`
otherwise, for every `BitInteger` type `T`. -/
def ToIntExact : Prop :=
  ∀ (t : IntTy) (x : Int),
    sameJl Subtype.val (toIntTy t x) ((JInt.convert (t.name) t x).map Subtype.val) = true

/-- `isequal(big(x), x)` holds for `Int64` and `UInt64` `x`, so `hash(big(x)) == hash(x)`. -/
def HashBigMatchesSmall : Prop :=
  ∀ (h : HTerm),
    (∀ x : JInt .i64, hashBig x.val h = hashNum (.int .i64 x) h) ∧
    (∀ x : JInt .u64, hashBig x.val h = hashNum (.int .u64 x) h)

/-- `hash(big(x)) == hash(x)` for every `Int128` and `UInt128` `x`. -/
def HashBigMatches128 : Prop :=
  ∀ (h : HTerm),
    (∀ x : JInt .i128, hashBig x.val h = hashNum (.int .i128 x) h) ∧
    (∀ x : JInt .u128, hashBig x.val h = hashNum (.int .u128 x) h)

/-- For negative exponents, `big(x)^p` agrees with `x^p` on `Int64` (`power_by_squaring`):
`1`, `±1` for `x == -1`, and `DomainError` otherwise. -/
def PowNegativeMatchesInt : Prop :=
  ∀ x p : JInt .i64, p.val < 0 →
    sameOutcome (bigintPow x.val p.val) (IntArith.PowersDigits.powerBySquaring x p) = true

/-- `digits(T, n; base)` on BigInt agrees with `digits(T, n; base)` on `Int64` for every element
type `T` and base `2..62`: the same digits, or the same exception type. -/
def DigitsMatchesInt : Prop :=
  ∀ (t : IntTy) (n : JInt .i64) (b : Nat), 2 ≤ b → b ≤ 62 →
    sameJl (List.map Subtype.val) (digitsBig t n.val b) ((digitsMachine t n.val b).map
      (List.map Subtype.val)) = true

theorem digitsMatchesInt_refuted : ¬ DigitsMatchesInt := by
  intro h
  have := h .u8 (JInt.lit .i64 (-7)) 10 (by decide) (by decide)
  revert this
  decide +kernel

/-- `digits!(a, n; base)` fills `a` with the `length(a)` least significant digits of `n` when `a`
is too short (`base/intfuncs.jl:1223-1228`), for every output vector and power-of-two base
`2^k > 62`. -/
def DigitsBangFillsLow : Prop :=
  ∀ (a : Vec) (n : Int) (k : Nat), 6 ≤ k → k ≤ 62 → 0 ≤ n →
    digitsBangBig a n k = .ok (lowDigits a.len n k)

theorem digitsBangFillsLow_refuted : ¬ DigitsBangFillsLow := by
  intro h
  have := h ⟨3, false⟩ (2 ^ 62 + 5) 7 (by decide) (by decide) (by decide)
  revert this
  decide +kernel

end JuliaLean.BigNums
