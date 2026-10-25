import JuliaLean.Core
import JuliaLean.IntArith.NumberTheory
import JuliaLean.IntArith.PowersDigits
import JuliaLean.Promotion.Hash

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

/-! ## Limbs -/

/-- Number of 64-bit limbs of `abs(x)`, i.e. `abs(x.size)` (`base/gmp.jl:68-72`). -/
def nlimbs (x : Int) : Nat := if x = 0 then 0 else x.natAbs.log2 / 64 + 1

/-- `unsafe_load(x.d, l + 1)`: limb `l` (least significant first) of `abs(x)`. -/
def limb (x : Int) (l : Nat) : Nat := x.natAbs / 2 ^ (64 * l) % 2 ^ 64

/-- `x.size`: signed limb count. -/
def size (x : Int) : Int := if x < 0 then -(nlimbs x : Int) else nlimbs x

/-! ## Division (`base/gmp.jl:495-514,625-626`) -/

/-- `mpz_tdiv_q` (GMP manual 5.6 "Division Functions": `tdiv` truncates `q` toward zero);
division by zero raises `DivideError`. -/
def tdivQ (n d : Int) : Jl Int := if d = 0 then .error .divideError else .ok (n.tdiv d)
/-- `mpz_tdiv_r`: `r = n - q*d` with `q` truncated, so `r` has the sign of `n`. -/
def tdivR (n d : Int) : Jl Int := if d = 0 then .error .divideError else .ok (n.tmod d)
/-- `mpz_fdiv_q`: `q` rounded toward minus infinity. -/
def fdivQ (n d : Int) : Jl Int := if d = 0 then .error .divideError else .ok (n.fdiv d)
/-- `mpz_fdiv_r`: `r = n - q*d` with `q` floored, so `r` has the sign of `d`. -/
def fdivR (n d : Int) : Jl Int := if d = 0 then .error .divideError else .ok (n.fmod d)
/-- `mpz_cdiv_q`: `q` rounded toward plus infinity. -/
def cdivQ (n d : Int) : Jl Int := if d = 0 then .error .divideError else .ok (-((-n).fdiv d))

/-- `div(x::BigInt, y::BigInt) = div(x, y, RoundToZero)`, `base/gmp.jl:505-512`. -/
def div (x y : Int) : Jl Int := tdivQ x y
/-- `rem(x::BigInt, y::BigInt) = MPZ.tdiv_r(x, y)`, `base/gmp.jl:495-503`. -/
def rem (x y : Int) : Jl Int := tdivR x y
/-- `mod(x::BigInt, y::BigInt) = MPZ.fdiv_r(x, y)`, `base/gmp.jl:495-503`. -/
def mod (x y : Int) : Jl Int := fdivR x y
/-- `fld(x::BigInt, y::BigInt) = div(x, y, RoundDown)`, `base/gmp.jl:513`. -/
def fld (x y : Int) : Jl Int := fdivQ x y
/-- `cld(x::BigInt, y::BigInt) = div(x, y, RoundUp)`, `base/gmp.jl:514`. -/
def cld (x y : Int) : Jl Int := cdivQ x y
/-- `divrem(x::BigInt, y::BigInt) = MPZ.tdiv_qr(x, y)`, `base/gmp.jl:625`. -/
def divrem (x y : Int) : Jl (Int × Int) := do pure (← tdivQ x y, ← tdivR x y)

/-! ## isqrt (`base/gmp.jl:637`) -/

/-- Floor square root of a natural number. -/
def natSqrt (n : Nat) : Nat :=
  (List.range (n + 1)).foldl (fun acc k => if k * k ≤ n then k else acc) 0

/-- `mpz_sqrt` (GMP manual 5.8: "Set rop to the truncated integer part of the square root of
op"). A negative operand raises GMP's `SQRT_OF_NEGATIVE` exception (`SIGFPE`), reported as
`DivideError`. -/
def mpzSqrt (x : Int) : Jl Int := if x < 0 then .error .divideError else .ok (natSqrt x.toNat)

/-- `isqrt(x::BigInt) = MPZ.sqrt(x)`, `base/gmp.jl:637`. -/
def isqrt (x : Int) : Jl Int := mpzSqrt x

/-! ## Powers (`base/gmp.jl:639-674`) -/

/-- `bigint_pow(x::BigInt, y::Integer)`, `base/gmp.jl:641-661`, for exponents that fit
`Culong` (`x^convert(Culong, y)` is `mpz_pow_ui`, the exact power). -/
def bigintPow (x y : Int) : Jl Int :=
  if x = 1 then .ok x
  else if x = -1 then .ok (if y % 2 ≠ 0 then x else -x)
  else if y < 0 then .error (.domainError "`y` cannot be negative.")
  else if y > 2 ^ 64 - 1 then
    if x = 0 then .ok x else .error (.overflowError "exponent is too large")
  else .ok (x ^ y.toNat)

/-- `powermod(x::BigInt, p::BigInt, m::BigInt)`, `base/gmp.jl:669-672`, reusing the GMP
`mpz_powm` primitive of the IntArith area. -/
def powermod (x p m : Int) : Jl Int := IntArith.NumberTheory.gmpPowermod x p m

/-! ## invmod (`base/gmp.jl:518-535`) -/

/-- `mpz_invert` (GMP manual 5.9 "Number Theoretic Functions"): if an inverse of `a` modulo
`b` exists, return it in `[0, abs(b))`; otherwise report failure. The documented result is
the unique such residue (`b ≠ 0`; Julia never calls it with `b = 0`). -/
def mpzInvert (a b : Int) : Option Int :=
  ((List.range b.natAbs).find? (fun (z : Nat) => ((z : Int) * a - 1) % (b.natAbs : Int) = 0)).map
    (fun (z : Nat) => (z : Int))

/-- `invmod(x::BigInt, y::BigInt)`, `base/gmp.jl:518-535`. -/
def invmod (x y : Int) : Jl Int :=
  let ya := (y.natAbs : Int)
  if ya = 1 then .ok 0
  else if y = 0 then .error (.domainError "")
  else match mpzInvert x ya with
    | none => .error (.domainError "")
    | some z => .ok (if y < 0 then z + y else z)

/-! ## Conversion to machine integers (`base/gmp.jl:367-407`) -/

/-- `flipsign(u, x.size)` for a `BitInteger` `u`: negation (wrapping) when `x < 0`. -/
def flipsignTy {t : IntTy} (u : JInt t) (x : Int) : JInt t := if x < 0 then -u else u

/-- `rem(x::BigInt, ::Type{T})`, `base/gmp.jl:369-378`: the least significant limb for types of
at most 64 bits, else the two low limbs shifted into place, then `flipsign`. -/
def remTy (t : IntTy) (x : Int) : JInt t :=
  if t.bits ≤ 64 then
    if x = 0 then JInt.lit t 0 else flipsignTy (JInt.wrap t (limb x 0)) x
  else
    let n := min (nlimbs x) ((t.bits / 8 + 7) / 8)
    let u := (List.range n).foldl
      (fun u l => u + JInt.wrap t (limb x l) * JInt.wrap t (2 ^ (64 * l))) (JInt.lit t 0)
    flipsignTy u x

/-- `(::Type{T})(x::BigInt)` for unsigned `T` of at least 64 bits, `base/gmp.jl:390-393`. -/
def toUnsignedWide (t : IntTy) (x : Int) : Jl (JInt t) :=
  if 0 ≤ size x ∧ size x ≤ ((t.bits / 8 + 7) / 8 : Nat) then .ok (remTy t x)
  else .error (.inexactError t.name)

/-- `(::Type{T})(x::BigInt)` for signed `T` of at least 64 bits, `base/gmp.jl:396-407`. -/
def toSignedWide (t : IntTy) (x : Int) : Jl (JInt t) :=
  let n := nlimbs x
  if n ≤ (t.bits / 8 + 7) / 8 then
    let y := remTy t x
    if decide (0 < x) != decide (0 < y.val) then .error (.inexactError t.name) else .ok y
  else .error (.inexactError t.name)

/-- `T(x::BigInt)` for every `BitInteger` `T`, `base/gmp.jl:387-407`. Types narrower than a
limb go through `convert(Limb, x)` or `convert(Int64, x)` and then `convert(T, ·)`. -/
def toIntTy (t : IntTy) (x : Int) : Jl (JInt t) :=
  if t.signed then
    if t.bits < 64 then do
      let y ← toSignedWide .i64 x
      JInt.convert t y.val
    else toSignedWide t x
  else
    if t.bits < 64 then do
      let y ← toUnsignedWide .u64 x
      JInt.convert t y.val
    else toUnsignedWide t x

/-! ## Hashing (`base/gmp.jl:917-955`) -/

/-- `trailing_zeros(x::BigInt)` for nonzero `x` (`mpz_scan1(x, 0)`). -/
def trailingZerosBig (x : Int) : Nat := go x.natAbs (x.natAbs.log2 + 1)
where
  go (m : Nat) : Nat → Nat
    | 0 => 0
    | k + 1 => if m % 2 == 1 || m == 0 then 0 else 1 + go (m / 2) k

/-- `hash(x::BigInt, h)` on 64-bit systems, `base/gmp.jl:917-955`, in the hash-term model of
`JuliaLean.Promotion.Hash`. The byte-hashing tail `h ⊻= (sz < 0); hash_bytes(limb_view, h)` is
`hash_integer` (`base/hashing.jl:147-160`) of the signed integer whose magnitude is
`abs(x) >> (8 * trailing_zero_bytes)`; it is the term `.int v h`. -/
def hashBig (x : Int) (h : HTerm) : HTerm :=
  let sz := size x
  if sz = 0 then hashI64 0 h
  else if sz = 1 then .u64 (limb x 0) h
  else if sz = -1 ∧ limb x 0 ≤ 2 ^ 63 then hashI64 (-(limb x 0 : Int)) h
  else
    let pow := trailingZerosBig x
    let nd := x.natAbs.log2 + 1
    let idx := pow / 64
    let shift := pow % 64
    let lw := if shift = 0 then limb x idx
      else (limb x (idx + 1) * 2 ^ (64 - shift) % 2 ^ 64 + limb x idx / 2 ^ shift) % 2 ^ 64
    if nd ≤ 1024 ∧ nd - pow ≤ 53 then
      let v : Int := if x < 0 then -(lw : Int) else lw
      hashF64 (Fl.roundRat (v * 2 ^ pow) 1 false) h
    else
      let h := HTerm.int pow h
      let v : Int := (if x < 0 then -1 else 1) * (x.natAbs / 2 ^ (8 * (pow / 8)) : Nat)
      HTerm.int v h

/-! ## digits (`base/gmp.jl:784-810`, `base/intfuncs.jl:1249-1281`) -/

/-- The base-`b` digits of `n`, least significant first, at least one (`ndigits(n; base)`). -/
def absDigits (n b : Nat) : List Nat := go n (n + 1)
where
  go (n : Nat) : Nat → List Nat
    | 0 => []
    | k + 1 => if n < b then [n] else n % b :: go (n / b) k

/-- `digits(T, n; base)` for a machine `n`: `digits!(zeros(T, ndigits(n; base)), n; base)` with
the generic loop `n, d = divrem(n, base); a[i] = d` (`base/intfuncs.jl:1249-1268`). Storing a
digit converts it to `T`, throwing `InexactError` when it does not fit. For a power-of-two base
and `n ≥ 0` Julia shifts instead (`base/intfuncs.jl:1256-1262`), which yields the same digits. -/
def digitsMachine (t : IntTy) (n : Int) (b : Nat) : Jl (List (JInt t)) :=
  let len := (absDigits n.natAbs b).length
  ((List.range len).foldl (fun (acc : Int × List Int) _ =>
      (acc.1.tdiv b, acc.2 ++ [acc.1.tmod b])) (n, [])).2.mapM (JInt.convert t)

/-- `digits(T, n::BigInt; base)` for `2 ≤ base ≤ 62`, `base/gmp.jl:784-799`: the digit values of
`string(n; base)` (magnitudes) are stored, then `map!(-, a, a)` negates them for negative `n`,
wrapping in `T`. -/
def digitsBig (t : IntTy) (n : Int) (b : Nat) : Jl (List (JInt t)) :=
  .ok ((absDigits n.natAbs b).map fun (d : Nat) =>
    let v := JInt.lit t (d : Int)
    if n < 0 then -v else v)

/-- An output vector for `digits!`: its length, and whether it is resizable (a `Vector`) or
not (a view or other fixed-size `StridedVector`, which has no `resize!` method). -/
structure Vec where
  len : Nat
  resizable : Bool
  deriving DecidableEq, Repr

/-- The `len` least significant base-`2^k` digits of `n ≥ 0`, as the docstring promises. -/
def lowDigits (len : Nat) (n : Int) (k : Nat) : List Int :=
  (List.range len).map fun i => (n.toNat / 2 ^ (k * i) % 2 ^ k : Nat)

/-- `digits!(a::Vector{Int64}, n::BigInt; base = 2^k)` for `base > 62`, `base/gmp.jl:800-806`
with `MPZ.export!` (`base/gmp.jl:274-284`): when `a` is shorter than the digit count, export!
calls `resize!(a, ndigits)`, a `MethodError` for non-resizable vectors; the exported words are
then truncated back to the original length. Restricted to `n ≥ 0`. -/
def digitsBangBig (a : Vec) (n : Int) (k : Nat) : Jl (List Int) :=
  let nd := ((n.natAbs.log2 + 1) + k - 1) / k
  if a.len < nd ∧ !a.resizable then .error (.methodError "resize!")
  else .ok (lowDigits a.len n k)

/-! ## Properties and refutations -/

/-- The exception type of a `JlError` (messages ignored). -/
def errKind : JlError → Nat
  | .overflowError _ => 0 | .argumentError _ => 1 | .boundsError => 2 | .inexactError _ => 3
  | .divideError => 4 | .domainError _ => 5 | .methodError _ => 6

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
    sameOutcome (powermod x.val p.val m.val) (IntArith.NumberTheory.powermod x p m) = true

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
    sameJl Subtype.val (toIntTy t x) ((JInt.convert t x).map Subtype.val) = true

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
