import JuliaLean.Promotion.IEEE
import JuliaLean.BigNums.Int

/-!
`BigFloat` at master `bbfa0ce4150` (`base/mpfr.jl`).

MPFR calls are exact primitives: each returns the exact result correctly rounded to the
destination precision in the requested rounding mode (MPFR 4.2 manual §4.4 "Rounding" and
§5 "MPFR Interface"). Julia sets the exponent range to its maximum (`base/mpfr.jl:47-56`),
so exponents are unbounded here. A finite nonzero value is `m * 2^e` with `m` odd.
-/

namespace JuliaLean.BigNums

open JuliaLean JuliaLean.Promotion

/-- Julia's rounding modes, `base/rounding.jl:37-109`. -/
inductive RMode where
  | nearest | toZero | up | down | fromZero | nearestTiesAway | nearestTiesUp
  deriving DecidableEq, Repr

/-- `MPFRRoundingMode`, `base/mpfr.jl:66-73` (`MPFRRoundFaithful` is never produced). -/
inductive MPFRMode where
  | rndN | rndZ | rndU | rndD | rndA
  deriving DecidableEq, Repr

/-- `convert(MPFRRoundingMode, r)`, `base/mpfr.jl:75-79`: only five modes have a method. -/
def toMPFR : RMode → Jl MPFRMode
  | .nearest => .ok .rndN
  | .toZero => .ok .rndZ
  | .up => .ok .rndU
  | .down => .ok .rndD
  | .fromZero => .ok .rndA
  | _ => .error (.methodError "convert")

/-- `_opposite_round`, `base/mpfr.jl:401-405`. -/
def opposite : MPFRMode → MPFRMode
  | .rndU => .rndD
  | .rndD => .rndU
  | m => m

/-- A BigFloat value (its precision is carried separately). -/
inductive BF where
  | nan
  | inf (neg : Bool)
  | zero (neg : Bool)
  | fin (m : Int) (e : Int)
  deriving DecidableEq, Repr

/-- The canonical finite value `m * 2^e`: factors of two move from `m` into `e`. -/
def mkFin (m : Int) (e : Int) : BF :=
  if m = 0 then .zero false else go m e (m.natAbs.log2 + 1)
where
  go (m : Int) (e : Int) : Nat → BF
    | 0 => .fin m e
    | k + 1 => if m % 2 = 0 then go (m / 2) (e + 1) k else .fin m e

/-- The exact value `n / d` of a finite value (`d > 0`, a power of two). -/
def BF.toRat : BF → Int × Nat
  | .fin m e => if 0 ≤ e then (m * 2 ^ e.toNat, 1) else (m, 2 ^ (-e).toNat)
  | _ => (0, 1)

def BF.signbit : BF → Bool
  | .nan => false
  | .inf s => s
  | .zero s => s
  | .fin m _ => decide (m < 0)

def BF.isnan : BF → Bool
  | .nan => true
  | _ => false

/-- `n / d` (`n ≠ 0`, `d > 0`) correctly rounded to `p` significant bits in mode `r`, ties to
even for `rndN` (MPFR manual §4.4). -/
def roundP (p : Nat) (r : MPFRMode) (n : Int) (d : Nat) : BF :=
  if n = 0 then .zero false
  else
    let neg := decide (n < 0)
    let a := n.natAbs
    let e := Fl.floorLog2Rat a d
    let k : Int := e + 1 - p
    let num := if 0 ≤ k then a else a * 2 ^ (-k).toNat
    let den := if 0 ≤ k then d * 2 ^ k.toNat else d
    let q := num / den
    let rm := num % den
    let up := match r with
      | .rndN => decide (2 * rm > den) || (decide (2 * rm = den) && q % 2 == 1)
      | .rndZ => false
      | .rndA => rm != 0
      | .rndU => rm != 0 && !neg
      | .rndD => rm != 0 && neg
    let q := if up then q + 1 else q
    mkFin (if neg then -(q : Int) else q) k

/-- `mpfr_div` at precision `p` in mode `r` (MPFR manual §5.5), for the operand kinds that
arise from `BigFloat(::Rational)`. -/
def divBF (p : Nat) (r : MPFRMode) : BF → BF → BF
  | .fin m1 e1, .fin m2 e2 =>
    let (n1, d1) := (BF.fin m1 e1).toRat
    let (n2, d2) := (BF.fin m2 e2).toRat
    roundP p r (n1 * d2 * n2.sign) (d1 * n2.natAbs)
  | .zero s, .fin m _ => .zero (s != decide (m < 0))
  | .fin m _, .zero s => .inf (decide (m < 0) != s)
  | .zero _, .zero _ => .nan
  | _, _ => .nan

/-- `BigFloat(x::Integer, r; precision = p)` (`mpfr_set_z`/`mpfr_set_si`, `base/mpfr.jl:320-386`). -/
def ofInt (p : Nat) (r : MPFRMode) (n : Int) : BF := roundP p r n 1

/-- `BigFloat(x::Rational, r; precision = p)`, `base/mpfr.jl:393-400`: the numerator is
converted in mode `r`, the denominator in `_opposite_round(r)`, both at precision `p`, and
their quotient is rounded in mode `r`. -/
def ofRational (p : Nat) (r : MPFRMode) (num : Int) (den : Nat) : BF :=
  divBF p r (ofInt p r num) (ofInt p (opposite r) den)

/-- `BigFloat(q, r; precision = p)` is `q` correctly rounded to `p` bits in direction `r` (the
`BigFloat` docstring, `base/mpfr.jl:258-263`), for every nonzero normalized finite rational. -/
def BigFloatOfRationalRounded : Prop :=
  ∀ (p : Nat) (r : MPFRMode) (num : Int) (den : Nat),
    1 ≤ p → 0 < den → num ≠ 0 → Nat.gcd num.natAbs den = 1 →
    ofRational p r num den = roundP p r num den

theorem bigFloatOfRationalRounded_refuted : ¬ BigFloatOfRationalRounded := by
  intro h
  have := h 2 .rndN 1 5 (by decide) (by decide) (by decide) (by decide)
  revert this
  decide +kernel

/-! ## Comparison with Float64 (`base/mpfr.jl:1009-1024`, `base/operators.jl:199,240`) -/

/-- `BigFloat(y::Float64)` (exact for every precision ≥ 53). -/
def ofF64 (y : Fl double) : BF :=
  if y.isnan then .nan
  else if y.isinf then .inf y.signbit
  else if y.iszero then .zero y.signbit
  else
    let (n, d) := y.toRat
    mkFin n (-(d.log2 : Int))

/-- Numeric three-way comparison of two non-NaN values; zeros of either sign are equal. -/
def numCmp (a b : BF) : Int :=
  let key : BF → Int × Int × Nat := fun
    | .inf s => if s then (-1, 0, 1) else (1, 0, 1)
    | v => (0, v.toRat.1, v.toRat.2)
  let (ka, na, da) := key a
  let (kb, nb, db) := key b
  if ka ≠ kb then (if ka < kb then -1 else 1)
  else if ka ≠ 0 then 0
  else
    let l := na * db
    let r := nb * da
    if l < r then -1 else if l = r then 0 else 1

/-- `cmp(x::BigFloat, y::CdoubleMax)`, `base/mpfr.jl:1009-1013`. `mpfr_cmp_d` compares
numerically and returns ±1 or 0 (MPFR manual §5.6). -/
def cmpF64 (x : BF) (y : Fl double) : Int :=
  if x.isnan then (if y.isnan then 0 else 1)
  else if y.isnan then -1
  else numCmp x (ofF64 y)

/-- `isless(x::AbstractFloat, y::AbstractFloat)`, `base/operators.jl:240`, with `x < y` the
numeric `<(::BigFloat, ::CdoubleMax)` (`base/mpfr.jl:1023`) and `signless`,
`base/operators.jl:199`. -/
def islessBF (x y : BF) : Bool :=
  (!x.isnan && (y.isnan || (x.signbit && !y.signbit))) ||
    (!x.isnan && !y.isnan && numCmp x y < 0)

/-- `cmp(x::BigFloat, y::Float64)` follows the total order implemented by `isless` (the `cmp`
docstring, `base/operators.jl:508-511`). -/
def CmpBigFloatIsless : Prop :=
  ∀ (x : BF) (y : Fl double),
    cmpF64 x y = (if islessBF x (ofF64 y) then -1 else if islessBF (ofF64 y) x then 1 else 0)

theorem cmpBigFloatIsless_refuted : ¬ CmpBigFloatIsless := by
  intro h
  have := h (.zero true) (Fl.zero false)
  revert this
  decide +kernel

/-! ## Rounding to integers (`base/mpfr.jl:428-468`) -/

/-- `n / d` (`d > 0`) rounded to an integer in mode `r`, as documented for each
`RoundingMode` (`base/rounding.jl:37-109`). -/
def roundIntSpec (r : RMode) (n : Int) (d : Nat) : Int :=
  let fl := n.fdiv d
  let rm := n - fl * d
  let tie := 2 * rm = (d : Int)
  let above := 2 * rm > (d : Int)
  match r with
  | .down => fl
  | .up => if rm = 0 then fl else fl + 1
  | .toZero => if rm = 0 ∨ 0 ≤ n then fl else fl + 1
  | .fromZero => if rm = 0 ∨ n < 0 then fl else fl + 1
  | .nearest => if above ∨ (tie ∧ fl % 2 ≠ 0) then fl + 1 else fl
  | .nearestTiesAway => if above ∨ (tie ∧ 0 ≤ n) then fl + 1 else fl
  | .nearestTiesUp => if above ∨ tie then fl + 1 else fl

/-- The `RoundingMode` an MPFR mode stands for. -/
def MPFRMode.toR : MPFRMode → RMode
  | .rndN => .nearest
  | .rndZ => .toZero
  | .rndU => .up
  | .rndD => .down
  | .rndA => .fromZero

/-- `round(T, x::BigFloat, r)` for `T = Int64`, `base/mpfr.jl:449-456,465-466`:
`_unchecked_cast` converts `r` to an MPFR mode, rounds with `mpfr_get_z` (MPFR manual §5.4),
and the range check throws `InexactError`. -/
def roundToInt (t : IntTy) (x : BF) (r : RMode) : Jl (JInt t) := do
  let mr ← toMPFR r
  match x with
  | .nan | .inf _ => .error (.inexactError "round")
  | .zero _ => JInt.convert t 0
  | .fin m e =>
    let (n, d) := (BF.fin m e).toRat
    match JInt.convert t (roundIntSpec mr.toR n d) with
    | .ok v => .ok v
    | .error _ => .error (.inexactError "round")

/-- `round(Int64, x, r)` for a finite BigFloat `x` rounds the value in direction `r` for every
`RoundingMode`, throwing `InexactError` only when the result does not fit (the `round`
docstring, `base/rounding.jl:331-350`). -/
def RoundBigFloatAllModes : Prop :=
  ∀ (m e : Int) (r : RMode), m ≠ 0 →
    roundToInt .i64 (.fin m e) r =
      match JInt.convert .i64 (roundIntSpec r (BF.fin m e).toRat.1 (BF.fin m e).toRat.2) with
      | .ok v => .ok v
      | .error _ => .error (.inexactError "round")

theorem roundBigFloatAllModes_refuted : ¬ RoundBigFloatAllModes := by
  intro h
  have := h 5 (-1) .nearestTiesAway (by decide)
  revert this
  decide +kernel

end JuliaLean.BigNums
