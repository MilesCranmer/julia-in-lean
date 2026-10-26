import JuliaLean.Float.Extras
import JuliaLean.IntArith.NumberTheory

/-!
`TwicePrecision{Float64}` arithmetic and the integer helpers used by Float64
ranges, from `base/twiceprecision.jl` at Julia master `bbfa0ce4150`.

Every floating-point operation is the exact binary64 model `JuliaLean.Float.F64`
(default rounding, gradual underflow). Julia `Int` values are `JInt .i64` and wrap
where Julia wraps. `two_mul` uses the hardware-FMA branch of
`base/floatfuncs.jl:376-380` on CPUs with hardware FMA.
-/

namespace JuliaLean.FloatRanges

open JuliaLean.Float

/-- Julia `Int` on 64-bit platforms. -/
abbrev I64 := JInt .i64

/-- An `Int` literal. -/
def i64 (n : Int) : I64 := JInt.lit .i64 n

/-- A correctly rounded decimal literal `n / d`, as Julia's parser produces it. -/
def dec (n : Int) (d : Nat := 1) : F64 := F64.roundRat n d false

/-- `+0.0`, `zero(Float64)`. -/
def fzero : F64 := F64.zero false

/-- `Float64(i)` for a machine integer; `base/float.jl:243-305`. -/
def flt {t : IntTy} (i : JInt t) : F64 := F64.ofJInt i

/-- `abs(x::Int)`, wrapping at typemin; `base/int.jl:233`. -/
def iabs (x : I64) : I64 := if x.val < 0 then -x else x

/-- `max(x, y)` on Int. -/
def imax (x y : I64) : I64 := if y.val > x.val then y else x

/-- `min(x, y)` on Int. -/
def imin (x y : I64) : I64 := if y.val < x.val then y else x

/-- `clamp(x, lo, hi)` on Int; `base/intfuncs.jl:1461-1464`. -/
def iclamp (x lo hi : I64) : I64 :=
  if x.val > hi.val then hi else if x.val < lo.val then lo else x

/-- `clamp(x, lo, hi)` on Float64; `base/intfuncs.jl:1461-1464`. -/
def fclamp (x lo hi : F64) : F64 :=
  if F64.lt hi x then hi else if F64.lt x lo then lo else x

/-- `_isless`, `base/math.jl:833`. -/
private def fisless (x y : F64) : Bool :=
  F64.lt x y || (F64.signbit x && !F64.signbit y)

/-- `max(x, y)` on Float64 (`max_float`); semantics of `base/math.jl:835`. -/
def fmax (x y : F64) : F64 :=
  if F64.isnan x || (!F64.isnan y && fisless y x) then x else y

/-- `min(x, y)` on Float64 (`min_float`); semantics of `base/math.jl:834`. -/
def fmin (x y : F64) : F64 :=
  if F64.isnan x || (!F64.isnan y && fisless x y) then x else y

/-- `top_set_bit(x::Int)`, `base/int.jl:569`: `64 - leading_zeros(x)`. -/
def topSetBit (x : I64) : Int :=
  if x.val < 0 then 64 else if x.val = 0 then 0 else (x.val.toNat.log2 : Int) + 1

/-- `isbetween`, `base/twiceprecision.jl:790`. -/
def isbetween (a x b : F64) : Bool :=
  (F64.le a x && F64.le x b) || (F64.le b x && F64.le x a)

/-- `lcm_unchecked`, `base/twiceprecision.jl:775`: `a * div(b, gcd(a, b))`, wrapping. -/
def lcmUnchecked (a b : I64) : Jl I64 := do
  let g ← IntArith.NumberTheory.gcd a b
  let q ← JInt.div b g
  pure (a * q)

/-- `truncmask`, `base/twiceprecision.jl:28-30`. -/
def truncmask (x : F64) (mask : Nat) : F64 := F64.ofBits (Nat.land mask (F64.toBits x))

/-- `typemax(UInt64) << nb`, Julia's shift by a signed count; `base/int.jl:613-614`. -/
def shlMask (nb : Int) : Nat :=
  if nb ≥ 64 then 0
  else if nb ≥ 0 then ((2^64 - 1) <<< nb.toNat) % 2^64
  else if nb ≤ -64 then 0
  else (2^64 - 1) >>> nb.natAbs

/-- `truncbits`, `base/twiceprecision.jl:33-35`. -/
def truncbits (x : F64) (nb : Int) : F64 := truncmask x (shlMask nb)

/-- `canonicalize2`, `base/twiceprecision.jl:48-51`. -/
def canonicalize2 (big little : F64) : F64 × F64 :=
  let h := F64.add big little
  (h, F64.add (F64.sub big h) little)

/-- `add12`, `base/twiceprecision.jl:83-86`. -/
def add12 (x y : F64) : F64 × F64 :=
  let (x, y) := if F64.lt (F64.abs x) (F64.abs y) then (y, x) else (x, y)
  canonicalize2 x y

/-- `two_mul` with hardware FMA, `base/floatfuncs.jl:376-380`; `mul12`,
`base/twiceprecision.jl:114-117`. -/
def mul12 (x y : F64) : F64 × F64 :=
  let h := F64.mul x y
  let l := F64.fma x y (F64.neg h)
  if !F64.isfinite h then (h, h) else (h, l)

/-- `TwicePrecision{Float64}`, `base/twiceprecision.jl:196-199`. -/
structure TP where
  hi : F64
  lo : F64
  deriving DecidableEq, Repr, Inhabited

namespace TP

/-- `TwicePrecision{T}(x::T)`, `base/twiceprecision.jl:201`. -/
def ofF (x : F64) : TP := ⟨x, fzero⟩

/-- `Float64(x::TwicePrecision)`, `base/twiceprecision.jl:265`. -/
def toF (x : TP) : F64 := F64.add x.hi x.lo

/-- `-(x::TwicePrecision)`, `base/twiceprecision.jl:279`. -/
def neg (x : TP) : TP := ⟨F64.neg x.hi, F64.neg x.lo⟩

/-- `splitprec(Float64, i)`, `base/twiceprecision.jl:22-26`; `oftype(i, hi)` is an
exact conversion that throws `InexactError` when `hi` is out of range. -/
def splitprec {t : IntTy} (i : JInt t) : Jl (F64 × F64) := do
  let hi := truncbits (flt i) 27
  let ihi ← F64.int t hi
  pure (hi, flt (i - ihi))

/-- `TwicePrecision{T}(i::Integer)`, `base/twiceprecision.jl:211-212`. -/
def ofInt {t : IntTy} (i : JInt t) : Jl TP := do
  let (a, b) ← splitprec i
  let (h, l) := canonicalize2 a b
  pure ⟨h, l⟩

/-- `+(x::TwicePrecision, y::Number)`, `base/twiceprecision.jl:289-292`. -/
def addF (x : TP) (y : F64) : TP :=
  let (s_hi, s_lo) := add12 x.hi y
  let (h, l) := canonicalize2 s_hi (F64.add s_lo x.lo)
  ⟨h, l⟩

/-- `+(x::TwicePrecision{T}, y::TwicePrecision{T})`, `base/twiceprecision.jl:295-299`. -/
def add (x y : TP) : TP :=
  let r := F64.add x.hi y.hi
  let s := if F64.lt (F64.abs y.hi) (F64.abs x.hi)
    then F64.add (F64.add (F64.add (F64.sub x.hi r) y.hi) y.lo) x.lo
    else F64.add (F64.add (F64.add (F64.sub y.hi r) x.hi) x.lo) y.lo
  let (h, l) := canonicalize2 r s
  ⟨h, l⟩

/-- `*(x::TwicePrecision{T}, y::TwicePrecision{T})`, `base/twiceprecision.jl:318-322`. -/
def mul (x y : TP) : TP :=
  let (zh, zl) := mul12 x.hi y.hi
  let (h, l) := canonicalize2 zh
    (F64.add (F64.add (F64.mul x.hi y.lo) (F64.mul x.lo y.hi)) zl)
  if F64.iszero zh || !F64.isfinite zh then ⟨zh, zh⟩ else ⟨h, l⟩

/-- `*(x::TwicePrecision, v::Number)` for `v::Float64`, `base/twiceprecision.jl:306-309`. -/
def mulF (x : TP) (v : F64) : TP :=
  if F64.eq v fzero then ⟨F64.mul x.hi v, F64.mul x.lo v⟩
  else mul x (ofF v)

/-- `/(x::TwicePrecision, y::TwicePrecision)`, `base/twiceprecision.jl:329-335`. -/
def div (x y : TP) : TP :=
  let hi := F64.div x.hi y.hi
  let (uh, ul) := mul12 hi y.hi
  let lo := F64.div
    (F64.sub (F64.add (F64.sub (F64.sub x.hi uh) ul) x.lo) (F64.mul hi y.lo)) y.hi
  let (h, l) := canonicalize2 hi lo
  if F64.iszero hi || !F64.isfinite hi then ⟨hi, hi⟩ else ⟨h, l⟩

/-- `/(x::TwicePrecision, v::Number)`, `base/twiceprecision.jl:325-327`. -/
def divF (x : TP) (v : F64) : TP := div x (ofF v)

/-- `TwicePrecision{Float64}((num, den))`, `base/twiceprecision.jl:222-225`:
`TwicePrecision{T}(n) / d`, where the divisor is converted to Float64. -/
def ofRatio {t : IntTy} (n d : JInt t) : Jl TP := do
  let x ← ofInt n
  pure (divF x (flt d))

/-- `twiceprecision(val::TwicePrecision, nb)`, `base/twiceprecision.jl:246-249`. -/
def trunc (val : TP) (nb : Int) : TP :=
  let hi := truncbits val.hi nb
  ⟨hi, F64.add (F64.sub val.hi hi) val.lo⟩

end TP

/-- `nbitslen(len, offset)`, `base/twiceprecision.jl:256`. -/
def nbitslen0 (len offset : I64) : Int :=
  if len.val < 2 then 0
  else topSetBit (imax (offset - i64 1) (len - offset) - i64 1) + 1

/-- `nbitslen(Float64, len, offset)`, `base/twiceprecision.jl:252-253`. -/
def nbitslen (len offset : I64) : Int := min 27 (nbitslen0 len offset)

/-- `maxintfloat(Float32, Int)`, a Float32 promoted to Float64 by the comparison in
`rat`; `base/floatfuncs.jl:35,46`. -/
def ratBound : F64 := dec 16777216

/-- `convert(Int, maxintfloat(Float32, Int))`, `base/twiceprecision.jl:767`. -/
def ratBoundInt : I64 := i64 16777216

/-- `maxintfloat(Float64, Int)`, `base/floatfuncs.jl:34,46`. -/
def maxintF : F64 := dec 9007199254740992

/-- One iteration bound of the `while` loop of `rat`. Each iteration either exits
or, after the first, multiplies `|b|` by at least the golden ratio (`|f| ≥ 1` since
`|y| > 1` after `inv`), so `max(|a|,|b|) > 2^24` after at most 40 iterations; the
remaining fuel is never reached. -/
def ratLoop (x : F64) : Nat → F64 → I64 → I64 → I64 → I64 → Jl (I64 × I64)
  | 0, _, a, b, _, _ => .ok (a, b)
  | fuel + 1, y, a, b, c, d =>
    if !F64.le (F64.abs y) ratBound then .ok (a, b)
    else do
      let f ← F64.truncInt .i64 y
      let y := F64.sub y (flt f)
      let a' := f * a + c
      let c := a
      let b' := f * b + d
      let d := b
      if !(decide ((imax (iabs a') (iabs b')).val ≤ ratBoundInt.val)) then return (c, d)
      if F64.eq (F64.div (flt a') (flt b')) x then return (a', b')
      ratLoop x fuel (F64.div F64.one y) a' b' c d

/-- `rat(x)`, `base/twiceprecision.jl:757-772`: continued-fraction approximation. -/
def rat (x : F64) : Jl (I64 × I64) := ratLoop x 100 x (i64 1) (i64 0) (i64 0) (i64 1)

end JuliaLean.FloatRanges
