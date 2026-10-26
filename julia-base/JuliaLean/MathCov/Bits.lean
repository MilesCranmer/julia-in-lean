import JuliaLean.MathCov.Fmt

/-!
Bit-level methods of `base/math.jl` and `base/floatfuncs.jl` at Julia master
`bbfa0ce4150`, generic over the three IEEE formats (`T : FTy`): `ldexp`, `exponent`,
`_exponent_finite_nonzero`, `scaleinv`, the integer `exponent` methods, `highword` and
friends, `copysign`/`flipsign`/`signbit`, `maxintfloat`, `min`/`max`, IEEE `rem` with
`RoundNearest`, `modf`, and `add22condh`.
-/

namespace JuliaLean.MathCov.Bits

open JuliaLean JuliaLean.Float JuliaLean.Promotion JuliaLean.MathCov.FP
open JuliaLean.FloatIntCov.Float (signMask exponentMask exponentOne significandBits
  exponentBits exponentBias exponentRawMax leadingZeros uintTy)

variable {T : FTy}

/-- Bit width of `T`. -/
def width (T : FTy) : Nat := T.fmt.width

/-- `x +% y` on `Int64`. -/
def addWrap64 (a b : Int) : Int := wrapInt .i64 (a + b)

/-- `ldexp(x::T, e::Integer) where T<:IEEEFloat`; `base/math.jl:854-897`. The integer
`e` is the exact value of any `Integer` type. -/
def ldexp (x : FV T) (e : Int) : FV T := Id.run do
  let xu0 := x.toBits
  let xs := xu0 % signMask T
  if xs ≥ exponentMask T then return x
  let mut xu := xu0
  let mut k : Int := (xs / 2 ^ significandBits T : Nat)
  if k == 0 then
    if xs == 0 then return x
    let m := leadingZeros (width T) xs - exponentBits T
    let ys := xs * 2 ^ m
    xu := ys + (if x.signbit then signMask T else 0)
    k := 1 - (m : Int)
    if e < -50000 then return flipsign (zero T) x
  if e > IntTy.max .i64 then return flipsign (inf T) x
  else if e < IntTy.min .i64 then return flipsign (zero T) x
  let n := wrapInt .i64 e
  k := addWrap64 k n
  if k ≥ exponentRawMax T then return flipsign (inf T) x
  if k > 0 then
    xu := (xu % 2 ^ significandBits T) + (if xu ≥ signMask T then signMask T else 0)
      + k.toNat * 2 ^ significandBits T
    return Fl.ofBits xu
  else
    if k ≤ -((significandBits T : Int)) - 1 then
      if e > 50000 then return flipsign (inf T) x
      return flipsign (zero T) x
    k := k + significandBits T + 1
    let z : FV T := Fl.ofBits ((exponentBias T - significandBits T - 1) * 2 ^ significandBits T)
    xu := (xu % 2 ^ significandBits T) + (if xu ≥ signMask T then signMask T else 0)
      + k.toNat * 2 ^ significandBits T
    return mul z (Fl.ofBits xu)

/-- `ldexp(x::Float16, q::Integer) = Float16(ldexp(Float32(x), q))`; `base/math.jl:898`. -/
def ldexp16 (x : FV .f16) (q : Int) : FV .f16 := conv (ldexp (conv x : FV .f32) q)

/-- `throw1(x)` and `throw2(x)` inside `exponent`; `base/math.jl:937-938`. -/
def exponentThrow1 : Jl Int := .error (.domainError "Cannot be NaN or Inf.")
def exponentThrow2 : Jl Int := .error (.domainError "Cannot be ±0.0.")

/-- `exponent(x::T) where T<:IEEEFloat`; `base/math.jl:936-950`. -/
def exponent (x : FV T) : Jl Int :=
  let xs := x.toBits % signMask T
  if xs ≥ exponentMask T then exponentThrow1
  else
    let k : Int := (xs / 2 ^ significandBits T : Nat)
    if k == 0 then
      if xs == 0 then exponentThrow2
      else
        let m : Int := (leadingZeros (width T) xs : Int) - exponentBits T
        .ok ((1 - m) - exponentBias T)
    else .ok (k - exponentBias T)

/-- `_exponent_finite_nonzero(x::T)`; `base/math.jl:956-965`. -/
def exponentFiniteNonzero (x : FV T) : Int :=
  let xs := x.toBits % signMask T
  let k : Int := (xs / 2 ^ significandBits T : Nat)
  if k == 0 then
    let m : Int := (leadingZeros (width T) xs : Int) - exponentBits T
    (1 - m) - exponentBias T
  else k - exponentBias T

/-- `_ilog2_step(y, d, s)` on nonnegative integers (`BigInt`); `base/math.jl:967-978`.
`fuel` bounds the recursion, which deepens only while `y >= d^2`. -/
def ilog2Step : Nat → Nat → Nat → Nat → Nat × Nat
  | 0, y, _, _ => (y, 0)
  | fuel + 1, y, d, s =>
    let (y1, n1) := if y / 2 ^ s ≥ d then ilog2Step fuel y (d * d) (s + s) else (y, 0)
    if y1 ≥ d then (y1 / 2 ^ s, n1 + s) else (y1, n1)

/-- `exponent(x::Integer)` for unbounded integers; `base/math.jl:980-985`. -/
def exponentInteger (x : Int) : Jl Int :=
  if x == 0 then .error (.domainError "cannot be zero")
  else .ok (ilog2Step (x.natAbs + 1) x.natAbs 2 1).2

/-- `exponent(x::Base.BitInteger)`; `base/math.jl:987-991`. `uabs` of `typemin` is its
magnitude, which fits the unsigned type. -/
def exponentBitInteger {t : IntTy} (x : JInt t) : Jl Int :=
  if x.val == 0 then .error (.domainError "cannot be zero")
  else
    let ux := x.val.natAbs
    .ok ((t.bits : Int) - leadingZeros t.bits ux - 1)

/-- `exponent(x::Bool)`; `base/math.jl:993-999`. -/
def exponentBool (x : Bool) : Jl Int :=
  if x then .ok 0 else .error (.domainError "cannot be zero")

/-- `scaleinv(x::T)`; `base/math.jl:1100-1111`. Returns `(scale, invscale)`. -/
def scaleinv (x : FV T) : FV T × FV T :=
  let umin := (floatminT T : FV T).toBits
  let umax := (div (one T) (floatminT T) : FV T).toBits
  let e := (x.toBits / 2 ^ significandBits T % 2 ^ exponentBits T) * 2 ^ significandBits T
  let u := Nat.min (Nat.max e umin) umax
  (Fl.ofBits u, Fl.ofBits (umin + umax - u))

/-- `highword(x::UInt64) = (x >>> 32) % UInt32`; `base/math.jl:1276`. -/
def highwordU64 (u : Nat) : Nat := u / 2 ^ 32 % 2 ^ 32
/-- `highword(x::Float64)`; `base/math.jl:1275`. -/
def highword64 (x : FV .f64) : Nat := highwordU64 x.toBits
/-- `highword(x::Float32) = reinterpret(UInt32, x)`; `base/math.jl:1277`. -/
def highword32 (x : FV .f32) : Nat := x.toBits
/-- `fromhighword(Float64, u)`; `base/math.jl:1279`. -/
def fromhighword64 (u : Nat) : FV .f64 := Fl.ofBits (u % 2 ^ 32 * 2 ^ 32)
/-- `fromhighword(Float32, u)`; `base/math.jl:1280`. -/
def fromhighword32 (u : Nat) : FV .f32 := Fl.ofBits (u % 2 ^ 32)
/-- `poshighword(x::UInt64) = highword(x) & 0x7fffffff`; `base/math.jl:1288-1290`. -/
def poshighwordU64 (u : Nat) : Nat := highwordU64 u % 2 ^ 31
def poshighword64 (x : FV .f64) : Nat := poshighwordU64 x.toBits
def poshighword32 (x : FV .f32) : Nat := highword32 x % 2 ^ 31

/-- `signbit(x::Float64/Float32/Float16) = signbit(bitcast(Int, x))`;
`base/floatfuncs.jl:15-17`. -/
def signbitBits (x : FV T) : Bool := decide (wrapInt (FloatIntCov.Float.intTy T) x.toBits < 0)

/-- `copysign(x::Float32, y::Float32) = copysign_float(x, y)`; `base/floatfuncs.jl:5-6`. -/
def copysignF (x y : FV T) : FV T := copysign x y

/-- `copysign(x::Float32/Float64, y::Real) = copysign(x, T(y))` for a float `y` of any
format; `base/floatfuncs.jl:7-8`. -/
def copysignReal {S : FTy} (x : FV T) (y : FV S) : FV T := copysign x (conv y)

/-- `flipsign(x::Float32, y::Float32)`: xor of the sign bits; `base/floatfuncs.jl:11`. -/
def flipsignF (x y : FV T) : FV T :=
  Fl.ofBits (Nat.xor x.toBits (y.toBits / signMask T % 2 * signMask T))

/-- `flipsign(x::Float32/Float64, y::Real) = flipsign(x, T(y))`; `base/floatfuncs.jl:12-13`. -/
def flipsignReal {S : FTy} (x : FV T) (y : FV S) : FV T := flipsignF x (conv y)

/-- `maxintfloat(::Type{T})` for the three formats; `base/floatfuncs.jl:34-36`. -/
def maxintfloat (T : FTy) : FV T := ofInt T (2 ^ (significandBits T + 1))

/-- `maxintfloat(x::T) = maxintfloat(T)`; `base/floatfuncs.jl:37`. -/
def maxintfloatOf (_x : FV T) : FV T := maxintfloat T

/-- `maxintfloat(::Type{S}, ::Type{T}) = min(maxintfloat(S), S(typemax(T)))` for an
integer type `t`; `base/floatfuncs.jl:46`. `min` is `min_float`. -/
def maxintfloatInt (S : FTy) (t : IntTy) : FV S :=
  let a := maxintfloat S
  let b : FV S := Fl.ofInt t.max
  if lt b a then b else a

/-- `maxintfloat() = maxintfloat(Float64)`; `base/floatfuncs.jl:47`. -/
def maxintfloatDefault : FV .f64 := maxintfloat .f64

/-- The two `Union{}` maxintfloat methods throw `MethodError`; `base/floatfuncs.jl:48-49`. -/
def maxintfloatBottom {α : Type} : Jl α := .error (.methodError "maxintfloat")

/-- `_isless(x, y) = (x < y) || (signbit(x) > signbit(y))`; `base/math.jl:833`. -/
def isless_ (x y : FV T) : Bool := lt x y || (x.signbit && !y.signbit)

/-- Generic `min`/`max` for `AbstractFloat`; `base/math.jl:834-835`. -/
def minGeneric (x y : FV T) : FV T := if x.isnan || (!y.isnan && isless_ x y) then x else y
def maxGeneric (x y : FV T) : FV T := if x.isnan || (!y.isnan && isless_ y x) then x else y

/-- `min_float`/`max_float` (LLVM `minimum`/`maximum`: NaN-propagating, `-0.0 < 0.0`);
`base/math.jl:838-839`. -/
def minFloat (x y : FV T) : FV T :=
  if x.isnan then x else if y.isnan then y else if isless_ y x then y else x
def maxFloat (x y : FV T) : FV T :=
  if x.isnan then x else if y.isnan then y else if isless_ x y then y else x

/-- `rem(x::T, p::T, ::RoundingMode{:Nearest})`; `base/math.jl:1122-1145`. `rem(x, 2p)` is
the `base/float.jl` remainder (`FloatIntCov.Float.rem`). -/
def remNearest (x p : FV T) : FV T := Id.run do
  if p.iszero || !x.isfinite || p.isnan then return nan T
  if eq x p then return copysign (zero T) x
  let oldx := x
  let mut x := abs (FloatIntCov.Float.rem x (mul (ofInt T 2) p))
  let p := abs p
  if lt p (mul (ofInt T 2) (floatminT T)) then
    if lt p (mul (ofInt T 2) x) then
      x := sub x p
      if le p (mul (ofInt T 2) x) then
        x := sub x p
  else
    let pHalf := div p (ofInt T 2)
    if lt pHalf x then
      x := sub x p
      if le pHalf x then
        x := sub x p
  return flipsign x oldx

/-- `modf(x::T) where T<:IEEEFloat`; `base/math.jl:1165-1170`. -/
def modf (x : FV T) : FV T × FV T :=
  if x.isinf then (copysign (zero T) x, x)
  else
    let ix := trunc x
    (copysign (sub x ix) x, ix)

/-- Generic `modf(x)` for a float `x`: `isinf(x) ? (flipsign(zero(x), x), x) :
(rem(x, one(x)), trunc(x))`; `base/math.jl:1163`. -/
def modfGeneric (x : FV T) : FV T × FV T :=
  if x.isinf then (flipsign (zero T) x, x)
  else (FloatIntCov.Float.rem x (one T), trunc x)

/-- `add22condh(xh, xl, yh, yl)`; `base/math.jl:1176-1185`. -/
def add22condh (xh xl yh yl : FV .f64) : FV .f64 :=
  let r := add xh yh
  let s := if lt (abs yh) (abs xh) then add (add (add (sub xh r) yh) yl) xl
    else add (add (add (sub yh r) xh) xl) yl
  add r s

end JuliaLean.MathCov.Bits
