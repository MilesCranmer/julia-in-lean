import JuliaLean.Core
import JuliaLean.base.float
import JuliaLean.base.math
import JuliaLean.Runtime.Float
import JuliaLean.base.special.exp

/-!
`cbrt(::Float64)` from `base/special/cbrt.jl`, Julia master `bbfa0ce4150`.
-/

namespace JuliaLean.MathFuncs

open JuliaLean.Float

/-- `highword(x::Float64) = (reinterpret(UInt64, x) >>> 32) % UInt32`; `base/math.jl:1275-1276`. -/
private def highword (x : F64) : Nat := bitsOf x / 2^32

/-- `fromhighword(Float64, u) = reinterpret(Float64, UInt64(u) << 32)`; `base/math.jl:1279`. -/
private def fromhighword (u : Nat) : F64 := ofBitsU (u * 2^32)

/-- `floor(UInt32, y)` for finite `0 ≤ y < 2^32`; `base/special/cbrt.jl:70,76`. -/
private def floorU32 (y : F64) : Nat :=
  let q := F64.toRat y
  (q.1 / (q.2 : Int)).toNat

/-- `_approx_cbrt(x::Float64)`; `base/special/cbrt.jl:63-79`. -/
def approxCbrt (x : F64) : F64 :=
  let adj := F64.sub (F64.div (F64.ofInt (1023 * 2)) (F64.ofInt 3)) (lit 0x3fa0ed8c97e0d750)
  let e2k := F64.ofInt (2^20)
  let u := highword x % 2^31
  if u ≥ highword F64.floatmin then
    let v := (u / 3 + floorU32 (F64.mul adj e2k)) % 2^32
    copysign (fromhighword v) x
  else
    let x := F64.mul x (lit 0x4340000000000000)
    let adj := F64.sub adj (F64.div (F64.ofInt 53) (F64.ofInt 3))
    let u := highword x % 2^31
    let v := (u / 3 + floorU32 (F64.mul adj e2k)) % 2^32
    copysign (fromhighword v) x

/-- `_improve_cbrt(x::Float64, t::Float64)`; `base/special/cbrt.jl:103-142`. -/
def improveCbrt (x t : F64) : F64 :=
  let r := F64.mul (F64.mul t t) (F64.div t x)
  let p := horner r [lit 0x3ffe03e60f61e692, lit 0xbffe28e092f02420, lit 0x3ff9f1604a49d6c2]
  let q := horner r [lit 0xbfe844cbbee751d9, lit 0x3fc2b000d4e4edd7]
  let t := F64.mul t (F64.add p (F64.mul (F64.mul (F64.mul r r) r) q))
  let u := ((bitsOf t + 0x80000000) % 2^64) &&& 0xffffffffc0000000
  let t := ofBitsU u
  let s := F64.mul t t
  let r := F64.div x s
  let w := F64.add t t
  let r := F64.div (F64.sub r t) (F64.add w r)
  F64.muladd t r t

/-- `cbrt(x::Float64)`; `base/special/cbrt.jl:144-150`. -/
def cbrt (x : F64) : F64 :=
  if !F64.isfinite x || F64.iszero x then x
  else improveCbrt x (approxCbrt x)

end JuliaLean.MathFuncs

namespace JuliaLean.MathCov.Special

open JuliaLean JuliaLean.Float JuliaLean.Promotion JuliaLean.MathCov.FP JuliaLean.MathCov.C

/-- `cbrt(x::AbstractFloat) = x < 0 ? -(-x)^(1//3) : x^(1//3)` for a float type with an
arbitrary power `pow`; `base/special/cbrt.jl:36`. -/
def cbrtAbstract {α : Type} (lt0 : α → Bool) (negα : α → α) (pow : α → α) (x : α) : α :=
  if lt0 x then negα (pow (negα x)) else pow x

/-- `_approx_cbrt(x::T)` for `T = Float32, Float64`; `base/special/cbrt.jl:63-79`. The
constants `floor(UInt32, adj * exp2(k))` are evaluated in Float64. -/
def approxCbrt {T : FTy} (x : FV T) : FV T :=
  let k : Nat := if T = .f64 then 20 else 23
  let adj0 : FV .f64 := if T = .f64 then cbrtAdj64 else cbrtAdj32
  let hw (z : FV T) : Nat := if T = .f64 then Bits.highwordU64 z.toBits else z.toBits % 2 ^ 32
  let fromhw (v : Nat) : FV T := if T = .f64 then Fl.ofBits (v % 2 ^ 32 * 2 ^ 32) else Fl.ofBits (v % 2 ^ 32)
  let floorU32 (y : FV .f64) : Nat :=
    let q := (Fl.ofF64 (F64.floor (Fl.toF64 y)) : FV .f64).toRat
    (q.1 / (q.2 : Int)).toNat
  let two_k : FV .f64 := Fl.ofBits ((1023 + k) * 2 ^ 52)
  let u := hw x % 2 ^ 31
  if u ≥ hw (floatminT T) then
    let v := u / 3 + floorU32 (mul adj0 two_k)
    copysign (fromhw (v % 2 ^ 32)) x
  else
    let mif := Bits.maxintfloat T
    let x' := mul x mif
    let e : Int := match Bits.exponent mif with | .ok e => e | .error _ => 0
    let adj := sub adj0 (div (ofInt .f64 e) (ofInt .f64 3))
    let u := hw x' % 2 ^ 31
    let v := u / 3 + floorU32 (mul adj two_k)
    copysign (fromhw (v % 2 ^ 32)) x'

/-- `tt^3` for a Float64 (`literal_pow`, i.e. `tt*tt*tt`). -/
def cube (t : FV .f64) : FV .f64 := mul (mul t t) t

/-- `_improve_cbrt(x::Float32, t::Float32)`; `base/special/cbrt.jl:81-101`. -/
def improveCbrt32 (x t : FV .f32) : FV .f32 :=
  let xx : FV .f64 := conv x
  let step (tt : FV .f64) : FV .f64 :=
    let tt3 := cube tt
    mul tt (div (add (mul (ofInt .f64 2) xx) tt3) (add (conv x) (mul (ofInt .f64 2) tt3)))
  conv (step (step (conv t)))

/-- `cbrt(x::Union{Float32,Float64})`; `base/special/cbrt.jl:144-150`. -/
def cbrt {T : FTy} (x : FV T) : FV T :=
  if !x.isfinite || x.iszero then x
  else
    let t := approxCbrt x
    if T = .f64 then conv (of64 (MathFuncs.improveCbrt (toD x) (toD t)))
    else improveCbrt32Of x t
where
  improveCbrt32Of {T : FTy} (x t : FV T) : FV T := conv (improveCbrt32 (conv x) (conv t))

/-- `cbrt(a::Float16)`; `base/special/cbrt.jl:152-167`. -/
def cbrt16 (a : FV .f16) : FV .f16 :=
  if !a.isfinite || a.iszero then a
  else
    let x : FV .f32 := conv a
    let u := x.toBits % 2 ^ 31
    let v := (u / 3 + 0x2a5119f2) % 2 ^ 32
    let t := copysign (Fl.ofBits v : FV .f32) x
    let nt (t : FV .f32) : FV .f32 :=
      mul cbrtThird32 (add (mul (ofInt .f32 2) t) (div x (mul t t)))
    conv (nt (nt t))

end JuliaLean.MathCov.Special

/-!
# Model of `base/special/cbrt.jl`

Typed source model at Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`. The
Float32 and Float64 union method is represented by `Float32or64`; low-level
IEEE operations use the shared float models.
-/

namespace JuliaLean.base.special.cbrt

open JuliaLean JuliaLean.Float JuliaLean.Promotion JuliaLean.MathCov.FP
open JuliaLean.MathCov

abbrev F32 := FV .f32
abbrev F64 := FV .f64

inductive Float32or64 where
  | f32 : F32 → Float32or64
  | f64 : F64 → Float32or64
  deriving Repr

/--
Julia source: base/special/cbrt.jl:36-36 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cbrt(x::AbstractFloat) = x < 0 ? -(-x)^(1//3) : x^(1//3)
```
-/
def cbrtAbstract {A E : Type} (lt : A → A → Bool) (zero : A) (neg : A → A)
    (pow : A → E → A) (oneThird : E) (x : A) : A :=
  if lt x zero then neg (pow (neg x) oneThird) else pow x oneThird

private def cbrtApprox32 (x : F32) : F32 := Id.run do
  let k : Int := (JuliaLean.FloatIntCov.Float.significandBits .f32 : Int) - (8 * FTy.bytes .f32 - 32 : Int)
  let adj := FP.sub
    (FP.div (FP.ofInt .f64 (2 * (JuliaLean.FloatIntCov.Float.exponentBias .f32 : Int))) (FP.ofInt .f64 3))
    (FP.lit .f64 0x3fa0ed8c97e0d750)
  let u := MathCov.Bits.poshighword32 x
  let floorAdj (a : FV .f64) : Nat :=
    (FP.unsafeTrunc .u32 (FP.floor (FP.mul a (FP.of64 (MathFuncs.exp2Int (JInt.wrap .i64 k)))))).val.toNat
  if u ≥ MathCov.Bits.highword32 (FP.floatminT .f32) then
    let v := (u / 3 + floorAdj adj) % 2^32
    return MathCov.Bits.fromhighword32 v |> fun v => FP.copysign v x
  else
    let x := FP.mul x (MathCov.Bits.maxintfloat .f32)
    let adj := FP.sub adj (FP.div
      (FP.ofInt .f64 (MathCov.Bits.exponentFiniteNonzero (MathCov.Bits.maxintfloat .f32)))
      (FP.ofInt .f64 3))
    let u := MathCov.Bits.poshighword32 x
    let v := (u / 3 + floorAdj adj) % 2^32
    return FP.copysign (MathCov.Bits.fromhighword32 v) x

private def cbrtApprox64 (x : F64) : F64 := Id.run do
  let k : Int := (JuliaLean.FloatIntCov.Float.significandBits .f64 : Int) - (8 * FTy.bytes .f64 - 32 : Int)
  let adj := FP.sub
    (FP.div (FP.ofInt .f64 (2 * (JuliaLean.FloatIntCov.Float.exponentBias .f64 : Int))) (FP.ofInt .f64 3))
    (FP.lit .f64 0x3fa0ed8c97e0d750)
  let floorAdj (a : FV .f64) : Nat :=
    (FP.unsafeTrunc .u32 (FP.floor (FP.mul a (FP.of64 (MathFuncs.exp2Int (JInt.wrap .i64 k)))))).val.toNat
  let u := MathCov.Bits.poshighword64 x
  if u ≥ MathCov.Bits.highword64 (FP.floatminT .f64) then
    let v := (u / 3 + floorAdj adj) % 2^32
    return FP.copysign (MathCov.Bits.fromhighword64 v) x
  else
    let x := FP.mul x (MathCov.Bits.maxintfloat .f64)
    let adj := FP.sub adj (FP.div
      (FP.ofInt .f64 (MathCov.Bits.exponentFiniteNonzero (MathCov.Bits.maxintfloat .f64)))
      (FP.ofInt .f64 3))
    let u := MathCov.Bits.poshighword64 x
    let v := (u / 3 + floorAdj adj) % 2^32
    return FP.copysign (MathCov.Bits.fromhighword64 v) x

/--
Julia source: base/special/cbrt.jl:63-79 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _approx_cbrt(x::T) where {T<:Union{Float32,Float64}}
    # floor(UInt32, adj * exp2(k)) should be evaluated to 2 constants.
    adj = exponent_bias(T)*2/3 - 0.03306235651
    k = significand_bits(T) - (8*sizeof(T) - 32)

    u = highword(x) & 0x7fff_ffff
    if u >= Base.Math.highword(floatmin(T))
        v = div(u, UInt32(3)) + floor(UInt32, adj * exp2(k))
    else
        # subnormal
        x *= maxintfloat(T)
        adj -= exponent(maxintfloat(T))/3
        u = highword(x) & 0x7fff_ffff
        v = div(u, UInt32(3)) + floor(UInt32, adj * exp2(k))
    end
    return copysign(fromhighword(T, v), x)
end
```
-/
def approxCbrt (x : Float32or64) : Float32or64 :=
  match x with
  | .f32 x => .f32 (cbrtApprox32 x)
  | .f64 x => .f64 (cbrtApprox64 x)

/--
Julia source: base/special/cbrt.jl:81-101 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _improve_cbrt(x::Float32, t::Float32)
    # Halley iterations solving
    #   t^2 - x/t == 0
    # with update
    #   t <- t*(t^3 + 2*x)/(2*t^3 + x)

    # Use double precision so that its terms can be arranged for efficiency
    # without causing overflow or underflow.
    xx = Float64(x)
    tt = Float64(t)

    # 1st step: 16 bits accuracy
    tt3 = tt^3
    tt *= (2*xx + tt3)/(x + 2*tt3)

    # 2nd step: 47 bits accuracy
    tt3 = tt^3
    tt *= (2*xx + tt3)/(x + 2*tt3)

    return Float32(tt)
end
```
-/
def improveCbrt32 (x t : F32) : F32 := Id.run do
  let xx := FP.toD x
  let step (tt : JuliaLean.Float.F64) : JuliaLean.Float.F64 := Id.run do
    let tt3 := F64.mul (F64.mul tt tt) tt
    return F64.mul tt (F64.div
      (F64.add (F64.mul (F64.ofInt 2) xx) tt3)
      (F64.add (FP.toD x) (F64.mul (F64.ofInt 2) tt3)))
  return FP.ofD (step (step (FP.toD t)))

/--
Julia source: base/special/cbrt.jl:103-142 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _improve_cbrt(x::Float64, t::Float64)
    # cbrt to 23 bits:
    #
    #    cbrt(x) = t * cbrt(x / t^3) ~= t * P(t^3 / x)
    #
    # where P(r) is a polynomial of degree 4 that approximates 1/cbrt(r)
    # to within 2^-23.5 when |r - 1| < 1/10.  The rough approximation
    # has produced t such that |t/cbrt(x) - 1| ~< 1/32, and cubing this
    # gives us bounds for r = t^3/x.

    r = (t*t)*(t/x)
    t *= (@horner(r, 1.87595182427177009643, -1.88497979543377169875, 1.621429720105354466140) +
          r^3 * @horner(r, -0.758397934778766047437, 0.145996192886612446982))

    # Round t away from zero to 23 bits (sloppily except for ensuring that
    # the result is larger in magnitude than cbrt(x) but not much more than
    # 2 23-bit ulps larger).  With rounding towards zero, the error bound
    # would be ~5/6 instead of ~4/6.  With a maximum error of 2 23-bit ulps
    # in the rounded t, the infinite-precision error in the Newton
    # approximation barely affects third digit in the final error
    # 0.667; the error in the rounded t can be up to about 3 23-bit ulps
    # before the final error is larger than 0.667 ulps.

    u = reinterpret(UInt64, t)
    u = (u +% 0x8000_0000) & UInt64(0xffff_ffff_c000_0000)
    t = reinterpret(Float64, u)

    # one step Newton iteration solving
    #   t^3 - x == 0
    # with update
    #   t <- t + t * (x/t^2 - t) / (3*t)

    # to 53 bits with error < 0.667 ulps
    s = t*t             # t*t is exact
    r = x/s             # error <= 0.5 ulps; |r| < |t|
    w = t+t             # t+t is exact
    r = (r - t)/(w + r) # r-t is exact; w+r ~= 3*t
    t = muladd(t, r, t) # error <= 0.5 + 0.5/3 + epsilon
    return t
end
```
-/
def improveCbrt64 (x t : F64) : F64 := Id.run do
  let x := FP.to64 x
  let t := FP.to64 t
  let r := F64.mul (F64.mul t t) (F64.div t x)
  let p := MathFuncs.horner r [MathFuncs.lit 0x3ffe03e60f61e692, MathFuncs.lit 0xbffe28e092f02420, MathFuncs.lit 0x3ff9f1604a49d6c2]
  let q := MathFuncs.horner r [MathFuncs.lit 0xbfe844cbbee751d9, MathFuncs.lit 0x3fc2b000d4e4edd7]
  let t := F64.mul t (F64.add p (F64.mul (F64.mul (F64.mul r r) r) q))
  let u := Nat.land ((MathFuncs.bitsOf t + 0x80000000) % 2^64) 0xffffffffc0000000
  let t := MathFuncs.ofBitsU u
  let s := F64.mul t t
  let r := F64.div x s
  let w := F64.add t t
  let r := F64.div (F64.sub r t) (F64.add w r)
  FP.of64 (F64.muladd t r t)

/--
Julia source: base/special/cbrt.jl:144-150 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function cbrt(x::Union{Float32,Float64})
    if !isfinite(x) || iszero(x)
        return x
    end
    t = _approx_cbrt(x)
    return _improve_cbrt(x, t)
end
```
-/
def cbrt (x : Float32or64) : Float32or64 :=
  match x with
  | .f32 x =>
    if !FP.isfinite x || FP.iszero x then .f32 x
    else .f32 (improveCbrt32 x (cbrtApprox32 x))
  | .f64 x =>
    if !FP.isfinite x || FP.iszero x then .f64 x
    else .f64 (improveCbrt64 x (cbrtApprox64 x))

/--
Julia source: base/special/cbrt.jl:152-167 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function cbrt(a::Float16)
    if !isfinite(a) || iszero(a)
        return a
    end
    x = Float32(a)

    # 5 bit approximation. Simpler than _approx_cbrt since subnormals can not appear
    u = highword(x) & 0x7fff_ffff
    v = div(u, UInt32(3)) + 0x2a5119f2
    t = copysign(fromhighword(Float32, v), x)

    # 2 newton iterations
    t = 0.33333334f0 * (2f0*t + x/(t*t))
    t = 0.33333334f0 * (2f0*t + x/(t*t))
    return Float16(t)
end
```
-/
def cbrt16 (a : FV .f16) : FV .f16 :=
  if !FP.isfinite a || FP.iszero a then a
  else
    let x : F32 := FP.conv a
    let u := MathCov.Bits.poshighword32 x
    let v := (u / 3 + 0x2a5119f2) % 2^32
    let t : F32 := FP.copysign (MathCov.Bits.fromhighword32 v) x
    let step (t : F32) : F32 := FP.mul (FP.lit .f32 0x3eaaaaab)
      (FP.add (FP.mul (FP.ofInt .f32 2) t) (FP.div x (FP.mul t t)))
    FP.conv (step (step t))

end JuliaLean.base.special.cbrt
