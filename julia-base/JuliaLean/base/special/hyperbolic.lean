import JuliaLean.Core
import JuliaLean.base.float
import JuliaLean.base.math
import JuliaLean.base.floatfuncs
import JuliaLean.base.special.exp

/-!
# Model of `base/special/hyperbolic.jl`

Typed models at Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`. The Float32 and
Float64 union methods use `Float32or64`; later-loaded logarithm methods are typed
parameters in `HyperbolicCalls`.
-/

namespace JuliaLean.base.special.hyperbolic

open JuliaLean JuliaLean.Float JuliaLean.Promotion JuliaLean.MathCov.FP
open JuliaLean.MathCov

abbrev F16 := FV .f16
abbrev F32 := FV .f32
abbrev F64 := FV .f64

inductive Float32or64 where
  | f32 : F32 → Float32or64
  | f64 : F64 → Float32or64
  deriving Repr

structure HyperbolicCalls where
  log32 : F32 → Jl F32
  log64 : F64 → Jl F64
  log1p32 : F32 → Jl F32
  log1p64 : F64 → Jl F64
private def half32 : F32 := FP.lit .f32 0x3f000000
private def half64 : F64 := FP.lit .f64 0x3fe0000000000000

/--
Julia source: base/special/hyperbolic.jl:20-20 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
H_SMALL_X(::Type{Float64}) = 2.0^-28
```
-/
def hSmallX64 : F64 := FP.lit .f64 0x3e30000000000000

/--
Julia source: base/special/hyperbolic.jl:21-21 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
H_MEDIUM_X(::Type{Float64}) = 22.0
```
-/
def hMediumX64 : F64 := FP.lit .f64 0x4036000000000000

/--
Julia source: base/special/hyperbolic.jl:23-23 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
H_SMALL_X(::Type{Float32}) = 2f-12
```
-/
def hSmallX32 : F32 := FP.lit .f32 0x39800000

/--
Julia source: base/special/hyperbolic.jl:24-24 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
H_MEDIUM_X(::Type{Float32}) = 9f0
```
-/
def hMediumX32 : F32 := FP.lit .f32 0x41100000

/--
Julia source: base/special/hyperbolic.jl:26-26 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
H_LARGE_X(::Type{Float64}) = 709.7822265633563 # nextfloat(709.7822265633562)
```
-/
def hLargeX64 : F64 := FP.lit .f64 0x40862e4200001d6c

/--
Julia source: base/special/hyperbolic.jl:28-28 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
H_LARGE_X(::Type{Float32}) = 88.72283f0
```
-/
def hLargeX32 : F32 := FP.lit .f32 0x42b17217

/--
Julia source: base/special/hyperbolic.jl:30-30 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
SINH_SMALL_X(::Type{Float64}) = 2.1
```
-/
def sinhSmallX64 : F64 := FP.lit .f64 0x4000cccccccccccd

/--
Julia source: base/special/hyperbolic.jl:31-31 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
SINH_SMALL_X(::Type{Float32}) = 3.0f0
```
-/
def sinhSmallX32 : F32 := FP.lit .f32 0x40400000

/--
Julia source: base/special/hyperbolic.jl:34-42 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sinh_kernel(x::Float64)
    x2, x2lo = two_mul(x,x)
    hi_order = evalpoly(x2, (8.333333333336817e-3, 1.9841269840165435e-4,
                             2.7557319381151335e-6, 2.5052096530035283e-8,
                             1.6059550718903307e-10, 7.634842144412119e-13,
                             2.9696954760355812e-15))
    hi,lo = exthorner(x2, (1.0, 0.16666666666666635, hi_order))
    return muladd(x, hi, muladd(x, lo, x*x2lo*0.16666666666666635))
end
```
-/
def sinhKernel64 (x : F64) : F64 := Id.run do
  let x := FP.to64 x
  let (x2, x2lo) := MathFuncs.twoMul x x
  let hiOrder := MathFuncs.horner x2 [
    MathFuncs.lit 0x3f811111111118e9, MathFuncs.lit 0x3f2a01a019fb687c,
    MathFuncs.lit 0x3ec71de3a78d06bd, MathFuncs.lit 0x3e5ae6449263db64,
    MathFuncs.lit 0x3de61273bb901e1c, MathFuncs.lit 0x3d6adcdabd0f458c,
    MathFuncs.lit 0x3ceabfa6cc2be8d4]
  let (hi, lo) := MathFuncs.exthorner MathFuncs.twoMul x2 (JuliaLean.Float.F64.one,
    MathFuncs.lit 0x3fc555555555554a, hiOrder)
  return FP.of64 (JuliaLean.Float.F64.muladd x hi
    (JuliaLean.Float.F64.muladd x lo
      (JuliaLean.Float.F64.mul (JuliaLean.Float.F64.mul x x2lo)
        (MathFuncs.lit 0x3fc555555555554a))))

/--
Julia source: base/special/hyperbolic.jl:44-50 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sinh_kernel(x::Float32)
    x=Float64(x)
    res = evalpoly(x*x, (1.0, 0.1666666779967941, 0.008333336726447933,
                         0.00019841001151414065, 2.7555538207080807e-6,
                         2.5143389765825282e-8, 1.6260094552031644e-10))
    return Float32(res*x)
end
```
-/
def sinhKernel32 (x : F32) : F32 :=
  let x64 := FP.toD x
  let res := MathFuncs.horner (JuliaLean.Float.F64.mul x64 x64) [
    MathFuncs.lit 0x3ff0000000000000, MathFuncs.lit 0x3fc555556daa2303,
    MathFuncs.lit 0x3f81111185a737e4, MathFuncs.lit 0x3f2a01890574351c,
    MathFuncs.lit 0x3ec71d81bbc11f40, MathFuncs.lit 0x3e5aff5cc31eed3e,
    MathFuncs.lit 0x3de659031d8501c7]
  FP.ofD (JuliaLean.Float.F64.mul res x64)

/--
Julia source: base/special/hyperbolic.jl:52-56 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function sinh16_kernel(x::Float32)
    res = evalpoly(x*x, (1.0f0, 0.16666667f0, 0.008333337f0, 0.00019841001f0,
                         2.7555539f-6, 2.514339f-8, 1.6260095f-10))
    return Float16(res*x)
end
```
-/
def sinhKernel16 (x : F32) : F16 :=
  let res := MathCov.Exp.horner (FP.mul x x) [
    FP.lit .f32 0x3f800000, FP.lit .f32 0x3e2aaaab, FP.lit .f32 0x3c08888c,
    FP.lit .f32 0x39500c48, FP.lit .f32 0x3638ec0e, FP.lit .f32 0x32d7fae6,
    FP.lit .f32 0x2f32c819]
  FP.conv (FP.mul res x)

private def sinh32Body (x : F32) : F32 := Id.run do
  let absx := FP.abs x
  if FP.le absx sinhSmallX32 then return sinhKernel32 x
  else if FP.le hLargeX32 absx then
    let e := JuliaLean.base.special.exp.exp (FP.mul half32 absx)
    return FP.copysign (FP.mul (FP.mul half32 e) e) x
  else
    let e := JuliaLean.base.special.exp.exp absx
    return FP.copysign (FP.mul half32
      (FP.sub e (FP.div (FP.ofInt .f32 1) e))) x

private def sinh64Body (x : F64) : F64 := Id.run do
  let absx := FP.abs x
  if FP.le absx sinhSmallX64 then return sinhKernel64 x
  else if FP.le hLargeX64 absx then
    let e := JuliaLean.base.special.exp.exp (FP.mul half64 absx)
    return FP.copysign (FP.mul (FP.mul half64 e) e) x
  else
    let e := JuliaLean.base.special.exp.exp absx
    return FP.copysign (FP.mul half64
      (FP.sub e (FP.div (FP.ofInt .f64 1) e))) x

/--
Julia source: base/special/hyperbolic.jl:58-80 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sinh(x::T) where T<:Union{Float32,Float64}
    # Method
    # mathematically sinh(x) is defined to be (exp(x)-exp(-x))/2
    #    1. Sometimes replace x by |x| (sinh(-x) = -sinh(x)).
    #    2. Find the branch and the expression to calculate and return it
    #      a)   0 <= x < SINH_SMALL_X
    #               approximate sinh(x) with a  minimax polynomial
    #      b)   SINH_SMALL_X <= x < H_LARGE_X
    #               return sinh(x) = (exp(x) - exp(-x))/2
    #      d)   H_LARGE_X  <= x
    #               return sinh(x) = exp(x/2)/2 * exp(x/2)
    #               Note that this branch automatically deals with Infs and NaNs

    absx = abs(x)
    if absx <= SINH_SMALL_X(T)
        return sinh_kernel(x)
    elseif absx >= H_LARGE_X(T)
        E = exp(T(.5)*absx)
        return copysign(T(.5)*E*E, x)
    end
    E = exp(absx)
    return copysign(T(.5)*(E - 1/E),x)
end
```
-/
def sinh (x : Float32or64) : Float32or64 :=
  match x with
  | .f32 x => .f32 (sinh32Body x)
  | .f64 x => .f64 (sinh64Body x)

/--
Julia source: base/special/hyperbolic.jl:82-88 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.sinh(a::Float16)
    x = Float32(a)
    absx = abs(x)
    absx <= SINH_SMALL_X(Float32) && return sinh16_kernel(x)
    E = exp(absx)
    return Float16(copysign(.5f0*(E - 1/E),x))
end
```
-/
def sinh16 (a : F16) : F16 :=
  let x : F32 := FP.conv a
  let absx := FP.abs x
  if FP.le absx sinhSmallX32 then sinhKernel16 x
  else
    let e := JuliaLean.base.special.exp.exp absx
    FP.conv (FP.copysign (FP.mul half32
      (FP.sub e (FP.div (FP.ofInt .f32 1) e))) x)

/--
Julia source: base/special/hyperbolic.jl:90-90 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
COSH_SMALL_X(::Type{T}) where T= one(T)
```
-/
def coshSmallX (T : FTy) : FV T := FP.ofInt T 1

/--
Julia source: base/special/hyperbolic.jl:92-94 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function cosh_kernel(x2::Float32)
    return evalpoly(x2, (1.0f0, 0.49999997f0, 0.041666888f0, 0.0013882756f0, 2.549933f-5))
end
```
-/
def coshKernel32 (x2 : F32) : F32 := MathCov.Exp.horner x2 [
  FP.lit .f32 0x3f800000, FP.lit .f32 0x3effffff, FP.lit .f32 0x3d2aaae6,
  FP.lit .f32 0x3ab5f6cd, FP.lit .f32 0x37d5e765]

/--
Julia source: base/special/hyperbolic.jl:96-101 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function cosh_kernel(x2::Float64)
    return evalpoly(x2, (1.0, 0.5000000000000002, 0.04166666666666269,
                         1.3888888889206764e-3, 2.4801587176784207e-5,
                         2.7557345825742837e-7, 2.0873617441235094e-9,
                         1.1663435515945578e-11))
end
```
-/
def coshKernel64 (x2 : F64) : F64 := FP.of64 (MathFuncs.horner (FP.to64 x2) [
  MathFuncs.lit 0x3ff0000000000000, MathFuncs.lit 0x3fe0000000000002,
  MathFuncs.lit 0x3fa5555555555318, MathFuncs.lit 0x3f56c16c16c3a8b9,
  MathFuncs.lit 0x3efa01a017cf8fee, MathFuncs.lit 0x3e927e50e2faf774,
  MathFuncs.lit 0x3e21ee283256325f, MathFuncs.lit 0x3da9a5ee33f739c4])

private def cosh32Body (x : F32) : F32 := Id.run do
  let absx := FP.abs x
  if FP.le absx (coshSmallX .f32) then return coshKernel32 (FP.mul x x)
  else if FP.le hLargeX32 absx then
    let e := JuliaLean.base.special.exp.exp (FP.mul half32 absx)
    return FP.mul (FP.mul half32 e) e
  else
    let e := JuliaLean.base.special.exp.exp absx
    return FP.mul half32 (FP.add e (FP.div (FP.ofInt .f32 1) e))

private def cosh64Body (x : F64) : F64 := Id.run do
  let absx := FP.abs x
  if FP.le absx (coshSmallX .f64) then return coshKernel64 (FP.mul x x)
  else if FP.le hLargeX64 absx then
    let e := JuliaLean.base.special.exp.exp (FP.mul half64 absx)
    return FP.mul (FP.mul half64 e) e
  else
    let e := JuliaLean.base.special.exp.exp absx
    return FP.mul half64 (FP.add e (FP.div (FP.ofInt .f64 1) e))

/--
Julia source: base/special/hyperbolic.jl:103-125 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function cosh(x::T) where T<:Union{Float32,Float64}
    # Method
    # mathematically cosh(x) is defined to be (exp(x)+exp(-x))/2
    #    1. Replace x by |x| (cosh(x) = cosh(-x)).
    #    2. Find the branch and the expression to calculate and return it
    #      a)   x <= COSH_SMALL_X
    #               approximate cosh(x) with a minimax polynomial
    #      b)   COSH_SMALL_X <= x < H_LARGE_X
    #               return cosh(x) = (exp(x) + exp(-x))/2
    #      e)   H_LARGE_X  <= x
    #               return cosh(x) = exp(x/2)/2 * exp(x/2)
    #               Note that this branch automatically deals with Infs and NaNs

    absx = abs(x)
    if absx <= COSH_SMALL_X(T)
        return cosh_kernel(x*x)
    elseif absx >= H_LARGE_X(T)
        E = exp(T(.5)*absx)
        return T(.5)*E*E
    end
    E = exp(absx)
    return T(.5)*(E + 1/E)
end
```
-/
def cosh (x : Float32or64) : Float32or64 :=
  match x with
  | .f32 x => .f32 (cosh32Body x)
  | .f64 x => .f64 (cosh64Body x)

private def sech32Body (x : F32) : F32 := Id.run do
  let absx := FP.abs x
  if !FP.le hLargeX32 absx then return FP.div (FP.ofInt .f32 1) (cosh32Body x)
  let e := JuliaLean.base.special.exp.exp (FP.mul (FP.neg half32) absx)
  return FP.mul (FP.mul (FP.ofInt .f32 2) e) e

/--
Julia source: base/special/hyperbolic.jl:129-134 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sech(x::T) where T<:Union{Float32,Float64}
    absx = abs(x)
    absx >= H_LARGE_X(T) || return inv(cosh(x))
    E = exp(T(-.5)*absx)
    return (2*E)*E
end
```
-/
def sech (x : Float32or64) : Float32or64 :=
  match x with
  | .f32 x => .f32 (sech32Body x)
  | .f64 x => .f64 (Id.run do
      let absx := FP.abs x
      if !FP.le hLargeX64 absx then return FP.div (FP.ofInt .f64 1) (cosh64Body x)
      let e := JuliaLean.base.special.exp.exp (FP.mul (FP.neg half64) absx)
      return FP.mul (FP.mul (FP.ofInt .f64 2) e) e)

private def csch32Body (x : F32) : F32 := Id.run do
  let absx := FP.abs x
  if !FP.le hLargeX32 absx then return FP.div (FP.ofInt .f32 1) (sinh32Body x)
  let e := JuliaLean.base.special.exp.exp (FP.mul (FP.neg half32) absx)
  return FP.copysign (FP.mul (FP.mul (FP.ofInt .f32 2) e) e) x

/--
Julia source: base/special/hyperbolic.jl:135-140 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function csch(x::T) where T<:Union{Float32,Float64}
    absx = abs(x)
    absx >= H_LARGE_X(T) || return inv(sinh(x))
    E = exp(T(-.5)*absx)
    return copysign((2*E)*E, x)
end
```
-/
def csch (x : Float32or64) : Float32or64 :=
  match x with
  | .f32 x => .f32 (csch32Body x)
  | .f64 x => .f64 (Id.run do
      let absx := FP.abs x
      if !FP.le hLargeX64 absx then return FP.div (FP.ofInt .f64 1) (sinh64Body x)
      let e := JuliaLean.base.special.exp.exp (FP.mul (FP.neg half64) absx)
      return FP.copysign (FP.mul (FP.mul (FP.ofInt .f64 2) e) e) x)

/--
Julia source: base/special/hyperbolic.jl:142-142 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sech(x::Float16) = Float16(sech(Float32(x)))
```
-/
def sech16 (x : F16) : F16 := FP.conv (sech32Body (FP.conv x))

/--
Julia source: base/special/hyperbolic.jl:143-143 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
csch(x::Float16) = Float16(csch(Float32(x)))
```
-/
def csch16 (x : F16) : F16 := FP.conv (csch32Body (FP.conv x))

/--
Julia source: base/special/hyperbolic.jl:146-146 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
TANH_LARGE_X(::Type{Float64}) = 44.0
```
-/
def tanhLargeX64 : F64 := FP.lit .f64 0x4046000000000000

/--
Julia source: base/special/hyperbolic.jl:147-147 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
TANH_LARGE_X(::Type{Float32}) = 18.0f0
```
-/
def tanhLargeX32 : F32 := FP.lit .f32 0x41900000

/--
Julia source: base/special/hyperbolic.jl:148-148 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
TANH_SMALL_X(::Type{Float64}) = 1.0
```
-/
def tanhSmallX64 : F64 := FP.lit .f64 0x3ff0000000000000

/--
Julia source: base/special/hyperbolic.jl:149-149 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
TANH_SMALL_X(::Type{Float32}) = 1.3862944f0       #2*log(2)
```
-/
def tanhSmallX32 : F32 := FP.lit .f32 0x3fb17218

/--
Julia source: base/special/hyperbolic.jl:150-156 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function tanh_kernel(x::Float64)
    return evalpoly(x, (1.0, -0.33333333333332904, 0.13333333333267555,
                        -0.05396825393066753, 0.02186948742242217,
                        -0.008863215974794633, 0.003591910693118715,
                        -0.0014542587440487815, 0.0005825521659411748,
                        -0.00021647574085351332, 5.5752458452673005e-5))
end
```
-/
def tanhKernel64 (x : F64) : F64 := FP.of64 (MathFuncs.horner (FP.to64 x) [
  MathFuncs.lit 0x3ff0000000000000, MathFuncs.lit 0xbfd5555555555508,
  MathFuncs.lit 0x3fc111111110b47e, MathFuncs.lit 0xbfaba1ba1b4f12d3,
  MathFuncs.lit 0x3f9664f47509d10f, MathFuncs.lit 0xbf8226e0b5fe36ab,
  MathFuncs.lit 0x3f6d6cc85ea08b17, MathFuncs.lit 0xbf57d39a6fb81983,
  MathFuncs.lit 0x3f4316cd401e8467, MathFuncs.lit 0xbf2c5fb87466544f,
  MathFuncs.lit 0x3f0d3af7e2c4393e])

/--
Julia source: base/special/hyperbolic.jl:157-160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function tanh_kernel(x::Float32)
    return evalpoly(x, (1.0f0, -0.3333312f0, 0.13328037f0,
                        -0.05350336f0, 0.019975215f0, -0.0050525228f0))
end
```
-/
def tanhKernel32 (x : F32) : F32 := MathCov.Exp.horner x [
  FP.lit .f32 0x3f800000, FP.lit .f32 0xbeaaaa63, FP.lit .f32 0x3e087aa6,
  FP.lit .f32 0xbd5b2657, FP.lit .f32 0x3ca3a310, FP.lit .f32 0xbba58fa2]

private def tanh32Body (x : F32) : F32 := Id.run do
  let abs2x := FP.abs (FP.mul (FP.ofInt .f32 2) x)
  if FP.le tanhLargeX32 abs2x then return FP.copysign (FP.ofInt .f32 1) x
  if FP.le abs2x tanhSmallX32 then return FP.mul x (tanhKernel32 (FP.mul x x))
  let k := JuliaLean.base.special.exp.exp abs2x
  return FP.copysign (FP.sub (FP.ofInt .f32 1)
    (FP.div (FP.ofInt .f32 2) (FP.add k (FP.ofInt .f32 1)))) x

private def tanh64Body (x : F64) : F64 := Id.run do
  let abs2x := FP.abs (FP.mul (FP.ofInt .f64 2) x)
  if FP.le tanhLargeX64 abs2x then return FP.copysign (FP.ofInt .f64 1) x
  if FP.le abs2x tanhSmallX64 then return FP.mul x (tanhKernel64 (FP.mul x x))
  let k := JuliaLean.base.special.exp.exp abs2x
  return FP.copysign (FP.sub (FP.ofInt .f64 1)
    (FP.div (FP.ofInt .f64 2) (FP.add k (FP.ofInt .f64 1)))) x

/--
Julia source: base/special/hyperbolic.jl:161-177 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function tanh(x::T) where T<:Union{Float32, Float64}
    # Method
    # mathematically tanh(x) is defined to be (exp(x)-exp(-x))/(exp(x)+exp(-x))
    #    1. reduce x to non-negative by tanh(-x) = -tanh(x).
    #    2. Find the branch and the expression to calculate and return it
    #      a) 0 <= x < H_SMALL_X
    #             Use a minimax polynomial over the range
    #      b) H_SMALL_X <= x < TANH_LARGE_X
    #           1 - 2/(exp(2x) + 1)
    #      c) TANH_LARGE_X <= x
    #            return 1
    abs2x = abs(2x)
    abs2x >= TANH_LARGE_X(T) && return copysign(one(T), x)
    abs2x <= TANH_SMALL_X(T) && return x*tanh_kernel(x*x)
    k = exp(abs2x)
    return copysign(1 - 2/(k+1), x)
end
```
-/
def tanh (x : Float32or64) : Float32or64 :=
  match x with
  | .f32 x => .f32 (tanh32Body x)
  | .f64 x => .f64 (tanh64Body x)

/--
Julia source: base/special/hyperbolic.jl:180-180 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
AH_LN2(::Type{Float64}) = 6.93147180559945286227e-01
```
-/
def ahLn264 : F64 := FP.lit .f64 0x3fe62e42fefa39ef

/--
Julia source: base/special/hyperbolic.jl:181-181 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
AH_LN2(::Type{Float32}) = 6.9314718246f-01
```
-/
def ahLn232 : F32 := FP.lit .f32 0x3f317218

private def asinh32Body (ops : HyperbolicCalls) (x : F32) : Jl F32 := do
  if !FP.isfinite x then return x
  let absx := FP.abs x
  let two := FP.ofInt .f32 2
  let w ← if FP.lt absx two then
    if FP.lt absx hSmallX32 then return x
    let t := FP.mul x x
    ops.log1p32 (FP.add absx (FP.div t
      (FP.add (FP.ofInt .f32 1) (FP.sqrtLlvm (FP.add (FP.ofInt .f32 1) t)))))
  else if FP.lt absx (FP.ofInt .f32 268435456) then
    let t := absx
    ops.log32 (FP.add (FP.mul two t)
      (FP.div (FP.ofInt .f32 1) (FP.add (FP.sqrtLlvm
        (FP.add (FP.mul x x) (FP.ofInt .f32 1))) t)))
  else
    do
      let w ← ops.log32 absx
      pure (FP.add w ahLn232)
  return FP.copysign w x

private def asinh64Body (ops : HyperbolicCalls) (x : F64) : Jl F64 := do
  if !FP.isfinite x then return x
  let absx := FP.abs x
  let two := FP.ofInt .f64 2
  let w ← if FP.lt absx two then
    if FP.lt absx hSmallX64 then return x
    let t := FP.mul x x
    ops.log1p64 (FP.add absx (FP.div t
      (FP.add (FP.ofInt .f64 1) (FP.sqrtLlvm (FP.add (FP.ofInt .f64 1) t)))))
  else if FP.lt absx (FP.ofInt .f64 268435456) then
    let t := absx
    ops.log64 (FP.add (FP.mul two t)
      (FP.div (FP.ofInt .f64 1) (FP.add (FP.sqrtLlvm
        (FP.add (FP.mul x x) (FP.ofInt .f64 1))) t)))
  else
    do
      let w ← ops.log64 absx
      pure (FP.add w ahLn264)
  return FP.copysign w x

/--
Julia source: base/special/hyperbolic.jl:183-219 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :nothrow function asinh(x::T) where T <: Union{Float32, Float64}
    # Method
    # mathematically asinh(x) = sign(x)*log(|x| + sqrt(x*x + 1))
    # is the principle value of the inverse hyperbolic sine
    # 1. Find the branch and the expression to calculate and return it
    #    a) |x| < 2^-28
    #        return x
    #    b) |x| < 2
    #        return sign(x)*log1p(|x| + x^2/(1 + sqrt(1+x^2)))
    #    c) 2 <= |x| < 2^28
    #        return sign(x)*log(2|x|+1/(|x|+sqrt(x*x+1)))
    #    d) |x| >= 2^28
    #        return sign(x)*(log(x)+ln2))
    # Non-finite inputs are handled below; all log/log1p calls receive positive
    # arguments, so this function never throws for Float32/Float64.
    if !isfinite(x)
        return x
    end
    absx = abs(x)
    if absx < T(2)
        # in a)
        if absx < T(2)^-28
            return x
        end
        # in b)
        t = x*x
        w = log1p(absx + t/(T(1) + sqrt(T(1) + t)))
    elseif absx < T(2)^28
        # in c)
        t = absx
        w = log(T(2)*t + T(1)/(sqrt(x*x + T(1)) + t))
    else
        # in d)
        w = log(absx) + AH_LN2(T)
    end
    return copysign(w, x)
end
```
-/
def asinh (ops : HyperbolicCalls) (x : Float32or64) : Jl Float32or64 :=
  match x with
  | .f32 x => do let y ← asinh32Body ops x; pure (.f32 y)
  | .f64 x => do let y ← asinh64Body ops x; pure (.f64 y)

/--
Julia source: base/special/hyperbolic.jl:222-222 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline acosh_domain_error(x) = throw(DomainError(x, "acosh(x) is only defined for x ≥ 1."))
```
-/
def acoshDomainError {A : Type} (_x : A) : Jl A :=
  .error (.domainError "acosh(x) is only defined for x ≥ 1.")

private def acosh32Body (ops : HyperbolicCalls) (x : F32) : Jl F32 := do
  if FP.isnan x then return x
  let one := FP.ofInt .f32 1
  let two := FP.ofInt .f32 2
  if FP.lt x one then acoshDomainError x
  else if FP.eq x one then return FP.zero .f32
  else if FP.lt x two then
    let t := FP.sub x one
    ops.log1p32 (FP.add t (FP.sqrtLlvm (FP.add (FP.mul two t) (FP.mul t t))))
  else if FP.lt x (FP.ofInt .f32 268435456) then
    let t := FP.mul x x
    ops.log32 (FP.sub (FP.mul two x)
      (FP.div one (FP.add x (FP.sqrtLlvm (FP.sub t one)))))
  else do
    let w ← ops.log32 x
    pure (FP.add w ahLn232)

private def acosh64Body (ops : HyperbolicCalls) (x : F64) : Jl F64 := do
  if FP.isnan x then return x
  let one := FP.ofInt .f64 1
  let two := FP.ofInt .f64 2
  if FP.lt x one then acoshDomainError x
  else if FP.eq x one then return FP.zero .f64
  else if FP.lt x two then
    let t := FP.sub x one
    ops.log1p64 (FP.add t (FP.sqrtLlvm (FP.add (FP.mul two t) (FP.mul t t))))
  else if FP.lt x (FP.ofInt .f64 268435456) then
    let t := FP.mul x x
    ops.log64 (FP.sub (FP.mul two x)
      (FP.div one (FP.add x (FP.sqrtLlvm (FP.sub t one)))))
  else do
    let w ← ops.log64 x
    pure (FP.add w ahLn264)

/--
Julia source: base/special/hyperbolic.jl:223-257 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function acosh(x::T) where T <: Union{Float32, Float64}
    # Method
    # mathematically acosh(x) if defined to be log(x + sqrt(x*x-1))
    # 1. Find the branch and the expression to calculate and return it
    #     a) x = 1
    #         return log1p(t+sqrt(2.0*t+t*t)) where t=x-1.
    #     b) 1 < x < 2
    #         return log1p(t+sqrt(2.0*t+t*t)) where t=x-1.
    #     c) 2 <= x <
    #         return log(2x-1/(sqrt(x*x-1)+x))
    #     d) x >= 2^28
    #         return log(x)+ln2
    # Special cases:
    #     if x < 1 throw DomainError

    isnan(x) && return x

    if x < T(1)
        return acosh_domain_error(x)
    elseif x == T(1)
        # in a)
        return T(0)
    elseif x < T(2)
        # in b)
        t = x - T(1)
        return log1p(t + sqrt(T(2)*t + t*t))
    elseif x < T(2)^28
        # in c)
        t = x*x
        return log(T(2)*x - T(1)/(x+sqrt(t - T(1))))
    else
        # in d)
        return log(x) + AH_LN2(T)
    end
end
```
-/
def acosh (ops : HyperbolicCalls) (x : Float32or64) : Jl Float32or64 :=
  match x with
  | .f32 x => do let y ← acosh32Body ops x; pure (.f32 y)
  | .f64 x => do let y ← acosh64Body ops x; pure (.f64 y)

/--
Julia source: base/special/hyperbolic.jl:260-260 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline atanh_domain_error(x) = throw(DomainError(x, "atanh(x) is only defined for |x| ≤ 1."))
```
-/
def atanhDomainError {A : Type} (_x : A) : Jl A :=
  .error (.domainError "atanh(x) is only defined for |x| ≤ 1.")

private def atanh32Body (ops : HyperbolicCalls) (x : F32) : Jl F32 := do
  if FP.isnan x then return x
  let absx := FP.abs x
  let one := FP.ofInt .f32 1
  let half := half32
  if FP.lt one absx then return (← atanhDomainError x)
  let t ← if FP.lt absx half then
    ops.log1p32 (FP.div (FP.mul (FP.ofInt .f32 2) absx) (FP.sub one absx))
  else
    ops.log32 (FP.div (FP.add one absx) (FP.sub one absx))
  return FP.mul half (FP.copysign t x)

private def atanh64Body (ops : HyperbolicCalls) (x : F64) : Jl F64 := do
  if FP.isnan x then return x
  let absx := FP.abs x
  let one := FP.ofInt .f64 1
  let half := half64
  if FP.lt one absx then return (← atanhDomainError x)
  let t ← if FP.lt absx half then
    ops.log1p64 (FP.div (FP.mul (FP.ofInt .f64 2) absx) (FP.sub one absx))
  else
    ops.log64 (FP.div (FP.add one absx) (FP.sub one absx))
  return FP.mul half (FP.copysign t x)

/--
Julia source: base/special/hyperbolic.jl:261-286 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function atanh(x::T) where T <: Union{Float32, Float64}
    # Method
    # 1. Reduce x to positive by atanh(-x) = -atanh(x)
    # 2. Find the branch and the expression to calculate and return it
    #     a) 0 <= x < 0.5
    #         return 0.5*log1p(2x/(1-x))
    #     b) 0.5 <= x <= 1
    #         return 0.5*log((x+1)/(1-x))
    # Special cases:
    #    if |x| > 1 throw DomainError
    isnan(x) && return x

    absx = abs(x)

    if absx > 1
        atanh_domain_error(x)
    end
    if absx < T(0.5)
        # in a)
        t = log1p(T(2)*absx/(T(1)-absx))
    else
        # in b)
        t = log((T(1)+absx)/(T(1)-absx))
    end
    return T(0.5)*copysign(t, x)
end
```
-/
def atanh (ops : HyperbolicCalls) (x : Float32or64) : Jl Float32or64 :=
  match x with
  | .f32 x => do let y ← atanh32Body ops x; pure (.f32 y)
  | .f64 x => do let y ← atanh64Body ops x; pure (.f64 y)

end JuliaLean.base.special.hyperbolic

namespace JuliaLean.NumMisc

/-- The small Float32 branch at `base/special/hyperbolic.jl:174`. -/
def tanhSmall32 (x : NF32) : NF32 :=
  nf32Mul x (nf32Horner (nf32Mul x x) tanhCoefficients32)

def takesTanhSmall32 (x : NF32) : Bool :=
  x.isfinite && !x.signbit &&
    JuliaLean.Promotion.Fl.le (JuliaLean.Promotion.Fl.add x x) (nf32 0x3fb17218)

inductive HVal where
  | negInf | negFinite | negZero | posZero | posFinite | posInf | nan
  deriving DecidableEq, Repr

def HVal.neg : HVal → HVal
  | .negInf => .posInf
  | .negFinite => .posFinite
  | .negZero => .posZero
  | .posZero => .negZero
  | .posFinite => .negFinite
  | .posInf => .negInf
  | .nan => .nan

/-- Sign and special-value branches of `sinh`, `base/special/hyperbolic.jl:58-80`. -/
def hsinh : HVal → HVal
  | .negInf => .negInf
  | .posInf => .posInf
  | .negZero => .negZero
  | .posZero => .posZero
  | .negFinite => .negFinite
  | .posFinite => .posFinite
  | .nan => .nan

/-- Sign and special-value branches of `cosh`, lines 103-125. -/
def hcosh : HVal → HVal
  | .negInf | .posInf => .posInf
  | .negZero | .posZero => .posFinite
  | .negFinite | .posFinite => .posFinite
  | .nan => .nan

/-- Sign and special-value branches of `tanh`, lines 161-177. -/
def htanh : HVal → HVal
  | .negInf => .negFinite
  | .posInf => .posFinite
  | .negZero => .negZero
  | .posZero => .posZero
  | .negFinite => .negFinite
  | .posFinite => .posFinite
  | .nan => .nan

/-- Sign and special-value branches of `asinh`, lines 183-219. -/
def hasinh : HVal → HVal
  | .negInf => .negInf
  | .posInf => .posInf
  | .negZero => .negZero
  | .posZero => .posZero
  | .negFinite => .negFinite
  | .posFinite => .posFinite
  | .nan => .nan

inductive InvSpecial where
  | negInf | negOne | negZero | posZero | posOne | posInf | nan
  deriving DecidableEq, Repr

inductive InvResult where
  | negInf | negZero | posZero | posInf | nan | domainError
  deriving DecidableEq, Repr

def InvResult.neg : InvResult → InvResult
  | .negInf => .posInf
  | .negZero => .posZero
  | .posZero => .negZero
  | .posInf => .negInf
  | .nan => .nan
  | .domainError => .domainError

def InvSpecial.neg : InvSpecial → InvSpecial
  | .negInf => .posInf
  | .negOne => .posOne
  | .negZero => .posZero
  | .posZero => .negZero
  | .posOne => .negOne
  | .posInf => .negInf
  | .nan => .nan

/-- `atanh` special branches, `base/special/hyperbolic.jl:259-286`. -/
def hatanh : InvSpecial → InvResult
  | .negInf | .posInf => .domainError
  | .negOne => .negInf
  | .posOne => .posInf
  | .negZero => .negZero
  | .posZero => .posZero
  | .nan => .nan

/-- `acosh` special branches, `base/special/hyperbolic.jl:221-257`. -/
def hacosh : InvSpecial → InvResult
  | .negInf | .negOne | .negZero | .posZero => .domainError
  | .posOne => .posZero
  | .posInf => .posInf
  | .nan => .nan

namespace Coverage

open JuliaLean

/-! ## `base/special/hyperbolic.jl:20-177` -/

inductive SinhBranch where | kernel | directExp | splitExp deriving DecidableEq, Repr
inductive CoshBranch where | kernel | directExp | splitExp deriving DecidableEq, Repr
inductive TanhBranch where | saturated | kernel | expFormula deriving DecidableEq, Repr

def sinhBranch (absx small large : Int) : SinhBranch :=
  if absx ≤ small then .kernel else if absx ≥ large then .splitExp else .directExp

def coshBranch (absx small large : Int) : CoshBranch :=
  if absx ≤ small then .kernel else if absx ≥ large then .splitExp else .directExp

def tanhBranch (abs2x small large : Int) : TanhBranch :=
  if abs2x ≥ large then .saturated else if abs2x ≤ small then .kernel else .expFormula

def reciprocalHyperbolicBranch (absx large : Int) : Bool := decide (absx ≥ large)

/-! ## `base/special/hyperbolic.jl:180-286` -/

inductive AsinhBranch where | nonfinite | tiny | belowTwo | medium | large deriving DecidableEq, Repr
inductive AcoshBranch where | nan | domain | one | belowTwo | medium | large deriving DecidableEq, Repr
inductive AtanhBranch where | nan | domain | belowHalf | upper deriving DecidableEq, Repr

def asinhBranch (finite : Bool) (absx two tiny large : Int) : AsinhBranch :=
  if !finite then .nonfinite else if absx < tiny then .tiny else if absx < two then .belowTwo
  else if absx < large then .medium else .large

def acoshBranch (nan : Bool) (x one two large : Int) : AcoshBranch :=
  if nan then .nan else if x < one then .domain else if x == one then .one
  else if x < two then .belowTwo else if x < large then .medium else .large

def atanhBranch (nan : Bool) (absx half one : Int) : AtanhBranch :=
  if nan then .nan else if absx > one then .domain else if absx < half then .belowHalf else .upper

end Coverage
end JuliaLean.NumMisc
