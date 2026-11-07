import JuliaLean.Core
import JuliaLean.base.float
import JuliaLean.base.math
import JuliaLean.base.intfuncs
import JuliaLean.base.reduce
import JuliaLean.base.special.exp
import JuliaLean.base.special.log

/-!
Model of the Float64 methods of `base/special/pow.jl`, Julia master `bbfa0ce4150`:
`^(::Float64, ::Float64)`, `^(::Float64, ::Integer)` and both `pow_body` methods.
-/

namespace JuliaLean.MathFuncs

open JuliaLean.Float

/-- `use_power_by_squaring(n) = -2^12 <= n <= 3 * 2^13`; `base/special/pow.jl:1-3`. -/
def usePowerBySquaring (n : Int) : Bool := decide (-4096 ≤ n ∧ n ≤ 24576)

/-- One iteration state `(x, xnlo, y, ynlo)` of the compensated power-by-squaring loop
`while n > 1 ... n >>>= 1 end`, with `fuel` bounding the iterations;
`base/special/pow.jl:130-140`. -/
def powBodyLoop : Nat → F64 → F64 → F64 → F64 → Int → F64 × F64 × F64 × F64
  | 0, x, xnlo, y, ynlo, _ => (x, xnlo, y, ynlo)
  | fuel + 1, x, xnlo, y, ynlo, n =>
    if n > 1 then
      let (y, ynlo) :=
        if n % 2 == 1 then
          let err := F64.muladd y xnlo (F64.mul x ynlo)
          let (y', ynlo') := twoMul x y
          (y', F64.add ynlo' err)
        else (y, ynlo)
      let err := F64.mul (F64.mul x (lit 0x4000000000000000)) xnlo
      let (x', xnlo') := twoMul x x
      powBodyLoop fuel x' (F64.add xnlo' err) y ynlo ((n % 2^64).toNat / 2 : Nat)
    else (x, xnlo, y, ynlo)

/-- Loop and final compensation of `pow_body(x::Float64, n::Integer)`;
`base/special/pow.jl:119-121,130-143`. The final `ifelse(..., muladd(x, y, err), x*y)` is
compiled with the product `x*y` shared by both branches, so that `muladd` is not fused:
on x86 Julia returns `x*y + err` with two roundings (e.g. `3.0^-3` gives
`0x3fa2f684bda12f69`, the fused value would be `0x3fa2f684bda12f68`). -/
def powBodyIFinish (x xnlo : F64) (n : Int) : F64 :=
  let (x, xnlo, y, ynlo) := powBodyLoop 64 x xnlo F64.one F64.zero n
  let err := F64.muladd y xnlo (F64.mul x ynlo)
  if F64.isfinite x && F64.isfinite err && !F64.iszero err then F64.add (F64.mul x y) err
  else F64.mul x y

/-- `pow_body(x::Float64, n::Integer)` for an Int64 value `n`, the compensated power by
squaring; `base/special/pow.jl:118-144`. -/
def powBodyI (x : F64) (n : Int) : F64 :=
  if n == 3 then F64.mul (F64.mul x x) x
  else if n < 0 then
    let rx := F64.div F64.one x
    if n == -2 then F64.mul rx rx
    else
      let xnlo := if F64.isfinite x then
          F64.mul (F64.neg (F64.fma x rx (lit 0xbff0000000000000))) rx
        else F64.zero true
      powBodyIFinish rx xnlo (JInt.wrap .i64 (-n)).val
  else powBodyIFinish x (F64.zero true) n

/-- `pow_body(x::Float64, y::Float64)`; `base/special/pow.jl:91-103`. -/
def powBodyF (x y : F64) : F64 :=
  let xu := if bitsOf x < 2^52 then
      (Nat.land (bitsOf (F64.mul x (lit 0x4330000000000000))) (2^63 - 1) + 2^64 - 52 * 2^52) % 2^64
    else bitsOf x
  let (logxhi, logxlo) := logExt xu
  let (xyhi, xylo) := twoMul logxhi y
  let xylo := F64.muladd logxlo y xylo
  let hi := F64.add xyhi xylo
  expImplLo hi (F64.sub xylo (F64.sub hi xyhi)) .e

/-- Body of `^(x::Float64, y::Float64)` after the clamp of `y` to `|y| <= 0x1.8p62`;
`base/special/pow.jl:16-29`. `unsafe_trunc(Int64, y)` is exact truncation and `y == yint`
is exact comparison. -/
def powFFClamped (x y : F64) : Jl F64 :=
  let (num, den) := F64.toRat y
  let yint := num.tdiv (den : Int)
  let yisint := num == yint * (den : Int)
  if yisint && yint == 0 then .ok F64.one
  else if yisint && usePowerBySquaring yint then .ok (powBodyI x yint)
  else if 2 * bitsOf x % 2^64 == 0 then
    .ok (boolMul copysign (!F64.lt F64.zero y) (F64.mul (F64.abs y) F64.inf))
  else if F64.lt x F64.zero && !yisint then .error (.domainError "^")
  else
    let s : Int := if F64.lt x F64.zero then (if yint.tmod 2 != 0 then -1 else 1) else 1
    if !F64.isfinite x then
      .ok (boolMul copysign (F64.lt F64.zero y || F64.isnan x) (copysign x (F64.ofInt s)))
    else .ok (copysign (powBodyF (F64.abs x) y) (F64.ofInt s))

/-- `^(x::Float64, y::Float64)`; `base/special/pow.jl:7-30`. -/
def powFF (x y : F64) : Jl F64 :=
  if bitsOf x == 0x3ff0000000000000 then .ok F64.one
  else if !F64.lt (F64.abs y) (lit 0x43d8000000000000) then
    if F64.isnan y then .ok y
    else powFFClamped x (F64.mul (signF y) (lit 0x43d8000000000000))
  else powFFClamped x y

/-- `^(x::Float64, n::Integer)` for the mathematical value `n` of any integer type;
`clamp(n, Int64)` saturates, `isodd(n)` uses the original `n`; `base/special/pow.jl:58-76`. -/
def powFI (x : F64) (n : Int) : F64 :=
  let n64 := if n > 2^63 - 1 then 2^63 - 1 else if n < -2^63 then -2^63 else n
  if n64 == 0 then F64.one
  else if usePowerBySquaring n64 then powBodyI x n64
  else if F64.isnan x then x
  else
    let s := if F64.signbit x && n.tmod 2 != 0 then lit 0xbff0000000000000 else F64.one
    let x := F64.abs x
    let y := F64.ofInt n64
    let (num, den) := F64.toRat y
    if num == n64 * (den : Int) then copysign (powBodyF x y) s
    else
      let n2 := n64.tmod 1024
      let y := F64.ofInt (n64 - n2)
      F64.mul (powBodyF x y) (copysign (powBodyI x n2) s)

end JuliaLean.MathFuncs

namespace JuliaLean.MathCov.Special

open JuliaLean JuliaLean.Float JuliaLean.Promotion JuliaLean.MathCov.FP JuliaLean.MathCov.C

/-- `use_power_by_squaring(n) = -2^12 <= n <= 3 * 2^13`; `base/special/pow.jl:1-3`. -/
def usePowerBySquaring (n : Int) : Bool := decide (-2 ^ 12 ≤ n ∧ n ≤ 3 * 2 ^ 13)

/-- `pow_body(x::Union{Float16,Float32}, n::Int32)`; `base/special/pow.jl:109-114`. -/
def powBodyI {T : FTy} (x : FV T) (n : Int) : FV T :=
  if n == -2 then let i := div (one T) x; mul i i
  else if n == 3 then mul (mul x x) x
  else if n < 0 then
    conv (powerBySquaring (div (one (widenTy T)) (conv x : FV (widenTy T))) (-n).toNat)
  else conv (powerBySquaring (conv x : FV (widenTy T)) n.toNat)

/-- `pow_body(x::T, y) = T(exp2(log2(abs(widen(x))) * y))` for `T = Float16, Float32`
and a `Float64` (or narrower) `y`; `base/special/pow.jl:105-107`. `log2`/`exp2` are the
`Float64` methods for `Float32` and the `Float32` methods for `Float16`. -/
def powBodyF (T : FTy) (x : FV T) (y : FV .f64) : FV T :=
  match T with
  | .f32 =>
    let l := match MathFuncs.log2 (toD (abs x)) with
      | .ok v => v
      | .error _ => F64.nan
    conv (of64 (MathFuncs.exp2 (F64.mul l (Fl.toF64 y))))
  | .f16 =>
    let w : FV .f32 := abs (conv x)
    let l := match Log.log2F32 w with
      | .ok v => v
      | .error _ => nan .f32
    conv (Exp.expImpl32 (mul l (conv y)) .two)
  | .f64 => x

/-- `x == yint` for a float `y` and the `Int32` from `unsafe_trunc`. -/
def eqInt {T : FTy} (y : FV T) (n : Int) : Bool := eq y (ofInt T n)

/-- `^(x::T, y::T) where T <: Union{Float16, Float32}`; `base/special/pow.jl:34-56`. -/
def powFF {T : FTy} (x y : FV T) : Jl (FV T) := do
  if eq x (one T) then return one T
  let maxExp : FV T := if T = .f16 then powMaxExp16Of T else powMaxExp32Of T
  let mut y := y
  if !(lt (abs y) maxExp) then
    if y.isnan then return y
    y := mul (if y.signbit then neg (one T) else one T) maxExp
  let yint := (unsafeTrunc .i32 y).val
  let yisint := eqInt y yint
  if yisint then
    if yint == 0 then return one T
    if usePowerBySquaring yint then return powBodyI x yint
  let mut s : Int := 1
  if lt x (zero T) then
    if !yisint then throw (.domainError "Exponentiation yielding a complex result")
    s := if yint % 2 != 0 then -1 else 1
  if !x.isfinite then
    return boolMul (lt (zero T) y || x.isnan) (copysign x (ofInt T s))
  return copysign (powBodyF T (abs x) (conv y)) (ofInt T s)
where
  powMaxExp16Of (T : FTy) : FV T := conv powMaxExp16
  powMaxExp32Of (T : FTy) : FV T := conv powMaxExp32


/-- `^(x::T, n::Integer) where T <: Union{Float16, Float32}`; `base/special/pow.jl:80-89`. -/
def powFI {T : FTy} (x : FV T) (n : Int) : FV T :=
  let n32 := clamp32 n
  if n32 == 0 then one T
  else if usePowerBySquaring n32 then powBodyI x n32
  else
    let s := if x.signbit && n % 2 != 0 then neg (one T) else one T
    let x := abs x
    copysign (powBodyF T x (ofInt .f64 n32)) s

end JuliaLean.MathCov.Special

/-!
# Model of `base/special/pow.jl`

Typed source models at Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`. Narrow
IEEE unions and generic integer dispatch are represented by explicit typed inputs;
logarithms for narrow `pow_body` calls remain interfaces to the later log model.
-/

namespace JuliaLean.base.special.pow

open JuliaLean JuliaLean.Float JuliaLean.Promotion JuliaLean.MathCov.FP
open JuliaLean.MathCov

abbrev F16 := FV .f16
abbrev F32 := FV .f32
abbrev F64 := FV .f64

inductive NarrowFloat where
  | f16 : F16 → NarrowFloat
  | f32 : F32 → NarrowFloat
  deriving Repr

inductive NarrowPair where
  | f16 : F16 → F16 → NarrowPair
  | f32 : F32 → F32 → NarrowPair

inductive PowerExponent where
  | f16 : F16 → PowerExponent
  | f32 : F32 → PowerExponent
  | f64 : F64 → PowerExponent

structure NarrowLogCalls where
  log2F32 : F32 → Jl F32
  log2F64 : JuliaLean.Float.F64 → Jl JuliaLean.Float.F64

structure IntegerPowerOps (N : Type) where
  clamp64 : N → JInt .i64
  clamp32 : N → JInt .i32
  isOdd : N → Bool

structure PowLoopOps (N : Type) where
  moreThanOne : N → Bool
  isOdd : N → Bool
  isThree : N → Bool
  isMinusTwo : N → Bool
  isNegative : N → Bool
  negate : N → N
  shiftRightOne : N → N

structure PowBodyState (N : Type) where
  x : JuliaLean.Float.F64
  xnlo : JuliaLean.Float.F64
  y : JuliaLean.Float.F64
  ynlo : JuliaLean.Float.F64
  n : N

private def int64PowLoopOps : PowLoopOps (JInt .i64) := {
  moreThanOne := fun n => n.val > 1,
  isOdd := fun n => n.val.tmod 2 != 0,
  isThree := fun n => n.val == 3,
  isMinusTwo := fun n => n.val == -2,
  isNegative := fun n => n.val < 0,
  negate := fun n => -n,
  shiftRightOne := fun n => JInt.wrap .i64 (n.val / 2) }
/--
Julia source: base/special/pow.jl:91-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :foldable @noinline function pow_body(x::Float64, y::Float64)
    xu = reinterpret(UInt64, x)
    if xu < (UInt64(1)<<52) # x is subnormal
        xu = reinterpret(UInt64, x * 0x1p52) # normalize x
        xu &= ~sign_mask(Float64)
        xu -%= (UInt64(52) << 52) # mess with the exponent
    end
    logxhi,logxlo = _log_ext(xu)
    xyhi, xylo = two_mul(logxhi,y)
    xylo = muladd(logxlo, y, xylo)
    hi = xyhi+xylo
    return @inline Base.Math.exp_impl(hi, xylo-(hi-xyhi), Val(:ℯ))
end
```
-/
def powBodyF64 (x y : F64) : F64 :=
  let xu := if MathFuncs.bitsOf (FP.to64 x) < 2^52 then
      (Nat.land (MathFuncs.bitsOf (JuliaLean.Float.F64.mul (FP.to64 x)
        (MathFuncs.lit 0x4330000000000000))) (2^63 - 1) + 2^64 - 52 * 2^52) % 2^64
    else MathFuncs.bitsOf (FP.to64 x)
  let (logxhi, logxlo) := MathFuncs.logExt xu
  let (xyhi, xylo) := MathFuncs.twoMul logxhi (FP.to64 y)
  let xylo := JuliaLean.Float.F64.muladd logxlo (FP.to64 y) xylo
  let hi := JuliaLean.Float.F64.add xyhi xylo
  FP.of64 (MathFuncs.expImplLo hi
    (JuliaLean.Float.F64.sub xylo (JuliaLean.Float.F64.sub hi xyhi)) .e)

/--
Julia source: base/special/pow.jl:118-144 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :terminates_locally @noinline function pow_body(x::Float64, n::Integer)
    y = 1.0
    xnlo = -0.0
    ynlo = 0.0
    n == 3 && return x*x*x # keep compatibility with literal_pow
    if n < 0
        rx = inv(x)
        n==-2 && return rx*rx #keep compatibility with literal_pow
        isfinite(x) && (xnlo = -fma(x, rx, -1.) * rx)
        x = rx
        n = -n
    end
    while n > 1
        if n&1 > 0
            err = muladd(y, xnlo, x*ynlo)
            y, ynlo = two_mul(x,y)
            ynlo += err
        end
        err = x*2*xnlo
        x, xnlo = two_mul(x, x)
        xnlo += err
        n >>>= 1
    end
    err = muladd(y, xnlo, x*ynlo)
    # x*y when err is zero, to keep the sign of a zero result
    return ifelse(isfinite(x) & isfinite(err) & !iszero(err), muladd(x, y, err), x*y)
end
```
-/
def powBodyInteger {N : Type} (ops : PowLoopOps N) (x : F64) (n : N) : Option (Jl F64) := Id.run do
  let one := JuliaLean.Float.F64.one
  let zeroNeg := JuliaLean.MathFuncs.lit 0x8000000000000000
  
  if ops.isThree n then return some (.ok (FP.of64 (JuliaLean.Float.F64.mul
    (JuliaLean.Float.F64.mul (FP.to64 x) (FP.to64 x)) (FP.to64 x))))
  let mut x := FP.to64 x
  let mut xnlo := zeroNeg
  let mut n := n
  if ops.isNegative n then
    let rx := JuliaLean.Float.F64.div one x
    if ops.isMinusTwo n then return some (.ok (FP.of64 (JuliaLean.Float.F64.mul rx rx)))
    if JuliaLean.Float.F64.isfinite x then
      xnlo := JuliaLean.Float.F64.mul
        (JuliaLean.Float.F64.neg (JuliaLean.Float.F64.fma x rx (JuliaLean.MathFuncs.lit 0xbff0000000000000))) rx
    x := rx
    n := ops.negate n
  let initial : PowBodyState N := { x, xnlo, y := one, ynlo := JuliaLean.Float.F64.zero, n }
  let loop := JuliaLean.base.reduce.whileLoop (fun state =>
    if ops.moreThanOne state.n then
      let (y, ynlo) := if ops.isOdd state.n then
        let err := JuliaLean.Float.F64.muladd state.y state.xnlo
          (JuliaLean.Float.F64.mul state.x state.ynlo)
        let (y, ynlo) := MathFuncs.twoMul state.x state.y
        (y, JuliaLean.Float.F64.add ynlo err)
      else (state.y, state.ynlo)
      let err := JuliaLean.Float.F64.mul
        (JuliaLean.Float.F64.mul state.x (JuliaLean.MathFuncs.lit 0x4000000000000000)) state.xnlo
      let (x, xnlo) := MathFuncs.twoMul state.x state.x
      let nextState : PowBodyState N := {
        x := x,
        xnlo := JuliaLean.Float.F64.add xnlo err,
        y := y,
        ynlo := ynlo,
        n := ops.shiftRightOne state.n
      }
      .ok (.inr nextState)
    else .ok (.inl state)) initial
  match loop with
  | none => return none
  | some (.error e) => return some (.error e)
  | some (.ok state) =>
    let err := JuliaLean.Float.F64.muladd state.y state.xnlo
      (JuliaLean.Float.F64.mul state.x state.ynlo)
    let product := JuliaLean.Float.F64.mul state.x state.y
    let value := if JuliaLean.Float.F64.isfinite state.x &&
        JuliaLean.Float.F64.isfinite err && !JuliaLean.Float.F64.iszero err then
      JuliaLean.Float.F64.muladd state.x state.y err
    else product
    return some (.ok (FP.of64 value))
/--
Julia source: base/special/pow.jl:1-3 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function use_power_by_squaring(n::Integer)
    -2^12 <= n <= 3 * 2^13
end
```
-/
def usePowerBySquaring (n : Int) : Bool := decide (-4096 ≤ n ∧ n ≤ 24576)

/--
Julia source: base/special/pow.jl:7-30 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@constprop :aggressive function ^(x::Float64, y::Float64)
    xu = reinterpret(UInt64, x)
    xu == reinterpret(UInt64, 1.0) && return 1.0
    # Exponents greater than this will always overflow or underflow.
    # Note that NaN can pass through this, but that will end up fine.
    if !(abs(y)<0x1.8p62)
        isnan(y) && return y
        y = sign(y)*0x1.8p62
    end
    yint = unsafe_trunc(Int64, y) # This is actually safe since julia freezes the result
    yisint = y == yint
    if yisint
        yint == 0 && return 1.0
        use_power_by_squaring(yint) && return @noinline pow_body(x, yint)
    end
    2*xu==0 && return abs(y)*Inf*(!(y>0)) # if x === +0.0 or -0.0 (Inf * false === 0.0)
    s = 1
    if x < 0
        !yisint && throw_exp_domainerror(x) # y isn't an integer
        s = ifelse(isodd(yint), -1, 1)
    end
    !isfinite(x) && return copysign(x,s)*(y>0 || isnan(x))           # x is inf or NaN
    return copysign(pow_body(abs(x), y), s)
end
```
-/
def powFF64 (x y : F64) : Option (Jl F64) := Id.run do
  let xu := MathFuncs.bitsOf (FP.to64 x)
  if xu == 0x3ff0000000000000 then return some (.ok (FP.ofInt .f64 1))
  let mut y := y
  if !FP.lt (FP.abs y) (FP.lit .f64 0x43d8000000000000) then
    if FP.isnan y then return some (.ok y)
    y := FP.mul (if y.signbit then FP.ofInt .f64 (-1) else FP.ofInt .f64 1)
      (FP.lit .f64 0x43d8000000000000)
  let yint := FP.unsafeTrunc .i64 y
  let yisint := FP.eq y (FP.ofInt .f64 yint.val)
  if yisint then
    if yint.val == 0 then return some (.ok (FP.ofInt .f64 1))
    if usePowerBySquaring yint.val then
      return powBodyInteger int64PowLoopOps x yint
  if (2 * xu) % 2^64 == 0 then
    let magnitude := JuliaLean.Float.F64.mul (FP.to64 (FP.abs y)) JuliaLean.Float.F64.inf
    return some (.ok (FP.of64 (JuliaLean.MathFuncs.boolMul JuliaLean.MathFuncs.copysign (!FP.lt (FP.ofInt .f64 0) y) magnitude)))
  let mut s : Int := 1
  if FP.lt x (FP.zero .f64) then
    if !yisint then return some (JuliaLean.base.math.throwExpDomainError x)
    s := if yint.val.tmod 2 != 0 then -1 else 1
  if !FP.isfinite x then
    return some (.ok (FP.of64 (JuliaLean.MathFuncs.boolMul JuliaLean.MathFuncs.copysign
      (FP.lt (FP.ofInt .f64 0) y || FP.isnan x)
      (FP.to64 (FP.copysign x (FP.ofInt .f64 s))))))
  return some (.ok (FP.copysign (powBodyF64 (FP.abs x) y) (FP.ofInt .f64 s)))

private def powBodyFloat16 (logs : NarrowLogCalls) (x : F16)
    (y : PowerExponent) : Jl F16 := do
  let l ← logs.log2F32 (FP.abs (FP.conv x))
  match y with
  | .f16 y => return FP.conv (JuliaLean.base.special.exp.exp2 (FP.mul l (FP.conv y)))
  | .f32 y => return FP.conv (JuliaLean.base.special.exp.exp2 (FP.mul l y))
  | .f64 y =>
    let p := JuliaLean.Float.F64.mul (FP.toD l) (FP.toD y)
    return FP.conv (FP.of64 (MathFuncs.exp2 p))

private def powBodyFloat32 (logs : NarrowLogCalls) (x : F32)
    (y : PowerExponent) : Jl F32 := do
  let l ← logs.log2F64 (FP.toD (FP.abs x))
  let y : JuliaLean.Float.F64 := match y with
    | .f16 y => FP.toD (FP.conv y : F32)
    | .f32 y => FP.toD y
    | .f64 y => FP.toD y
  return FP.ofD (MathFuncs.exp2 (JuliaLean.Float.F64.mul l y))
private def toBaseFloat32 (x : F32) : JuliaLean.base.float.FV .f32 :=
  JuliaLean.Promotion.Fl.ofBits x.toBits

private def fromBaseFloat32 (x : JuliaLean.base.float.FV .f32) : F32 :=
  FP.lit .f32 x.toBits

private def toBaseFloat64 (x : F64) : JuliaLean.base.float.FV .f64 :=
  JuliaLean.Promotion.Fl.ofBits x.toBits

private def fromBaseFloat64 (x : JuliaLean.base.float.FV .f64) : F64 :=
  FP.lit .f64 x.toBits

private def powBodyI16 (x : F16) (n : JInt .i32) : Jl F16 := do
  if n.val == -2 then
    let i := FP.div (FP.ofInt .f16 1) x
    return FP.mul i i
  if n.val == 3 then return FP.mul (FP.mul x x) x
  let widened : F32 := FP.conv x
  if n.val < 0 then
    let inverse := FP.div (FP.ofInt .f32 1) widened
    let result ← JuliaLean.base.intfuncs.powerFloat .f32 (toBaseFloat32 inverse) (-n).val
    return FP.conv (fromBaseFloat32 result)
  let result ← JuliaLean.base.intfuncs.powerFloat .f32 (toBaseFloat32 widened) n.val
  return FP.conv (fromBaseFloat32 result)

private def powBodyI32 (x : F32) (n : JInt .i32) : Jl F32 := do
  if n.val == -2 then
    let i := FP.div (FP.ofInt .f32 1) x
    return FP.mul i i
  if n.val == 3 then return FP.mul (FP.mul x x) x
  let widened : F64 := FP.conv x
  if n.val < 0 then
    let inverse := FP.div (FP.ofInt .f64 1) widened
    let result ← JuliaLean.base.intfuncs.powerFloat .f64 (toBaseFloat64 inverse) (-n).val
    return FP.conv (fromBaseFloat64 result)
  let result ← JuliaLean.base.intfuncs.powerFloat .f64 (toBaseFloat64 widened) n.val
  return FP.conv (fromBaseFloat64 result)

private def powBodyFloatNarrow (logs : NarrowLogCalls) (x : NarrowFloat)
    (y : PowerExponent) : Jl NarrowFloat := do
  match x with
  | .f16 x => return .f16 (← powBodyFloat16 logs x y)
  | .f32 x => return .f32 (← powBodyFloat32 logs x y)

private def powFF16 (logs : NarrowLogCalls) (x y : F16) : Jl F16 := do
  if FP.eq x (FP.ofInt .f16 1) then return FP.ofInt .f16 1
  let mut y := y
  if !FP.lt (FP.abs y) JuliaLean.MathCov.C.powMaxExp16 then
    if FP.isnan y then return y
    y := FP.mul (if y.signbit then FP.ofInt .f16 (-1) else FP.ofInt .f16 1)
      JuliaLean.MathCov.C.powMaxExp16
  let yint := FP.unsafeTrunc .i32 y
  let yisint := FP.eq y (FP.ofInt .f16 yint.val)
  if yisint then
    if yint.val == 0 then return FP.ofInt .f16 1
    if usePowerBySquaring yint.val then
      return (← powBodyI16 x yint)
  let mut s : Int := 1
  if FP.lt x (FP.zero .f16) then
    if !yisint then return (← JuliaLean.base.math.throwExpDomainError x)
    s := if yint.val.tmod 2 != 0 then -1 else 1
  if !FP.isfinite x then
    return JuliaLean.MathCov.Special.boolMul
      (FP.lt (FP.zero .f16) y || FP.isnan x) (FP.copysign x (FP.ofInt .f16 s))
  let value ← powBodyFloat16 logs (FP.abs x) (.f16 y)
  return FP.copysign value (FP.ofInt .f16 s)

private def powFF32 (logs : NarrowLogCalls) (x y : F32) : Jl F32 := do
  if FP.eq x (FP.ofInt .f32 1) then return FP.ofInt .f32 1
  let mut y := y
  if !FP.lt (FP.abs y) JuliaLean.MathCov.C.powMaxExp32 then
    if FP.isnan y then return y
    y := FP.mul (if y.signbit then FP.ofInt .f32 (-1) else FP.ofInt .f32 1)
      JuliaLean.MathCov.C.powMaxExp32
  let yint := FP.unsafeTrunc .i32 y
  let yisint := FP.eq y (FP.ofInt .f32 yint.val)
  if yisint then
    if yint.val == 0 then return FP.ofInt .f32 1
    if usePowerBySquaring yint.val then
      return (← powBodyI32 x yint)
  let mut s : Int := 1
  if FP.lt x (FP.zero .f32) then
    if !yisint then return (← JuliaLean.base.math.throwExpDomainError x)
    s := if yint.val.tmod 2 != 0 then -1 else 1
  if !FP.isfinite x then
    return JuliaLean.MathCov.Special.boolMul
      (FP.lt (FP.zero .f32) y || FP.isnan x) (FP.copysign x (FP.ofInt .f32 s))
  let value ← powBodyFloat32 logs (FP.abs x) (.f32 y)
  return FP.copysign value (FP.ofInt .f32 s)

/--
Julia source: base/special/pow.jl:34-56 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@constprop :aggressive function ^(x::T, y::T) where T <: Union{Float16, Float32}
    x == 1 && return one(T)
    # Exponents greater than this will always overflow or underflow.
    # Note that NaN can pass through this, but that will end up fine.
    max_exp = T == Float16 ? T(3<<14) : T(0x1.Ap30)
    if !(abs(y)<max_exp)
        isnan(y) && return y
        y = sign(y)*max_exp
    end
    yint = unsafe_trunc(Int32, y) # This is actually safe since julia freezes the result
    yisint = y == yint
    if yisint
        yint == 0 && return one(T)
        use_power_by_squaring(yint) && return pow_body(x, yint)
    end
    s = 1
    if x < 0
        !yisint && throw_exp_domainerror(x) # y isn't an integer
        s = ifelse(isodd(yint), -1, 1)
    end
    !isfinite(x) && return copysign(x,s)*(y>0 || isnan(x)) # x is inf or NaN
    return copysign(pow_body(abs(x), y), s)
end
```
-/
def powFFNarrow (logs : NarrowLogCalls) (args : NarrowPair) : Jl NarrowFloat := do
  match args with
  | .f16 x y => return .f16 (← powFF16 logs x y)
  | .f32 x y => return .f32 (← powFF32 logs x y)

/--
Julia source: base/special/pow.jl:58-76 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@constprop :aggressive @inline function ^(x::Float64, n::Integer)
    n64 = clamp(n, Int64)
    n64 == 0 && return one(x)
    if use_power_by_squaring(n64)
        return pow_body(x, n64)
    else
        isnan(x) && return x
        s = ifelse(signbit(x) && isodd(n), -1.0, 1.0)
        x = abs(x)
        y = float(n64)
        if y == n64
            return copysign(pow_body(x, y), s)
        else
            n2 = n64 % 1024
            y = float(n64 - n2)
            return pow_body(x, y) * copysign(pow_body(x, n2), s)
        end
    end
end
```
-/
def powFI64 {N : Type} (ops : IntegerPowerOps N) (x : F64) (n : N) : Option (Jl F64) := Id.run do
  let n64 := ops.clamp64 n
  if n64.val == 0 then return some (.ok (FP.ofInt .f64 1))
  if usePowerBySquaring n64.val then return powBodyInteger int64PowLoopOps x n64
  if FP.isnan x then return some (.ok x)
  let s : F64 := if x.signbit && ops.isOdd n then FP.ofInt .f64 (-1) else FP.ofInt .f64 1
  let x := FP.abs x
  let y := FP.ofInt .f64 n64.val
  if FP.eq y (FP.ofInt .f64 n64.val) then
    return some (.ok (FP.copysign (powBodyF64 x y) s))
  let n2 := JInt.wrap .i64 (n64.val.tmod 1024)
  let y := FP.ofInt .f64 (n64.val - n2.val)
  let partialValue := powBodyF64 x y
  let squared ← powBodyInteger int64PowLoopOps x n2
  match squared with
  | none => return none
  | some (.error e) => return some (.error e)
  | some (.ok v) => return some (.ok (FP.mul partialValue (FP.copysign v s)))


/--
Julia source: base/special/pow.jl:80-89 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@constprop :aggressive @inline function ^(x::T, n::Integer) where T <: Union{Float16, Float32}
    n32 = clamp(n, Int32)
    # Exponents greater than this will always overflow or underflow.
    # Note that NaN can pass through this, but that will end up fine.
    n32 == 0 && return one(x)
    use_power_by_squaring(n32) && return pow_body(x, n32)
    s = ifelse(signbit(x) && isodd(n), -one(T), one(T))
    x = abs(x)
    return copysign(pow_body(x, widen(T)(n32)), s)
end
```
-/
def powFINarrow {N : Type} (ops : IntegerPowerOps N) (logs : NarrowLogCalls)
    (x : NarrowFloat) (n : N) : Jl NarrowFloat := do
  match x with
  | .f16 x =>
    let n32 := ops.clamp32 n
    if n32.val == 0 then return .f16 (FP.ofInt .f16 1)
    if usePowerBySquaring n32.val then
      return .f16 (← powBodyI16 x n32)
    let s := if x.signbit && ops.isOdd n then FP.ofInt .f16 (-1) else FP.ofInt .f16 1
    let y := FP.ofInt .f32 n32.val
    let value ← powBodyFloat16 logs (FP.abs x) (.f32 y)
    return .f16 (FP.copysign value s)
  | .f32 x =>
    let n32 := ops.clamp32 n
    if n32.val == 0 then return .f32 (FP.ofInt .f32 1)
    if usePowerBySquaring n32.val then
      return .f32 (← powBodyI32 x n32)
    let s := if x.signbit && ops.isOdd n then FP.ofInt .f32 (-1) else FP.ofInt .f32 1
    let y := FP.ofInt .f64 n32.val
    let value ← powBodyFloat32 logs (FP.abs x) (.f64 y)
    return .f32 (FP.copysign value s)

/--
Julia source: base/special/pow.jl:105-107 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function pow_body(x::T, y) where T <: Union{Float16, Float32}
    return T(exp2(log2(abs(widen(x))) * y))
end
```
-/
def powBodyFloat (logs : NarrowLogCalls) (x : NarrowFloat) (y : PowerExponent) : Jl NarrowFloat :=
  powBodyFloatNarrow logs x y

/--
Julia source: base/special/pow.jl:109-114 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function pow_body(x::Union{Float16, Float32}, n::Int32)
    n == -2 && return (i=inv(x); i*i)
    n == 3 && return x*x*x #keep compatibility with literal_pow
    n < 0 && return oftype(x, Base.power_by_squaring(inv(widen(x)), -n))
    return oftype(x, Base.power_by_squaring(widen(x), n))
end
```
-/
def powBodyINarrow (x : NarrowFloat) (n : JInt .i32) : Jl NarrowFloat := do
  match x with
  | .f16 x => return .f16 (← powBodyI16 x n)
  | .f32 x => return .f32 (← powBodyI32 x n)




end JuliaLean.base.special.pow

namespace JuliaLean.MathCov.FloatFuncs

open JuliaLean JuliaLean.Float JuliaLean.Promotion JuliaLean.MathCov.FP

variable {T : FTy}

/-- `oftype(fx, base)^digits` and `oftype(fx, base)^oftype(fx, digits/2)` for
`T = Float16, Float32` (`base/special/pow.jl`) and `Float64` (`MathFuncs`). -/
def powI (b : FV T) (n : Int) : FV T :=
  match T, b with
  | .f64, b => of64 (MathFuncs.powFI (to64 b) n)
  | _, b => Special.powFI b n
def powF (b y : FV T) : Jl (FV T) :=
  match T, b, y with
  | .f64, b, y => do return of64 (← MathFuncs.powFF (to64 b) (to64 y))
  | _, b, y => Special.powFF b y

end JuliaLean.MathCov.FloatFuncs

namespace JuliaLean.MathFuncs

open JuliaLean.Float

/-- `pow_body(x::Float32, n::Int32)`; `base/special/pow.jl:109-115`. -/
def powBody32I (x : F32) (n : Int) : F32 :=
  if n == -2 then let i := inv32 x; mul32 i i
  else if n == 3 then mul32 (mul32 x x) x
  else if n < 0 then toF32 (powerBySquaring (F64.div F64.one (ofF32 x)) (-n).toNat)
  else toF32 (powerBySquaring (ofF32 x) n.toNat)

/-- `pow_body(x::Float32, y::Float64) = Float32(exp2(log2(abs(widen(x))) * y))`;
`base/special/pow.jl:105-107`. -/
def powBody32F (x : F32) (y : F64) : F32 :=
  match log2 (F64.abs (ofF32 x)) with
  | .ok l => toF32 (exp2 (F64.mul l y))
  | .error _ => toF32 F64.nan

/-- `^(x::Float32, n::Integer)`; `base/special/pow.jl:80-88`. -/
def pow32I (x : F32) (n : Int) : F32 :=
  let n32 := max (-2^31) (min (2^31 - 1) n)
  if n32 == 0 then toF32 F64.one
  else if usePowerBySquaring n32 then powBody32I x n32
  else
    let s := if F32.signbit x && n % 2 != 0 then toF32 (F64.neg F64.one) else toF32 F64.one
    let ax : F32 := BitVec.ofNat 32 (x.toNat % 2^31)
    copysign32 (powBody32F ax (F64.ofInt n32)) s

end JuliaLean.MathFuncs
