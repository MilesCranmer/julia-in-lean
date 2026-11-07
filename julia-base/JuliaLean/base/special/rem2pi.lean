import JuliaLean.base.float
import JuliaLean.base.math
import JuliaLean.base.special.rem_pio2
import JuliaLean.base.irrationals

/-!
Remainder after division by 2π for Float64, `base/special/rem2pi.jl` and
`base/math.jl`, Julia master `bbfa0ce4150`.
-/

namespace JuliaLean.MathFuncs

open JuliaLean.Float

/-- `pi1o2_h`, π/2 rounded to Float64; `base/special/rem2pi.jl:2`. -/
def pi1o2H : F64 := lit 0x3ff921fb54442d18
/-- `pi1o2_l`, π/2 - `pi1o2_h` rounded to Float64; `base/special/rem2pi.jl:3`. -/
def pi1o2L : F64 := lit 0x3c91a62633145c07
/-- `pi2o2_h`, π rounded to Float64; `base/special/rem2pi.jl:5`. -/
def pi2o2H : F64 := lit 0x400921fb54442d18
/-- `pi2o2_l`, π - `pi2o2_h` rounded to Float64; `base/special/rem2pi.jl:6`. -/
def pi2o2L : F64 := lit 0x3ca1a62633145c07
/-- `pi3o2_h`, 3π/2 rounded to Float64; `base/special/rem2pi.jl:8`. -/
def pi3o2H : F64 := lit 0x4012d97c7f3321d2
/-- `pi3o2_l`, 3π/2 - `pi3o2_h` rounded to Float64; `base/special/rem2pi.jl:9`. -/
def pi3o2L : F64 := lit 0x3caa79394c9e8a0a
/-- `pi4o2_h`, 2π rounded to Float64; `base/special/rem2pi.jl:11`. -/
def pi4o2H : F64 := lit 0x401921fb54442d18
/-- `pi4o2_l`, 2π - `pi4o2_h` rounded to Float64; `base/special/rem2pi.jl:12`. -/
def pi4o2L : F64 := lit 0x3cb1a62633145c07

/-- `iseven(n)` for an `Int`: `rem(n, 2) == 0`; `base/int.jl:181`. -/
private def isevenInt (n : Int) : Bool := n % 2 == 0

/-- `n & 2 == 2` for an `Int`, testing bit 1 of the two's-complement encoding;
`base/int.jl:407`. -/
private def bit2 (n : Int) : Bool := (n >>> 1) % 2 == 1

/-- `rem2pi(x::Float64, ::RoundingMode{:Nearest})`; `base/special/rem2pi.jl:14-39`. -/
def rem2piNearest (x : F64) : F64 :=
  if F64.isnan x then x
  else if F64.isinf x then F64.nan
  else if ltPi (F64.abs x) then x
  else
    let (n, hi, lo) := remPio2Kernel x
    if isevenInt n then
      if bit2 n then
        if F64.le hi F64.zero then add22condh hi lo pi2o2H pi2o2L
        else add22condh hi lo (F64.neg pi2o2H) (F64.neg pi2o2L)
      else F64.add hi lo
    else
      if bit2 n then add22condh hi lo (F64.neg pi1o2H) (F64.neg pi1o2L)
      else add22condh hi lo pi1o2H pi1o2L

/-- `rem2pi(x::Float64, ::RoundingMode{:ToZero})`, with `2*Float64(pi,RoundDown)` as the
Int-times-Float64 product; `base/special/rem2pi.jl:40-67`. -/
def rem2piToZero (x : F64) : F64 :=
  if F64.isnan x then x
  else if F64.isinf x then F64.nan
  else
    let ax := F64.abs x
    if F64.le ax (F64.mul (F64.ofInt 2) piRoundDown) then x
    else
      let (n, hi, lo) := remPio2Kernel ax
      let z :=
        if isevenInt n then
          if bit2 n then add22condh hi lo pi2o2H pi2o2L
          else if F64.lt F64.zero hi then F64.add hi lo
          else add22condh hi lo pi4o2H pi4o2L
        else
          if bit2 n then add22condh hi lo pi3o2H pi3o2L
          else add22condh hi lo pi1o2H pi1o2L
      copysign z x

/-- `rem2pi(x::Float64, ::RoundingMode{:Down})`; `base/special/rem2pi.jl:68-99`. -/
def rem2piDown (x : F64) : F64 :=
  if F64.isnan x then x
  else if F64.isinf x then F64.nan
  else if F64.lt x pi4o2H && F64.le F64.zero x then x
  else if F64.lt x pi4o2H && F64.lt (F64.neg pi4o2H) x then
    add22condh x F64.zero pi4o2H pi4o2L
  else
    let (n, hi, lo) := remPio2Kernel x
    if isevenInt n then
      if bit2 n then add22condh hi lo pi2o2H pi2o2L
      else if F64.lt F64.zero hi then F64.add hi lo
      else add22condh hi lo pi4o2H pi4o2L
    else
      if bit2 n then add22condh hi lo pi3o2H pi3o2L
      else add22condh hi lo pi1o2H pi1o2L

/-- `rem2pi(x::Float64, ::RoundingMode{:Up})`; `base/special/rem2pi.jl:100-131`. -/
def rem2piUp (x : F64) : F64 :=
  if F64.isnan x then x
  else if F64.isinf x then F64.nan
  else if F64.lt (F64.neg pi4o2H) x && F64.le x F64.zero then x
  else if F64.lt (F64.neg pi4o2H) x && F64.lt x pi4o2H then
    add22condh x F64.zero (F64.neg pi4o2H) (F64.neg pi4o2L)
  else
    let (n, hi, lo) := remPio2Kernel x
    if isevenInt n then
      if bit2 n then add22condh hi lo (F64.neg pi2o2H) (F64.neg pi2o2L)
      else if F64.lt hi F64.zero then F64.add hi lo
      else add22condh hi lo (F64.neg pi4o2H) (F64.neg pi4o2L)
    else
      if bit2 n then add22condh hi lo (F64.neg pi1o2H) (F64.neg pi1o2L)
      else add22condh hi lo (F64.neg pi3o2H) (F64.neg pi3o2L)

/-- `rem2pi(x::Float64, r)`: the four Float64 methods; `RoundNearestTiesAway` has no
method; `base/special/rem2pi.jl:14-131`. -/
def rem2pi (x : F64) (m : Rounding) : Jl F64 :=
  match m with
  | .RoundNearest => .ok (rem2piNearest x)
  | .RoundToZero => .ok (rem2piToZero x)
  | .RoundDown => .ok (rem2piDown x)
  | .RoundUp => .ok (rem2piUp x)
  | .RoundNearestTiesAway => .error (.methodError "rem2pi")

end JuliaLean.MathFuncs

namespace JuliaLean.MathCov.Special

open JuliaLean JuliaLean.Float JuliaLean.Promotion JuliaLean.MathCov.FP JuliaLean.MathCov.C

/-- The four `rem2pi(x::Float64, r)` methods; `base/special/rem2pi.jl:14-131`. -/
def rem2pi64 (x : FV .f64) (r : FloatFuncs.Mode) : FV .f64 :=
  let f := Fl.toF64 x
  Fl.ofF64 (match r with
    | .Nearest => MathFuncs.rem2piNearest f
    | .ToZero => MathFuncs.rem2piToZero f
    | .Down => MathFuncs.rem2piDown f
    | _ => MathFuncs.rem2piUp f)

/-- `rem2pi(x::Float32, r)` and `rem2pi(x::Float16, r)`: round the `Float64` result;
`base/special/rem2pi.jl:133-134`. -/
def rem2piNarrow {T : FTy} (x : FV T) (r : FloatFuncs.Mode) : FV T := conv (rem2pi64 (conv x) r)

/-- `rem2pi(x::Int32, r) = rem2pi(Float64(x), r)`; `base/special/rem2pi.jl:135`. -/
def rem2piInt32 (x : JInt .i32) (r : FloatFuncs.Mode) : FV .f64 := rem2pi64 (ofInt .f64 x.val) r

/-- `rem2pi(x::Integer, r)`: `fx = float(x)`, which must equal `x`;
`base/special/rem2pi.jl:138-142`. -/
def rem2piInteger (x : Int) (r : FloatFuncs.Mode) : Jl (FV .f64) :=
  let fx : FV .f64 := ofInt .f64 x
  if fx.isfinite && fx.toRat.2 == 1 && fx.toRat.1 == x then .ok (rem2pi64 fx r)
  else .error (.argumentError "argument to rem2pi is too large")

end JuliaLean.MathCov.Special

/-!
# Model of `base/special/rem2pi.jl`

The four Float64 methods call the source-mirrored `remPio2Kernel` and `base.math.add22condh`.
The Irrational-π comparison and directed `Float64(pi, RoundDown)` conversion stay explicit inputs.
The Float32, Float16, and Int32 methods pass Float64 dispatch through an interface; the generic
Integer fallback keeps its `float`, equality, and `rem2pi` callees generic. -/

namespace JuliaLean.base.special.rem2pi

open JuliaLean JuliaLean.Promotion

abbrev F64 := JuliaLean.base.float.FV .f64
abbrev Mode := JuliaLean.base.float.RoundingMode

/--
Julia source: base/special/rem2pi.jl:1-3 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# multiples of pi/2, as double-double (ie with "tail")
const pi1o2_h  = 1.5707963267948966     # convert(Float64, pi * BigFloat(1/2))
const pi1o2_l  = 6.123233995736766e-17  # convert(Float64, pi * BigFloat(1/2) - pi1o2_h)
```
-/
def pi1o2 : F64 × F64 :=
  (Fl.ofBits 0x3ff921fb54442d18, Fl.ofBits 0x3c91a62633145c07)

/--
Julia source: base/special/rem2pi.jl:4-6 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

const pi2o2_h  = 3.141592653589793      # convert(Float64, pi * BigFloat(1))
const pi2o2_l  = 1.2246467991473532e-16 # convert(Float64, pi * BigFloat(1) - pi2o2_h)
```
-/
def pi2o2 : F64 × F64 :=
  (Fl.ofBits 0x400921fb54442d18, Fl.ofBits 0x3ca1a62633145c07)

/--
Julia source: base/special/rem2pi.jl:7-9 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

const pi3o2_h  = 4.71238898038469       # convert(Float64, pi * BigFloat(3/2))
const pi3o2_l  = 1.8369701987210297e-16 # convert(Float64, pi * BigFloat(3/2) - pi3o2_h)
```
-/
def pi3o2 : F64 × F64 :=
  (Fl.ofBits 0x4012d97c7f3321d2, Fl.ofBits 0x3caa79394c9e8a0a)

/--
Julia source: base/special/rem2pi.jl:10-13 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

const pi4o2_h  = 6.283185307179586      # convert(Float64, pi * BigFloat(2))
const pi4o2_l  = 2.4492935982947064e-16 # convert(Float64, pi * BigFloat(2) - pi4o2_h)

```
-/
def pi4o2 : F64 × F64 :=
  (Fl.ofBits 0x401921fb54442d18, Fl.ofBits 0x3cb1a62633145c07)

private def isevenInt (n : JInt .i64) : Bool := n.val % 2 == 0

private def bit2 (n : JInt .i64) : Bool :=
  (JuliaLean.base.int.band n (JInt.lit .i64 2)).val == 2

/--
Julia source: base/special/rem2pi.jl:14-39 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rem2pi(x::Float64, ::RoundingMode{:Nearest})
    isnan(x) && return x
    isinf(x) && return NaN

    abs(x) < pi && return x

    n,y = rem_pio2_kernel(x)

    if iseven(n)
        if n & 2 == 2 # n % 4 == 2: add/subtract pi
            if y.hi <= 0
                return add22condh(y.hi,y.lo,pi2o2_h,pi2o2_l)
            else
                return add22condh(y.hi,y.lo,-pi2o2_h,-pi2o2_l)
            end
        else          # n % 4 == 0: add 0
            return y.hi+y.lo
        end
    else
        if n & 2 == 2 # n % 4 == 3: subtract pi/2
            return add22condh(y.hi,y.lo,-pi1o2_h,-pi1o2_l)
        else          # n % 4 == 1: add pi/2
            return add22condh(y.hi,y.lo,pi1o2_h,pi1o2_l)
        end
    end
end
```
-/
def rem2piNearest (ltPi : F64 → Bool) (x : F64) : F64 := Id.run do
  if JuliaLean.base.float.isnan_IEEEFloat x then return x
  if JuliaLean.base.float.isinf_IEEEFloat x then return JuliaLean.base.float.nan_float .f64
  if ltPi (JuliaLean.base.float.abs_float x) then return x
  let (n, y) := JuliaLean.base.special.rem_pio2.remPio2Kernel x
  if isevenInt n then
    if bit2 n then
      if JuliaLean.base.float.le_float (T := .f64) y.hi (JuliaLean.base.float.zero_float .f64) then
        return JuliaLean.base.math.add22condh y.hi y.lo pi2o2.1 pi2o2.2
      else
        return JuliaLean.base.math.add22condh y.hi y.lo
          (JuliaLean.base.float.neg_float pi2o2.1) (JuliaLean.base.float.neg_float pi2o2.2)
    else
      return JuliaLean.base.float.add_float (T := .f64) y.hi y.lo
  else if bit2 n then
    return JuliaLean.base.math.add22condh y.hi y.lo
      (JuliaLean.base.float.neg_float pi1o2.1) (JuliaLean.base.float.neg_float pi1o2.2)
  else
    return JuliaLean.base.math.add22condh y.hi y.lo pi1o2.1 pi1o2.2

/--
Julia source: base/special/rem2pi.jl:40-67 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rem2pi(x::Float64, ::RoundingMode{:ToZero})
    isnan(x) && return x
    isinf(x) && return NaN

    ax = abs(x)
    ax <= 2*Float64(pi,RoundDown) && return x

    n,y = rem_pio2_kernel(ax)

    if iseven(n)
        if n & 2 == 2 # n % 4 == 2: add pi
            z = add22condh(y.hi,y.lo,pi2o2_h,pi2o2_l)
        else          # n % 4 == 0: add 0 or 2pi
            if y.hi > 0
                z = y.hi+y.lo
            else      # negative: add 2pi
                z = add22condh(y.hi,y.lo,pi4o2_h,pi4o2_l)
            end
        end
    else
        if n & 2 == 2 # n % 4 == 3: add 3pi/2
            z = add22condh(y.hi,y.lo,pi3o2_h,pi3o2_l)
        else          # n % 4 == 1: add pi/2
            z = add22condh(y.hi,y.lo,pi1o2_h,pi1o2_l)
        end
    end
    copysign(z,x)
end
```
-/
def rem2piToZero (piRoundDown : F64) (x : F64) : F64 := Id.run do
  if JuliaLean.base.float.isnan_IEEEFloat x then return x
  if JuliaLean.base.float.isinf_IEEEFloat x then return JuliaLean.base.float.nan_float .f64
  let ax := JuliaLean.base.float.abs_float x
  let two := JuliaLean.base.float.floatOfInt .f64 (JInt.lit .i64 2)
  if JuliaLean.base.float.le_float ax (JuliaLean.base.float.mul_float two piRoundDown) then return x
  let (n, y) := JuliaLean.base.special.rem_pio2.remPio2Kernel ax
  let z :=
    if isevenInt n then
      if bit2 n then
        JuliaLean.base.math.add22condh y.hi y.lo pi2o2.1 pi2o2.2
      else if JuliaLean.base.float.lt_float (T := .f64) (JuliaLean.base.float.zero_float .f64) y.hi then
        JuliaLean.base.float.add_float (T := .f64) y.hi y.lo
      else
        JuliaLean.base.math.add22condh y.hi y.lo pi4o2.1 pi4o2.2
    else if bit2 n then
      JuliaLean.base.math.add22condh y.hi y.lo pi3o2.1 pi3o2.2
    else
      JuliaLean.base.math.add22condh y.hi y.lo pi1o2.1 pi1o2.2
  return JuliaLean.base.float.copysign_float z x

/--
Julia source: base/special/rem2pi.jl:68-99 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rem2pi(x::Float64, ::RoundingMode{:Down})
    isnan(x) && return x
    isinf(x) && return NaN

    if x < pi4o2_h
        if x >= 0
            return x
        elseif x > -pi4o2_h
            return add22condh(x,0.0,pi4o2_h,pi4o2_l)
        end
    end

    n,y = rem_pio2_kernel(x)

    if iseven(n)
        if n & 2 == 2 # n % 4 == 2: add pi
            return add22condh(y.hi,y.lo,pi2o2_h,pi2o2_l)
        else          # n % 4 == 0: add 0 or 2pi
            if y.hi > 0
                return y.hi+y.lo
            else      # negative: add 2pi
                return add22condh(y.hi,y.lo,pi4o2_h,pi4o2_l)
            end
        end
    else
        if n & 2 == 2 # n % 4 == 3: add 3pi/2
            return add22condh(y.hi,y.lo,pi3o2_h,pi3o2_l)
        else          # n % 4 == 1: add pi/2
            return add22condh(y.hi,y.lo,pi1o2_h,pi1o2_l)
        end
    end
end
```
-/
def rem2piDown (x : F64) : F64 := Id.run do
  if JuliaLean.base.float.isnan_IEEEFloat x then return x
  if JuliaLean.base.float.isinf_IEEEFloat x then return JuliaLean.base.float.nan_float .f64
  if JuliaLean.base.float.lt_float x pi4o2.1 then
    if JuliaLean.base.float.le_float (JuliaLean.base.float.zero_float .f64) x then
      return x
    else if JuliaLean.base.float.lt_float (JuliaLean.base.float.neg_float pi4o2.1) x then
      return JuliaLean.base.math.add22condh x (JuliaLean.base.float.zero_float .f64)
        pi4o2.1 pi4o2.2
  let (n, y) := JuliaLean.base.special.rem_pio2.remPio2Kernel x
  if isevenInt n then
    if bit2 n then
      return JuliaLean.base.math.add22condh y.hi y.lo pi2o2.1 pi2o2.2
    else if JuliaLean.base.float.lt_float (T := .f64) (JuliaLean.base.float.zero_float .f64) y.hi then
      return JuliaLean.base.float.add_float (T := .f64) y.hi y.lo
    else
      return JuliaLean.base.math.add22condh y.hi y.lo pi4o2.1 pi4o2.2
  else if bit2 n then
    return JuliaLean.base.math.add22condh y.hi y.lo pi3o2.1 pi3o2.2
  else
    return JuliaLean.base.math.add22condh y.hi y.lo pi1o2.1 pi1o2.2

/--
Julia source: base/special/rem2pi.jl:100-132 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rem2pi(x::Float64, ::RoundingMode{:Up})
    isnan(x) && return x
    isinf(x) && return NaN

    if x > -pi4o2_h
        if x <= 0
            return x
        elseif x < pi4o2_h
            return add22condh(x,0.0,-pi4o2_h,-pi4o2_l)
        end
    end

    n,y = rem_pio2_kernel(x)

    if iseven(n)
        if n & 2 == 2 # n % 4 == 2: sub pi
            return add22condh(y.hi,y.lo,-pi2o2_h,-pi2o2_l)
        else          # n % 4 == 0: sub 0 or 2pi
            if y.hi < 0
                return y.hi+y.lo
            else      # positive: sub 2pi
                return add22condh(y.hi,y.lo,-pi4o2_h,-pi4o2_l)
            end
        end
    else
        if n & 2 == 2 # n % 4 == 3: sub pi/2
            return add22condh(y.hi,y.lo,-pi1o2_h,-pi1o2_l)
        else          # n % 4 == 1: sub 3pi/2
            return add22condh(y.hi,y.lo,-pi3o2_h,-pi3o2_l)
        end
    end
end

```
-/
def rem2piUp (x : F64) : F64 := Id.run do
  if JuliaLean.base.float.isnan_IEEEFloat x then return x
  if JuliaLean.base.float.isinf_IEEEFloat x then return JuliaLean.base.float.nan_float .f64
  if JuliaLean.base.float.lt_float (JuliaLean.base.float.neg_float pi4o2.1) x then
    if JuliaLean.base.float.le_float x (JuliaLean.base.float.zero_float .f64) then
      return x
    else if JuliaLean.base.float.lt_float x pi4o2.1 then
      return JuliaLean.base.math.add22condh x (JuliaLean.base.float.zero_float .f64)
        (JuliaLean.base.float.neg_float pi4o2.1) (JuliaLean.base.float.neg_float pi4o2.2)
  let (n, y) := JuliaLean.base.special.rem_pio2.remPio2Kernel x
  if isevenInt n then
    if bit2 n then
      return JuliaLean.base.math.add22condh y.hi y.lo
        (JuliaLean.base.float.neg_float pi2o2.1) (JuliaLean.base.float.neg_float pi2o2.2)
    else if JuliaLean.base.float.lt_float (T := .f64) y.hi (JuliaLean.base.float.zero_float .f64) then
      return JuliaLean.base.float.add_float (T := .f64) y.hi y.lo
    else
      return JuliaLean.base.math.add22condh y.hi y.lo
        (JuliaLean.base.float.neg_float pi4o2.1) (JuliaLean.base.float.neg_float pi4o2.2)
  else if bit2 n then
    return JuliaLean.base.math.add22condh y.hi y.lo
      (JuliaLean.base.float.neg_float pi1o2.1) (JuliaLean.base.float.neg_float pi1o2.2)
  else
    return JuliaLean.base.math.add22condh y.hi y.lo
      (JuliaLean.base.float.neg_float pi3o2.1) (JuliaLean.base.float.neg_float pi3o2.2)

/--
Julia source: base/special/rem2pi.jl:133-133 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rem2pi(x::Float32, r::RoundingMode) = Float32(rem2pi(Float64(x), r))
```
-/
def rem2piFloat32 (rem2pi64 : F64 → Mode → Jl F64)
    (x : JuliaLean.base.float.FV .f32) (r : Mode) : Jl (JuliaLean.base.float.FV .f32) := do
  let result ← rem2pi64 (JuliaLean.base.float.convertFloat .f64 x) r
  pure (JuliaLean.base.float.convertFloat .f32 result)

/--
Julia source: base/special/rem2pi.jl:134-134 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rem2pi(x::Float16, r::RoundingMode) = Float16(rem2pi(Float64(x), r))
```
-/
def rem2piFloat16 (rem2pi64 : F64 → Mode → Jl F64)
    (x : JuliaLean.base.float.FV .f16) (r : Mode) : Jl (JuliaLean.base.float.FV .f16) := do
  let result ← rem2pi64 (JuliaLean.base.float.convertFloat .f64 x) r
  pure (JuliaLean.base.float.convertFloat .f16 result)

/--
Julia source: base/special/rem2pi.jl:135-136 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rem2pi(x::Int32, r::RoundingMode) = rem2pi(Float64(x), r)

```
-/
def rem2piInt32 (rem2pi64 : F64 → Mode → Jl F64)
    (x : JInt .i32) (r : Mode) : Jl F64 :=
  rem2pi64 (JuliaLean.base.float.floatOfInt .f64 x) r

/--
Julia source: base/special/rem2pi.jl:137-142 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# general fallback
function rem2pi(x::Integer, r::RoundingMode)
    fx = float(x)
    fx == x || throw(ArgumentError(LazyString(typeof(x), " argument to rem2pi is too large: ", x)))
    rem2pi(fx, r)
end
```
-/
def rem2piInteger {I F R : Type}
    (float : I → Jl F) (equal : F → I → Jl Bool)
    (rem2pi : F → Mode → Jl R) (x : I) (r : Mode) : Jl R := do
  let fx ← float x
  let isExact ← equal fx x
  if isExact then
    rem2pi fx r
  else
    .error (.argumentError "argument to rem2pi is too large")

end JuliaLean.base.special.rem2pi
