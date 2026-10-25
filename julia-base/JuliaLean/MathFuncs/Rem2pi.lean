import JuliaLean.MathFuncs.RemPio2

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

/-- `Float64(pi, RoundDown)`, the largest Float64 below π (its `nextfloat` lies above π);
`base/irrationals.jl:101-106`, `base/mathconstants.jl:13`. -/
def piRoundDown : F64 := lit 0x400921fb54442d18

/-- `x < pi` for a Float64 `x` and the Irrational π, decided exactly as
`x <= Float64(pi, RoundDown)`; `base/irrationals.jl:128`. -/
def ltPi (x : F64) : Bool := F64.le x piRoundDown

/-- `add22condh(xh, xl, yh, yl)`: high part of Dekker's double-double sum;
`base/math.jl:1176-1186`. -/
def add22condh (xh xl yh yl : F64) : F64 :=
  let r := F64.add xh yh
  let s :=
    if F64.lt (F64.abs yh) (F64.abs xh) then
      F64.add (F64.add (F64.add (F64.sub xh r) yh) yl) xl
    else
      F64.add (F64.add (F64.add (F64.sub yh r) xh) xl) yl
  F64.add r s

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

/-- `mod2pi(x) = rem2pi(x, RoundDown)`; `base/math.jl:1241`. -/
def mod2pi (x : F64) : F64 := rem2piDown x

end JuliaLean.MathFuncs
