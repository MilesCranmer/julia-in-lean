import JuliaLean.FloatIntCov.Float
import JuliaLean.MathFuncs.Prelude

/-!
Arithmetic on the three IEEE formats for the `base/math.jl`, `base/special/*.jl`,
`base/floatfuncs.jl` and `base/rounding.jl` coverage models (Julia master `bbfa0ce4150`).

Values are `Promotion.FV T` bit patterns. Every operation on a `Float32` or `Float16`
operand widens exactly to binary64, applies the shared `JuliaLean.Float.F64` intrinsic,
and rounds back once (`Fl.convert`). For `+`, `-`, `*`, `/` and `sqrt` this equals the
correctly rounded operation of the narrow format, because binary64 has more than
`2p+2` significand bits for `p = 24` and `p = 11` (Julia evaluates `Float16` arithmetic in
`Float32` and rounds again, which is equally exact since `24 ≥ 2*11+2`). `fma` of narrow
operands rounds the exact rational once. `muladd` is fused in the MathCov call sites except
for the compensated `cospi` product, where Julia's optimized code keeps separate operations.
-/

namespace JuliaLean.MathCov

open JuliaLean JuliaLean.Float JuliaLean.Promotion

namespace FP

variable {T : FTy}

/-- `Float64(x)`, the exact `fpext`; `base/float.jl:346`. -/
def toD (x : FV T) : F64 := Fl.toF64 (Fl.convert x : Fl double)

/-- `T(y::Float64)`, the `fptrunc` rounding; `base/float.jl:343`. -/
def ofD (y : F64) : FV T := Fl.convert (Fl.ofF64 y)

/-- The shared binary64 model's view of a `Float64` value, and back. -/
def of64 (y : F64) : FV .f64 := Fl.ofF64 y
def to64 (x : FV .f64) : F64 := Fl.toF64 x

/-- Conversion between formats, `S(x::T)`; `base/float.jl:342-349`. -/
def conv {S : FTy} (x : FV T) : FV S := Fl.convert x

/-- A literal of the format given by its bit pattern. -/
def lit (T : FTy) (u : Nat) : FV T := Fl.ofBits u

def add (x y : FV T) : FV T := ofD (F64.add (toD x) (toD y))
def sub (x y : FV T) : FV T := ofD (F64.sub (toD x) (toD y))
def mul (x y : FV T) : FV T := ofD (F64.mul (toD x) (toD y))
def div (x y : FV T) : FV T := ofD (F64.div (toD x) (toD y))

/-- `sqrt_llvm`: correctly rounded square root, NaN for negative arguments;
`base/math.jl:631`. -/
def sqrt64 (y : F64) : F64 := match F64.sqrt y with
  | .ok r => r
  | .error _ => F64.nan

def sqrtLlvm (x : FV T) : FV T := ofD (sqrt64 (toD x))

/-- `fma_float` (hardware fused multiply-add) with one rounding of the exact
`x*y+z`; `base/floatfuncs.jl:464-466`. Exact zeros and nonfinite operands follow the
binary64 rules, which are the IEEE rules of every format. -/
def fma (x y z : FV T) : FV T :=
  let wide : FV T := ofD (F64.fma (toD x) (toD y) (toD z))
  if T = .f64 then wide
  else if x.isfinite && y.isfinite && z.isfinite then
    let a := x.toRat
    let b := y.toRat
    let c := z.toRat
    let n := a.1 * b.1 * (c.2 : Int) + c.1 * ((a.2 * b.2 : Nat) : Int)
    if n == 0 then wide else Fl.roundRat n (a.2 * b.2 * c.2) false
  else wide

/-- `muladd_float`, fused at the ordinary MathCov call sites; `base/float.jl:492`. -/
def muladd (x y z : FV T) : FV T := fma x y z

def neg (x : FV T) : FV T := Fl.neg x
def abs (x : FV T) : FV T := Fl.ofBits x.magnitude
def signbit (x : FV T) : Bool := x.signbit
def isnan (x : FV T) : Bool := x.isnan
def isinf (x : FV T) : Bool := x.isinf
def isfinite (x : FV T) : Bool := x.isfinite
def iszero (x : FV T) : Bool := x.iszero
def lt (x y : FV T) : Bool := Fl.lt x y
def le (x y : FV T) : Bool := Fl.le x y
def eq (x y : FV T) : Bool := Fl.eq x y
def isequal (x y : FV T) : Bool := Fl.isequal x y

/-- `copysign_float`: magnitude of `x`, sign bit of `y`; `base/floatfuncs.jl:5-6`. -/
def copysign (x y : FV T) : FV T :=
  Fl.ofBits (x.magnitude + if y.signbit then 2 ^ (T.fmt.eb + T.fmt.sb) else 0)

/-- `flipsign`: xor with the sign bit of `y`; `base/floatfuncs.jl:10-11`. -/
def flipsign (x y : FV T) : FV T := if y.signbit then Fl.neg x else x

def zero (T : FTy) (neg : Bool := false) : FV T := Fl.zero neg
def inf (T : FTy) (neg : Bool := false) : FV T := Fl.inf neg
def nan (T : FTy) : FV T := Fl.nan
/-- `T(n)` for a small integer literal `n`. -/
def ofInt (T : FTy) (n : Int) : FV T := Fl.ofInt n

/-- Integer rounding of a float in its own type (`trunc_llvm`, `floor_llvm`, `ceil_llvm`,
`rint_llvm`); the binary64 rounding of the exact widening is exact. `base/float.jl:458-461`. -/
def roundI (x : FV T) (mode : Rounding := .RoundNearest) : FV T := ofD (F64.round (toD x) mode)
def trunc (x : FV T) : FV T := roundI x .RoundToZero
def floor (x : FV T) : FV T := roundI x .RoundDown
def ceil (x : FV T) : FV T := roundI x .RoundUp

/-- `eps(x)` for finite `x`: the gap to the next float of larger magnitude;
`base/float.jl:1089-1099`. -/
def epsOf (x : FV T) : FV T :=
  abs (sub (FloatIntCov.Float.nextFloat T (abs x)) (abs x))

/-- `eps(T)`; `base/float.jl:1080-1082`. -/
def epsT (T : FTy) : FV T := FloatIntCov.Float.typeEps T
def floatminT (T : FTy) : FV T := FloatIntCov.Float.floatMin T
def floatmaxT (T : FTy) : FV T := Fl.floatmax
def nextfloat (x : FV T) (n : Int := 1) : FV T := FloatIntCov.Float.nextFloat T x n
def prevfloat (x : FV T) (n : Int := 1) : FV T := FloatIntCov.Float.prevFloat T x n

/-- Exact value of a finite float as a rational `(num, den)`. -/
def val (x : FV T) : Int × Nat := x.toRat

/-- `unsafe_trunc(t, x)`. -/
def unsafeTrunc (t : IntTy) (x : FV T) : JInt t := x.unsafeTrunc t

/-- `reinterpret(Unsigned, x)` as a natural number. -/
def bits (x : FV T) : Nat := x.toBits

end FP

end JuliaLean.MathCov
