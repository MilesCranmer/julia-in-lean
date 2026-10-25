import JuliaLean.MathFuncs.Pow
import JuliaLean.MathFuncs.Float32

/-!
`prevpow(a::Float32, x::Float64)` from `base/intfuncs.jl:694-713` (master `bbfa0ce4150`),
with the Float32 power `^(::Float32, ::Integer)` of `base/special/pow.jl:80-88,105-115` and
the generic `power_by_squaring` of `base/intfuncs.jl:399-443` on Float64. Float32 `*` and
`inv` are computed as the Float64 operation followed by `Float32(...)`; with 53 ≥ 2·24+2
bits this double rounding equals the correctly rounded binary32 operation.
-/

namespace JuliaLean.MathFuncs

open JuliaLean.Float

/-- Binary32 multiplication, `base/float.jl:489`. -/
def mul32 (x y : F32) : F32 := toF32 (F64.mul (ofF32 x) (ofF32 y))

/-- Binary32 `inv(x) = one(x)/x`, `base/number.jl:269` and `base/float.jl:490`. -/
def inv32 (x : F32) : F32 := toF32 (F64.div F64.one (ofF32 x))

/-- Number of trailing zero bits of a positive natural, with fuel. -/
private def tz : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, n => if n % 2 == 1 then 0 else 1 + tz k (n / 2)

/-- Square `x` `t` times. -/
private def squareTimes (x : F64) : Nat → F64
  | 0 => x
  | t + 1 => squareTimes (F64.mul x x) t

/-- The outer `while p > 0` loop of `power_by_squaring`; `base/intfuncs.jl:432-439`. -/
private def pbsLoop : Nat → F64 → F64 → Nat → F64
  | 0, _, y, _ => y
  | k + 1, x, y, p =>
    if p == 0 then y
    else
      let t := tz 64 p + 1
      let x := squareTimes x t
      pbsLoop k x (F64.mul y x) (p >>> t)

/-- `power_by_squaring(x::Float64, p)` for `p ≥ 1` with `mul = *`;
`base/intfuncs.jl:399-443`. -/
def powerBySquaring (x : F64) (p : Nat) : F64 :=
  if p == 1 then x
  else if p == 0 then F64.one
  else if p == 2 then F64.mul x x
  else
    let t := tz 64 p + 1
    let p := p >>> t
    let x := if t - 1 > 0 then squareTimes (F64.mul x x) (t - 2) else x
    pbsLoop 64 x x p

/-- `pow_body(x::Float32, n::Int32)`; `base/special/pow.jl:109-115`. -/
def powBody32I (x : F32) (n : Int) : F32 :=
  if n == -2 then let i := inv32 x; mul32 i i
  else if n == 3 then mul32 (mul32 x x) x
  else if n < 0 then toF32 (powerBySquaring (F64.div F64.one (ofF32 x)) (-n).toNat)
  else toF32 (powerBySquaring (ofF32 x) n.toNat)

/-- Float32 sign-copy intrinsic; `base/floatfuncs.jl:6`. -/
def copysign32 (x y : F32) : F32 :=
  BitVec.ofNat 32 (x.toNat % 2^31 + (if F32.signbit y then 2^31 else 0))

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

/-- `prevpow(a::Float32, x::Float64)`: `log(a, x)` promotes to Float64 and is
`log(x)/log(a)` (`base/math.jl:259,304`); `floor(Integer, v)` is `floor(Int, v)`
(`base/float.jl:456`); comparisons promote Float32 to Float64 (`base/float.jl:479,617`);
`hastypemax(Float32)` holds with `typemax(Float32) == Inf32`; `base/intfuncs.jl:694-713`. -/
def prevpow32 (a : F32) (x : F64) : Jl F32 := do
  let af := ofF32 a
  if F64.lt x F64.one then throw (.domainError "prevpow")
  if F64.le af F64.one then throw (.domainError "prevpow")
  let lx ← log x
  let la ← log af
  let n ← F64.floorInt .i64 (F64.div lx la)
  let p := pow32I a n.val
  if F64.lt F64.inf x then throw (.domainError "prevpow")
  let wp := pow32I a (n.val + 1)
  if F64.le (ofF32 wp) x then return wp
  if F64.le (ofF32 p) x then return p
  return pow32I a (n.val - 1)

end JuliaLean.MathFuncs
