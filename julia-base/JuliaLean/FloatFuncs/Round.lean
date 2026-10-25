import JuliaLean.Float
import JuliaLean.MathFuncs.Log
import JuliaLean.MathFuncs.Pow
import JuliaLean.MathFuncs.Float32

/-!
`round` for Float64 with every `RoundingMode`, and `round(x, r; digits, sigdigits)`
(`base/floatfuncs.jl`, `base/rounding.jl`, `base/float.jl` at master `bbfa0ce4150`;
these definitions are unchanged from 1.13.2).

The five LLVM-backed modes reuse `JuliaLean.Float.F64.round`. `Float64^Int` is
`MathFuncs.powFI`, `Float64^Float64` is `MathFuncs.powFF`, `log10` is `MathFuncs.log10`.
-/

namespace JuliaLean.FloatFuncs

open JuliaLean JuliaLean.Float JuliaLean.MathFuncs

/-- The seven rounding modes, `base/rounding.jl:48-110`. -/
inductive Mode where
  | Nearest | NearestTiesAway | NearestTiesUp | ToZero | FromZero | Up | Down
  deriving Repr, DecidableEq, Inhabited

/-- The four `F64.round` intrinsic modes. -/
def Mode.llvm : Mode → Option Rounding
  | .Nearest => some .RoundNearest
  | .NearestTiesAway => some .RoundNearestTiesAway
  | .ToZero => some .RoundToZero
  | .Up => some .RoundUp
  | .Down => some .RoundDown
  | _ => none

/-- `round(x::IEEEFloat, r)` for every mode: `base/float.jl:458-461` (ToZero, Down, Up,
Nearest), `base/floatfuncs.jl:151-154` (NearestTiesAway, via `F64.round`),
`base/floatfuncs.jl:156-158` (NearestTiesUp) and `base/floatfuncs.jl:160-162` (FromZero). -/
def roundF (x : F64) : Mode → F64
  | .Nearest => F64.round x .RoundNearest
  | .NearestTiesAway => F64.round x .RoundNearestTiesAway
  | .ToZero => F64.round x .RoundToZero
  | .Up => F64.round x .RoundUp
  | .Down => F64.round x .RoundDown
  | .FromZero => if F64.signbit x then F64.round x .RoundDown else F64.round x .RoundUp
  | .NearestTiesUp =>
    -- copysign(floor((x + (T(0.25) - eps(T(0.5)))) + (T(0.25) + eps(T(0.5)))), x)
    let quarter := F64.ofBits 0x3fd0000000000000
    let e := F64.eps (F64.ofBits 0x3fe0000000000000)
    copysign (F64.floor (F64.add (F64.add x (F64.sub quarter e)) (F64.add quarter e))) x

/-- The exact integer `round(n/d, r)` of a rational with positive denominator. -/
def exactRound (n : Int) (d : Nat) (r : Mode) : Int :=
  let f := n / (d : Int)
  let rem := n % (d : Int)
  if rem = 0 then f
  else
    let twice := 2 * rem
    match r with
    | .Down => f
    | .Up => f + 1
    | .ToZero => if n < 0 then f + 1 else f
    | .FromZero => if n < 0 then f else f + 1
    | .Nearest => if twice < d then f else if twice > d then f + 1 else if f % 2 = 0 then f else f + 1
    | .NearestTiesAway => if twice < d then f else if twice > d then f + 1 else if n < 0 then f else f + 1
    | .NearestTiesUp => if twice < d then f else f + 1

/-- `_round_invstep(x, invstep, r)`; `base/floatfuncs.jl:82-88`. -/
def roundInvstep (x invstep : F64) (r : Mode) : F64 :=
  let y := F64.div (roundF (F64.mul x invstep) r) invstep
  if !F64.isfinite y then x else y

/-- `_round_invstepsqrt(x, invstepsqrt, r)`; `base/floatfuncs.jl:92-98`. -/
def roundInvstepsqrt (x s : F64) (r : Mode) : F64 :=
  let y := F64.div (F64.div (roundF (F64.mul (F64.mul x s) s) r) s) s
  if !F64.isfinite y then x else y

/-- `_round_step(x, step, r)`; `base/floatfuncs.jl:101-114`. -/
def roundStep (x step : F64) (r : Mode) : F64 :=
  let y := F64.mul (roundF (F64.div x step) r) step
  if !F64.isfinite y then
    if F64.lt (F64.zero false) x then (if r = .Up then F64.inf false else F64.zero false)
    else if F64.lt x (F64.zero false) then (if r = .Down then F64.inf true else F64.zero true)
    else x
  else y

/-- `_round_digits(x, r, digits, 10)` for Float64 `x` and Int64 `digits`;
`base/floatfuncs.jl:116-130`. `digits/2` is the Float64 quotient of `/(::Int, ::Int)`. -/
def roundDigits (x : F64) (r : Mode) (digits : JInt .i64) : Jl F64 :=
  let ten := F64.ofInt 10
  if digits.val ≥ 0 then
    let invstep := powFI ten digits.val
    if F64.isfinite invstep then .ok (roundInvstep x invstep r)
    else do
      let s ← powFF ten (F64.div (F64.ofInt digits.val) (F64.ofInt 2))
      pure (roundInvstepsqrt x s r)
  else .ok (roundStep x (powFI ten (-digits).val) r)

/-- `hidigit(x::AbstractFloat, 10) = 1 + floor(Int, log10(abs(x)))`, zero for `x == 0`;
`base/floatfuncs.jl:133-136`. `floor(Int, y)` is `F64.floorInt .i64`. -/
def hidigit (x : F64) : Jl (JInt .i64) :=
  if F64.iszero x then .ok (JInt.wrap .i64 0)
  else do
    let l ← log10 (F64.abs x)
    let f ← F64.floorInt .i64 l
    pure (JInt.wrap .i64 1 + f)

/-- `round(x, r; digits)` for Float64; `base/floatfuncs.jl:56-79` (`isfinite(x) || return x`). -/
def roundDigitsKw (x : F64) (r : Mode) (digits : JInt .i64) : Jl F64 :=
  if !F64.isfinite x then .ok x else roundDigits x r digits

/-- `round(x, r; sigdigits)` for Float64: `_round_sigdigits`, `base/floatfuncs.jl:145-148`,
behind the finiteness check of `base/floatfuncs.jl:68`. -/
def roundSigdigits (x : F64) (r : Mode) (sigdigits : JInt .i64) : Jl F64 :=
  if !F64.isfinite x then .ok x
  else do
    let h ← hidigit x
    roundDigits x r (sigdigits - h)

/-- `round(Float32, x::Float64, r)` for the nearest modes: `round(::Type{T}, x, r) =
_round_convert(T, round(x, r), x, r)` with the generic `_round_convert(T, x_integer, x, r) =
convert(T, x_integer)`; `base/rounding.jl:490-491`. -/
def roundToF32 (x : F64) (r : Mode) : MathFuncs.F32 := toF32 (roundF x r)

end JuliaLean.FloatFuncs
