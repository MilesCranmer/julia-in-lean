import JuliaLean.FloatFuncs.Round
import JuliaLean.MathCov.Fmt

/-!
Models of `base/rounding.jl` at Julia master `bbfa0ce4150` (unchanged in the
functions below from 1.13.2 except where noted): rounding-mode predicates,
`correct_rounding_requires_increment`, the floating-point environment wrappers, and
the directed conversions `_convert_rounding`.

The floating-point environment is an explicit state `FEnv`. The constants
`JL_FE_*` are the x86-64 glibc `<fenv.h>` values reported by `jl_get_fenv_consts`.
-/

namespace JuliaLean.MathCov.Rounding

open JuliaLean JuliaLean.Float JuliaLean.Promotion JuliaLean.FloatFuncs
open JuliaLean.MathCov.FP

/-- `rounds_to_nearest(::RoundingMode)` and its three nearest-mode methods;
`base/rounding.jl:115-118`. -/
def roundsToNearest : Mode → Bool
  | .Nearest | .NearestTiesUp | .NearestTiesAway => true
  | _ => false

/-- `rounds_away_from_zero(mode, sign_bit)`; `base/rounding.jl:119-122`. The nearest modes
have no method. -/
def roundsAwayFromZero : Mode → Bool → Jl Bool
  | .Up, s => .ok !s
  | .Down, s => .ok s
  | .FromZero, _ => .ok true
  | .ToZero, _ => .ok false
  | _, _ => .error (.methodError "rounds_away_from_zero")

/-- `tie_breaker_is_to_even`; `base/rounding.jl:123-125`. -/
def tieBreakerIsToEven : Mode → Jl Bool
  | .Nearest => .ok true
  | .NearestTiesUp => .ok false
  | .NearestTiesAway => .ok false
  | _ => .error (.methodError "tie_breaker_is_to_even")

/-- `tie_breaker_rounds_away_from_zero`; `base/rounding.jl:126-127`. -/
def tieBreakerRoundsAwayFromZero : Mode → Bool → Jl Bool
  | .NearestTiesUp, s => .ok !s
  | .NearestTiesAway, _ => .ok true
  | _, _ => .error (.methodError "tie_breaker_rounds_away_from_zero")

/-- The `(mode, sign_bit)` tuple methods; `base/rounding.jl:129-132`. -/
def roundsToNearestT (t : Mode × Bool) : Bool := roundsToNearest t.1
def roundsAwayFromZeroT (t : Mode × Bool) : Jl Bool := roundsAwayFromZero t.1 t.2
def tieBreakerIsToEvenT (t : Mode × Bool) : Jl Bool := tieBreakerIsToEven t.1
def tieBreakerRoundsAwayFromZeroT (t : Mode × Bool) : Jl Bool :=
  tieBreakerRoundsAwayFromZero t.1 t.2

/-- `FinalBit`, `RoundBit`, `StickyBit`; `base/rounding.jl:134-136`. -/
inductive Bit where
  | final | round | sticky
  deriving DecidableEq

/-- `correct_rounding_requires_increment(x, rounding_mode, sign_bit)`;
`base/rounding.jl:138-168`. -/
def correctRoundingRequiresIncrement (x : Bit → Bool) (m : Mode) (s : Bool) : Jl Bool := do
  let r := (m, s)
  if roundsToNearestT r then
    if x .round then
      if x .sticky then pure true
      else if (← tieBreakerIsToEvenT r) then pure (x .final)
      else tieBreakerRoundsAwayFromZeroT r
    else pure false
  else
    if (← roundsAwayFromZeroT r) then
      if x .round then pure true else pure (x .sticky)
    else pure false

/-- x86-64 glibc rounding-mode codes `JL_FE_TONEAREST`, `JL_FE_DOWNWARD`,
`JL_FE_UPWARD`, `JL_FE_TOWARDZERO`; `base/rounding.jl:5-17`. -/
def feToNearest : Int := 0x000
def feDownward : Int := 0x400
def feUpward : Int := 0x800
def feTowardZero : Int := 0xc00

/-- `to_fenv`; `base/rounding.jl:170-173`. -/
def toFenv : Mode → Jl Int
  | .Nearest => .ok feToNearest
  | .ToZero => .ok feTowardZero
  | .Up => .ok feUpward
  | .Down => .ok feDownward
  | _ => .error (.methodError "to_fenv")

/-- `from_fenv(r::Integer)`; `base/rounding.jl:175-187`. -/
def fromFenv (r : Int) : Jl Mode :=
  if r == feToNearest then .ok .Nearest
  else if r == feDownward then .ok .Down
  else if r == feUpward then .ok .Up
  else if r == feTowardZero then .ok .ToZero
  else .error (.argumentError "invalid rounding mode code")

/-- The thread's floating-point environment: the C rounding mode and the
flush-to-zero/denormals-are-zero flag. -/
structure FEnv where
  rounding : Int
  zeroSubnormals : Bool

/-- `jl_set_fenv_rounding(i) = fesetround(i)`: 0 and the new mode for a valid code,
nonzero and no change otherwise. -/
def jlSetFenvRounding (i : Int) (e : FEnv) : Int × FEnv :=
  if i == feToNearest || i == feDownward || i == feUpward || i == feTowardZero then
    (0, { e with rounding := i })
  else (1, e)

/-- `setrounding_raw(::Type{<:Union{Float32,Float64}}, i)`; `base/rounding.jl:219`. -/
def setroundingRaw (i : Int) (e : FEnv) : Int × FEnv := jlSetFenvRounding i e

/-- `rounding_raw(::Type{<:Union{Float32,Float64}})`; `base/rounding.jl:220`. -/
def roundingRaw (e : FEnv) : Int := e.rounding

/-- `rounding(::Type{T}) where {T<:Union{Float32,Float64}}`; `base/rounding.jl:222`. -/
def rounding (e : FEnv) : Jl Mode := fromFenv (roundingRaw e)

/-- `rounding(::Type{Union{}}, slurp...)`, `setrounding(f, ::Type{Union{}}, slurp...)`,
`maxintfloat(::Type{Union{}}, ...)` and the other bottom-type methods: `MethodError`;
`base/rounding.jl:223,247`. -/
def bottomMethodError {α : Type} (fn : String) : Jl α := .error (.methodError fn)

/-- `setrounding(f, T, rounding)`; `base/rounding.jl:238-246`. `rawGet`/`rawSet` are
`rounding_raw(T)`/`setrounding_raw(T, ·)`, `setr` is `setrounding(T, ·)` (no method for
`Float32`/`Float64`), and `f` runs on the state. The `finally` restores the raw mode. -/
def setroundingF {S α : Type} (rawGet : S → Int) (rawSet : Int → S → S)
    (setr : Mode → S → Jl S) (f : S → Jl α × S) (mode : Mode) (s : S) : Jl α × S :=
  let old := rawGet s
  match setr mode s with
  | .error e => (.error e, s)
  | .ok s1 =>
    let (res, s2) := f s1
    (res, rawSet old s2)

/-- `setrounding_raw(f, T, rounding)`; `base/rounding.jl:248-256`. -/
def setroundingRawF {S α : Type} (rawGet : S → Int) (rawSet : Int → S → S)
    (f : S → Jl α × S) (rounding : Int) (s : S) : Jl α × S :=
  let old := rawGet s
  let s1 := rawSet rounding s
  let (res, s2) := f s1
  (res, rawSet old s2)

/-- `setrounding(T, mode)` for `T = Float32, Float64`: no method. -/
def setroundingFloat (_ : Mode) (_ : FEnv) : Jl FEnv := .error (.methodError "setrounding")

/-- `set_zero_subnormals(yes)`: `jl_set_zero_subnormals` returns 0 on x86-64, which
supports flush-to-zero; `base/rounding.jl:313`. -/
def setZeroSubnormals (yes : Bool) (e : FEnv) : Bool × FEnv :=
  (true, { e with zeroSubnormals := yes })

/-- `get_zero_subnormals()`; `base/rounding.jl:325`. -/
def getZeroSubnormals (e : FEnv) : Bool := e.zeroSubnormals

/-- Exact comparison `a < b` between floats of two formats (both widen exactly). -/
def ltMixed {T S : FTy} (a : FV T) (b : FV S) : Bool := F64.lt (toD a) (toD b)

/-- `x > 0.0` and `x < 0.0` for a float `x`. -/
def posF {S : FTy} (x : FV S) : Bool := F64.lt (F64.zero false) (toD x)
def negF {S : FTy} (x : FV S) : Bool := F64.lt (toD x) (F64.zero false)

/-- `T(x::Real, r)` = `_convert_rounding(T, x, r)` for a floating-point `x` of format
`S`; `base/rounding.jl:267-293`. `convert(T, x)` is the nearest conversion. The two
ties modes have no `_convert_rounding` method. -/
def convertRounding (T : FTy) {S : FTy} (x : FV S) : Mode → Jl (FV T)
  | .Nearest => .ok (conv x)
  | .Down =>
    let y : FV T := conv x
    .ok (if ltMixed x y then prevfloat y else y)
  | .Up =>
    let y : FV T := conv x
    .ok (if ltMixed y x then nextfloat y else y)
  | .ToZero =>
    let y : FV T := conv x
    .ok (if posF x then (if ltMixed x y then prevfloat y else y)
         else (if ltMixed y x then nextfloat y else y))
  | .FromZero =>
    let y : FV T := conv x
    .ok (if negF x then (if ltMixed x y then prevfloat y else y)
         else (if ltMixed y x then nextfloat y else y))
  | _ => .error (.methodError "_convert_rounding")

/-! ## Generic rounding forwarders, `base/rounding.jl:480-497` -/

/-- The keyword forwarding methods `trunc`, `floor`, `ceil`, and `round`. -/
def roundForward {α β : Type} (round : α → Mode → β) (x : α) (m : Mode) : β := round x m

/-- The typed forwarding methods `trunc(T,x)`, `floor(T,x)`, `ceil(T,x)`, and `round(T,x)`. -/
def roundTypeForward {α β γ : Type} (round : α → β → Mode → γ)
    (T : α) (x : β) (m : Mode) : γ := round T x m

/-- `round(T, x, r) = _round_convert(T, round(x,r), x, r)`. -/
def roundTypeConvert {α β γ : Type} (round : α → Mode → β)
    (convert : β → α → Mode → γ) (x : α) (r : Mode) : γ := convert (round x r) x r

/-- `_round_convert(T, x_integer, x, r) = convert(T, x_integer)`. -/
def roundConvertGeneric {α β : Type} (convert : α → β) (xInteger : α) : β := convert xInteger

/-- The `Union{}` rounding forwarders throw `MethodError`. -/
def bottomRoundError {α : Type} (fn : String) : Jl α := .error (.methodError fn)

/-- `round(x::Integer, r) = x`. -/
def roundInteger (x : Int) (_r : Mode) : Int := x

end JuliaLean.MathCov.Rounding
