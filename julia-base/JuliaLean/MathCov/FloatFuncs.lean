import JuliaLean.MathCov.Special
import JuliaLean.MathCov.Rounding
import JuliaLean.FloatFuncs.Isapprox

/-!
Methods of `base/floatfuncs.jl` at Julia master `bbfa0ce4150` not modelled by the
`FloatFuncs` area, generic over the three IEEE formats: the `round` keyword dispatcher,
`_round_invstep`, `_round_invstepsqrt`, `hidigit`, `_round_sigdigits`, the three
non-intrinsic rounding modes, `isapprox` and its integer helpers, `rtoldefault`,
`fma_emulated`, `splitbits`, `two_mul`, `fma_correction` and `fma`.
-/

namespace JuliaLean.MathCov.FloatFuncs

open JuliaLean JuliaLean.Float JuliaLean.Promotion JuliaLean.MathCov.FP
open JuliaLean.FloatFuncs (Mode)

variable {T : FTy}

/-- `round(x::T, r)` for the four `llvm` modes (`base/float.jl:458-461`) and the three
`base/floatfuncs.jl` methods below. -/
def roundM (x : FV T) : Mode → FV T
  | .Nearest => roundI x .RoundNearest
  | .ToZero => trunc x
  | .Up => ceil x
  | .Down => floor x
  | .NearestTiesAway =>
    let y := trunc x
    if eq x y then y else trunc (sub (mul (ofInt T 2) x) y)
  | .NearestTiesUp =>
    let q : FV T := div (one T) (ofInt T 4)
    let e := epsOf (div (one T) (ofInt T 2))
    copysign (floor (add (add x (sub q e)) (add q e))) x
  | .FromZero => if x.signbit then floor x else ceil x

/-- `round(x::AbstractFloat, ::RoundingMode{:NearestTiesAway})`; `base/floatfuncs.jl:151-154`. -/
def roundTiesAway (x : FV T) : FV T := roundM x .NearestTiesAway
/-- `round(x::T, ::RoundingMode{:NearestTiesUp})`; `base/floatfuncs.jl:156-158`. -/
def roundTiesUp (x : FV T) : FV T := roundM x .NearestTiesUp
/-- `round(x::AbstractFloat, ::typeof(RoundFromZero))`; `base/floatfuncs.jl:160-162`. -/
def roundFromZero (x : FV T) : FV T := roundM x .FromZero

/-- `_round_invstep(x, invstep, r)`; `base/floatfuncs.jl:82-88`. -/
def roundInvstep (x invstep : FV T) (r : Mode) : FV T :=
  let y := div (roundM (mul x invstep) r) invstep
  if !y.isfinite then x else y

/-- `_round_invstepsqrt(x, invstepsqrt, r)`; `base/floatfuncs.jl:92-98`. -/
def roundInvstepsqrt (x s : FV T) (r : Mode) : FV T :=
  let y := div (div (roundM (mul (mul x s) s) r) s) s
  if !y.isfinite then x else y

/-- `_round_step(x, step, r)`; `base/floatfuncs.jl:101-114`. -/
def roundStep (x step : FV T) (r : Mode) : FV T :=
  let y := mul (roundM (div x step) r) step
  if !y.isfinite then
    if lt (zero T) x then (if r = .Up then inf T else zero T)
    else if lt x (zero T) then (if r = .Down then inf T true else zero T true)
    else x
  else y

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

/-- `_round_digits(x, r, digits, base)` for a float `x`; `base/floatfuncs.jl:116-130`. -/
def roundDigits (x : FV T) (r : Mode) (digits base : Int) : Jl (FV T) :=
  let b := ofInt T base
  if digits ≥ 0 then
    let invstep := powI b digits
    if invstep.isfinite then .ok (roundInvstep x invstep r)
    else do
      let s ← powF b (conv (div (ofInt .f64 digits) (ofInt .f64 2)))
      return roundInvstepsqrt x s r
  else .ok (roundStep x (powI b (-digits)) r)

/-- `log10` and `log` of the format (`Float16` via `Float32`). -/
def log10T (x : FV T) : Jl (FV T) :=
  match T, x with
  | .f64, x => do return of64 (← MathFuncs.log10 (to64 x))
  | .f32, x => Log.log10F32 x
  | .f16, x => do return conv (← Log.log10F32 (conv x))

/-- `floor(Int, y)`: `InexactError` outside `Int64`. -/
def floorInt (y : FV T) : Jl Int :=
  let f := floor y
  if f.isfinite && IntTy.min .i64 ≤ f.truncVal && f.truncVal ≤ IntTy.max .i64 then .ok f.truncVal
  else .error (.inexactError "Int64")

/-- `hidigit(x::AbstractFloat, base)` for `base = 10` and `base = 2`; `log(base, abs(x))`
for other bases is `logBase`; `base/floatfuncs.jl:133-142`. -/
def hidigit (x : FV T) (base : Int) (logBase : FV T → Jl (FV T)) : Jl Int := do
  if x.iszero then return 0
  if base == 10 then return 1 + (← floorInt (← log10T (abs x)))
  else if base == 2 then return 1 + (← Bits.exponent x)
  else return 1 + (← floorInt (← logBase (abs x)))

/-- `hidigit(x::Integer, base) = ndigits0z(x, base)` for `base ≥ 2`: the number of base-`b`
digits of `x`, zero for `x = 0`; `base/floatfuncs.jl:132`. -/
def ndigitsNat (n b : Nat) : Nat :=
  if h : n = 0 ∨ b < 2 then 0 else 1 + ndigitsNat (n / b) b
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

def ndigits0z (x : Int) (b : Nat) : Nat := ndigitsNat x.natAbs b

def hidigitInt (x : Int) (b : Nat) : Nat := ndigits0z x b

/-- `hidigit(x::Real, base) = hidigit(float(x), base)`; `base/floatfuncs.jl:143`. -/
def hidigitReal {α : Type} (float : α → FV T) (x : α) (base : Int) (lb : FV T → Jl (FV T)) : Jl Int :=
  hidigit (float x) base lb

/-- `_round_sigdigits(x, r, sigdigits, base)`; `base/floatfuncs.jl:145-148`. -/
def roundSigdigits (x : FV T) (r : Mode) (sigdigits base : Int) (lb : FV T → Jl (FV T)) :
    Jl (FV T) := do
  let h ← hidigit x base lb
  roundDigits x r (sigdigits - h) base

/-- `round(x::Real, r; digits, sigdigits, base)` for a float `x`; `base/floatfuncs.jl:56-79`.
`none` is `nothing`; `round(x, r)` without keywords is `roundM`. -/
def roundKw (x : FV T) (r : Mode) (digits sigdigits base : Option Int)
    (lb : FV T → Jl (FV T)) : Jl (FV T) :=
  match digits, sigdigits with
  | none, none =>
    match base with
    | none => .error (.methodError "round")
    | some _ => .ok (roundM x r)
  | none, some s => if !x.isfinite then .ok x else roundSigdigits x r s (base.getD 10) lb
  | some d, none => if !x.isfinite then .ok x else roundDigits x r d (base.getD 10)
  | some _, some _ => .error (.argumentError "`round` cannot use both `digits` and `sigdigits` arguments.")

/-! ## isapprox -/

/-- The exact value of a finite float as a rational; `none` for nonfinite values. -/
def ratOf (x : FV T) : Option (Int × Nat) := if x.isfinite then some x.toRat else none

/-- `isapprox(x::Number, y::Number; atol, rtol, nans, norm=abs)` for floats of one format
with float tolerances: `x == y || (isfinite(x) && isfinite(y) && abs(x-y) <=
max(atol, rtol*max(abs(x), abs(y)))) || (nans && isnan(x) && isnan(y))`;
`base/floatfuncs.jl:230-237`. `max` is `max_float`. -/
def isapproxF (x y atol rtol : FV T) (nans : Bool) : Bool :=
  eq x y ||
    (x.isfinite && y.isfinite &&
      le (abs (sub x y)) (Bits.maxFloat atol (mul rtol (Bits.maxFloat (abs x) (abs y))))) ||
    (nans && x.isnan && y.isnan)

/-- `rtoldefault(::Type{T}) = sqrt(eps(T))` for a float type; `base/floatfuncs.jl:326`. -/
def rtoldefaultT (T : FTy) : FV T := sqrtLlvm (epsT T)
/-- `rtoldefault(::Type{<:Real}) = 0`; `base/floatfuncs.jl:327`. -/
def rtoldefaultReal : Int := 0
/-- `rtoldefault(::Type{T}) where {T<:Number}`: recurse into `typeof(one(T))`, throwing
`MethodError` when it is `T` itself; `base/floatfuncs.jl:330-334`. -/
def rtoldefaultNumber {τ : Type} [DecidableEq τ] (oneType : τ → τ) (rt : τ → Jl (FV .f64))
    (t : τ) : Jl (FV .f64) :=
  if oneType t = t then .error (.methodError "rtoldefault") else rt (oneType t)
/-- `rtoldefault(x, y, atol)`: `max` of the two type defaults, zero if `atol > 0`;
`base/floatfuncs.jl:335-338`. Each default is a float of the format or `0` (`none`). -/
def rtoldefault3 (rx ry : Option (FV T)) (atolPos : Bool) : Option (FV T) :=
  let m := match rx, ry with
    | some a, some b => some (Bits.maxFloat a b)
    | some a, none => some a
    | none, some b => some b
    | none, none => none
  if atolPos then (m.map fun _ => zero T) else m

/-- An integer argument of `isapprox`: its type (`none` for `Bool`) and value. -/
structure IntArg where
  ty : Option IntTy
  val : Int

/-- `_uabsdiff(x, y)` on integers: the exact absolute difference (`base/floatfuncs.jl:244-273`);
each fixed-width method computes it in its unsigned type, widening on carry. -/
def uabsdiff (x y : Int) : Int := if x < y then y - x else x - y

/-- `_uabsdiff(x::BitUnsigned, y::BitUnsigned)`: `hi - lo` in the promoted unsigned type. -/
def uabsdiffUU (t : IntTy) (x y : Int) : Int := wrapInt t (max x y - min x y)

/-- `_uabsdiff(x::BitSigned, y::BitSigned)`: `unsigned(hi) - unsigned(lo)` in the promoted
type's unsigned counterpart. -/
def uabsdiffSS (t : IntTy) (x y : Int) : Int :=
  let u := t.toUnsigned
  wrapInt u (wrapInt u (max x y) - wrapInt u (min x y))

/-- `_mixed_uabsdiff(x::BitSigned, y::BitUnsigned)` returning `(m, u, d, carried)` in
`U = promote_type(unsigned(typeof(x)), typeof(y))`; `base/floatfuncs.jl:261-267`. -/
def mixedUabsdiff (U : IntTy) (x y : Int) : Int × Int × Int × Bool :=
  let v := wrapInt U x
  let u := wrapInt U y
  let d := if x < y then wrapInt U (u - v) else wrapInt U (v - u)
  (wrapInt U (-v), u, d, x < 0 && d < u)

/-- `_uabsdiff(x::BitSigned, y::BitUnsigned)`; `base/floatfuncs.jl:269-272`. -/
def uabsdiffSU (U : IntTy) (x y : Int) : Int :=
  let (m, u, d, carried) := mixedUabsdiff U x y
  if carried then m + u else d

/-- `_uabsdiff_le(x::BitSigned, y::BitUnsigned, b)` for a bound `b` given as an exact
rational (`lean` of `b > typemax(d)` and `d <= b` compare exactly);
`base/floatfuncs.jl:275-284`. -/
def uabsdiffLeSU (U : IntTy) (x y : Int) (bNum : Int) (bDen : Nat) : Bool :=
  let (m, u, d, carried) := mixedUabsdiff U x y
  let le (a : Int) : Bool := decide (a * (bDen : Int) ≤ bNum)
  if carried && !(le U.max) then le (m + u)
  else le d && !carried

/-- `_uabsdiff_le(x::Integer, y::Integer, b::Real)` for an integral bound. -/
def uabsdiffLe (x y bound : Int) : Bool := decide (uabsdiff x y ≤ bound)

/-- `_widesum_le(m, u, b)` for an integral bound. -/
def widesumLe (m u bound : Int) : Bool := decide (m + u ≤ bound)

/-- `_scaled_rtol(rtol::BitInteger, scale::BitInteger) = mul_with_overflow(promote(rtol,
scale)...)`; `base/floatfuncs.jl:287`. Returns the wrapped product and the overflow flag. -/
def scaledRtolInt (t : IntTy) (rtol scale : Int) : Int × Bool :=
  let p := wrapInt t rtol * wrapInt t scale
  (wrapInt t p, decide (wrapInt t p ≠ p))

/-- `_scaled_rtol(rtol::Real, scale::Integer) = (rtol * scale, false)`; `base/floatfuncs.jl:286`. -/
def scaledRtolReal {α : Type} (mulα : α → Int → α) (rtol : α) (scale : Int) : α × Bool :=
  (mulα rtol scale, false)

/-- The `norm === abs` branch of integer `isapprox`; `base/floatfuncs.jl:289-303`.
The fixed-width type `t` controls the overflow-aware tolerance product. -/
def isapproxInt (t : IntTy) (x y atol rtol : Int) : Bool :=
  if atol < 1 && rtol == 0 then x == y
  else if x == y then true
  else
    let (bound, overflowed) := scaledRtolInt t rtol (max x.natAbs y.natAbs)
    overflowed || decide (uabsdiff x y ≤ max atol bound)

/-- `isapprox(y; kwargs...) = x -> isapprox(x, y; kwargs...)`; `base/floatfuncs.jl:315`. -/
def isapproxCurried {α : Type} (approx : α → α → Bool) (y : α) : α → Bool := fun x => approx x y

/-- `≉(args...; kws...) = !≈(args...; kws...)`; `base/floatfuncs.jl:323`. -/
def napprox {α : Type} (approx : α → α → Bool) (x y : α) : Bool := !approx x y

/-! ## fma and its emulation -/

/-- `two_mul(x::T, y::T) where {T<:Number} = (x*y, fma(x, y, -x*y))`; `base/floatfuncs.jl:371-374`;
and `two_mul(x::T, y::T)` for `Float16`/`Float32` with hardware fma (`base/floatfuncs.jl:390-394`). -/
def twoMul (x y : FV T) : FV T × FV T := Exp.twoMulG x y

/-- The fma-free branch of `two_mul(x::Float16/Float32)`: `xy = widen(x)*y`, `(T(xy),
T(xy - T(xy)))`; `base/floatfuncs.jl:395-397`. -/
def twoMulNoFma (x y : FV T) : FV T × FV T :=
  let xy : FV .f64 := mul (conv x) (conv y)
  let txy : FV T := conv xy
  (txy, conv (sub xy (conv txy)))

/-- `truncbits(x, 27)`: clear the low 27 significand bits; `base/twiceprecision.jl:33-35`. -/
def truncbits27 (x : FV .f64) : FV .f64 := Fl.ofBits (x.toBits / 2 ^ 27 * 2 ^ 27)

/-- `splitbits(x::Float64) = (hi, x - hi)`; `base/floatfuncs.jl:364-367`. -/
def splitbits (x : FV .f64) : FV .f64 × FV .f64 := let hi := truncbits27 x; (hi, sub x hi)

/-- `two_mul(x::Float64, y::Float64)`; `base/floatfuncs.jl:376-388`. `hasFma` is
`Core.Intrinsics.have_fma(Float64)`. -/
def twoMul64 (hasFma : Bool) (x y : FV .f64) : FV .f64 × FV .f64 :=
  if hasFma then let xy := mul x y; (xy, fma x y (neg xy))
  else
    let (xhi, xlo) := splitbits x
    let (yhi, ylo) := splitbits y
    let xy := mul x y
    let (ylohi, ylolo) := splitbits ylo
    let xylo := add (sub (mul xlo ylohi) (sub (sub (sub xy (mul xhi yhi)) (mul xlo yhi)) (mul xhi ylo)))
      (mul ylolo xlo)
    (xy, xylo)

/-- `fma_emulated(a::T, b::T, c::T)` for `T = Float16, Float32` (round to odd in the
wider type); `base/floatfuncs.jl:350-361`. -/
def fmaEmulatedNarrow (a b c : FV T) : FV T :=
  let W := Special.widenTy T
  let ab : FV W := mul (conv a) (conv b)
  let res : FV W := add ab (conv c)
  let bb := sub res ab
  let err := add (sub ab (sub res bb)) (sub (conv c) bb)
  let u := res.toBits
  let adjust := lt (zero W) (abs err) && u % 2 == 0
  let u' := if adjust then (if err.signbit == res.signbit then u + 1 else u + 2 ^ W.fmt.width - 1) else u
  conv (Fl.ofBits u' : FV W)

/-- `fma_correction(abhi, ablo, c, r)`; `base/floatfuncs.jl:403-411`. -/
def fmaCorrection (abhi ablo c r : FV .f64) : FV .f64 :=
  let e := if lt (abs c) (abs abhi) then add (sub abhi r) c else add (sub c r) abhi
  let s := add e ablo
  let serr := if lt (abs ablo) (abs e) then add (sub e s) ablo else add (sub ablo s) e
  if !serr.iszero && s.toBits % 2 == 0 then nextfloat s (if lt (zero .f64) serr then 1 else -1)
  else s

/-- `isless(abs(x), c)` for the thresholds of `fma_emulated`. -/
def isless64 (x y : FV .f64) : Bool := Fl.isless x y

/-- `fma_emulated(a::Float64, b::Float64, c::Float64)`; `base/floatfuncs.jl:413-460`. -/
def fmaEmulated64 (hasFma : Bool) (a b c : FV .f64) : FV .f64 := Id.run do
  let (abhi, ablo) := twoMul64 hasFma a b
  let t969 : FV .f64 := lit .f64 0x0360000000000000
  if !(add abhi c).isfinite || isless64 (abs abhi) (nextfloat t969) ||
      isless64 (abs a) t969 || isless64 (abs b) t969 then
    let aandbfinite := a.isfinite && b.isfinite
    if !(c.isfinite && aandbfinite) then return (if aandbfinite then c else add abhi c)
    if a.iszero || b.iszero then return add abhi c
    let bias := Bits.exponentFiniteNonzero a + Bits.exponentFiniteNonzero b
    let cDenorm := Bits.ldexp c (-bias)
    if cDenorm.isfinite then
      let a := if FloatIntCov.Float.isSubnormal a then mul a (lit .f64 0x4330000000000000) else a
      let b := if FloatIntCov.Float.isSubnormal b then mul b (lit .f64 0x4330000000000000) else b
      let a : FV .f64 := Fl.ofBits (a.toBits % 2 ^ 52 + (if a.signbit then 2 ^ 63 else 0) + 0x3ff0000000000000)
      let b : FV .f64 := Fl.ofBits (b.toBits % 2 ^ 52 + (if b.signbit then 2 ^ 63 else 0) + 0x3ff0000000000000)
      let c := if eq (Bits.ldexp cDenorm bias) c then cDenorm else copysign (floatminT .f64) c
      let (abhi, ablo) := twoMul64 hasFma a b
      let r := add abhi c
      let s := fmaCorrection abhi ablo c r
      let mut sumhi := add r s
      if !sumhi.iszero then
        let bitsLost := -bias - Bits.exponentFiniteNonzero sumhi - 1022
        if bitsLost > 0 then
          let sumlo := add (sub r sumhi) s
          if (bitsLost != 1) != (sumhi.toBits % 2 == 1) then
            sumhi := nextfloat sumhi (if lt (zero .f64) sumlo then 1 else if lt sumlo (zero .f64) then -1 else 0)
      return Bits.ldexp sumhi bias
    if abhi.isinf && c.signbit == (mul a b).signbit then return abhi
  let r := add abhi c
  let s := fmaCorrection abhi ablo c r
  return add r s

/-- `fma(x::T, y::T, z::T) where {T<:IEEEFloat}`: `have_fma(T) ? fma_float : fma_emulated`;
`base/floatfuncs.jl:464-466`. -/
def fmaDispatch (hasFma : Bool) (x y z : FV T) : FV T :=
  if hasFma then fma x y z
  else match T, x, y, z with
    | .f64, x, y, z => fmaEmulated64 false x y z
    | _, x, y, z => fmaEmulatedNarrow x y z

end JuliaLean.MathCov.FloatFuncs
