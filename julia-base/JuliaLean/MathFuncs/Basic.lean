import JuliaLean.MathFuncs.Prelude

/-!
Short `base/math.jl` functions on Float64 (master `bbfa0ce4150`): `min`, `max`,
`minmax`, `clamp`, `hypot`, `scaleinv`, `deg2rad`, `rad2deg`, `fourthroot`,
`exponent(::Real)` for `Rational{Int64}`, and the generic and `BitSigned`
`copysign`/`flipsign` methods.
-/

namespace JuliaLean.MathFuncs

open JuliaLean.Float

/-- LLVM `minimum`, the `min_float` intrinsic behind `min(::Float64, ::Float64)`;
`base/math.jl:838`. A NaN operand gives NaN; `-0.0` is below `+0.0`. -/
def fmin (x y : F64) : F64 :=
  if F64.isnan x then x
  else if F64.isnan y then y
  else if F64.lt x y || (F64.iszero x && F64.iszero y && F64.signbit x) then x
  else y

/-- LLVM `maximum`, the `max_float` intrinsic behind `max(::Float64, ::Float64)`;
`base/math.jl:839`. -/
def fmax (x y : F64) : F64 :=
  if F64.isnan x then x
  else if F64.isnan y then y
  else if F64.lt y x || (F64.iszero x && F64.iszero y && F64.signbit y) then x
  else y

/-- `minmax(x::T, y::T) where {T<:AbstractFloat} = min(x, y), max(x, y)`; `base/math.jl:836`. -/
def fminmax (x y : F64) : F64 × F64 := (fmin x y, fmax x y)

/-- `clamp(x, lo, hi)` with three Float64 arguments; `base/intfuncs.jl:1461-1464`. -/
def clamp (x lo hi : F64) : F64 :=
  if F64.lt hi x then hi else if F64.lt x lo then lo else x

/-- `sqrt(eps(Float64)/2)`, the constant at `base/math.jl:753`. -/
def hypotTiny : F64 := lit 0x3E46A09E667F3BCD
/-- `eps(Float64)*sqrt(floatmin(Float64))`, `base/math.jl:758`. -/
def hypotScale : F64 := lit 0x1CC0000000000000
/-- `sqrt(floatmax(Float64)/2)`, `base/math.jl:759`. -/
def hypotBig : F64 := lit 0x5FE6A09E667F3BCC
/-- `sqrt(floatmin(Float64))`, `base/math.jl:763`. -/
def hypotSmall : F64 := lit 0x2000000000000000

/-- `_hypot(x, y)` for Float64 on a machine with hardware fma (`have_fma` true);
`base/math.jl:732-776`. -/
def hypot (x y : F64) : F64 :=
  let axu := F64.abs x
  let ayu := F64.abs y
  let ax := F64.div axu F64.one
  let ay := F64.div ayu F64.one
  if F64.isinf ax || F64.isinf ay then F64.inf
  else
    let swap := F64.lt ax ay
    let axu := if swap then ayu else axu
    let (ax, ay) := if swap then (ay, ax) else (ax, ay)
    if F64.le ay (F64.mul ax hypotTiny) then axu
    else
      let (ax, ay, scale) :=
        if F64.lt hypotBig ax then
          (F64.mul ax hypotScale, F64.mul ay hypotScale, F64.div F64.one hypotScale)
        else if F64.lt ay hypotSmall then
          (F64.div ax hypotScale, F64.div ay hypotScale, hypotScale)
        else (ax, ay, F64.one)
      let h0 := match F64.sqrt (F64.muladd ax ax (F64.mul ay ay)) with
        | .ok v => v
        | .error _ => F64.nan
      let hsquared := F64.mul h0 h0
      let axsquared := F64.mul ax ax
      let num := F64.sub
        (F64.add (F64.fma (F64.neg ay) ay (F64.sub hsquared axsquared))
          (F64.fma h0 h0 (F64.neg hsquared)))
        (F64.fma ax ax (F64.neg axsquared))
      let h := F64.sub h0 (F64.div num (F64.mul (F64.ofInt 2) h0))
      F64.mul (F64.mul h scale) F64.one

/-- `scaleinv(x::Float64)`; `base/math.jl:1100-1111`. -/
def scaleinv (x : F64) : F64 × F64 :=
  let umin := 0x0010000000000000
  let umax := 0x7FD0000000000000
  let e := bitsOf x / 2^52 % 2048 * 2^52
  let u := if e > umax then umax else if e < umin then umin else e
  (F64.ofBits u, F64.ofBits (umin + umax - u))

/-- Maximum of the bit patterns of nonnegative values,
`reinterpret(T, maximum(z -> reinterpret(Signed, z), x))`; `base/math.jl:822`. -/
def maxBits : List F64 → Nat
  | [] => 0
  | x :: xs => max (bitsOf x) (maxBits xs)

/-- `mapreduce(y -> abs2(y * invscale), add_fast, x)` folded from the left, the order the
compiler emits for three arguments; `add_fast` lets it reassociate longer sums;
`base/math.jl:826-827`. -/
def sumScaledSquares (invscale : F64) : F64 → List F64 → F64
  | acc, [] => acc
  | acc, y :: ys =>
    let t := F64.mul y invscale
    sumScaledSquares invscale (F64.add acc (F64.mul t t)) ys

/-- `_hypot(x::NTuple{N,<:IEEEFloat})` for `N ≥ 3` Float64 arguments; `base/math.jl:816-828`. -/
def hypotN (xs : List F64) : F64 :=
  let xs := xs.map F64.abs
  if xs.any (fun z => F64.eq z F64.inf) then F64.inf
  else
    let maxabs := F64.ofBits (maxBits xs)
    if !(F64.lt F64.zero maxabs) then maxabs
    else
      let (scale, invscale) := scaleinv maxabs
      match xs with
      | [] => maxabs
      | y :: ys =>
        let t := F64.mul y invscale
        match F64.sqrt (sumScaledSquares invscale (F64.mul t t) ys) with
        | .ok s => F64.mul scale s
        | .error _ => F64.nan

/-- `Float64(pi)`, the `π` constant of `base/mathconstants.jl:13` rounded to nearest. -/
def piF64 : F64 := lit 0x400921FB54442D18

/-- `deg2rad(z::AbstractFloat) = z * _pi_over_180(z)`, `_pi_over_180(z) = oftype(z, pi)/180`;
`base/math.jl:216-218,253`. -/
def deg2rad (z : F64) : F64 := F64.mul z (F64.div piF64 (F64.ofInt 180))

/-- `rad2deg(z::AbstractFloat) = z * _180_over_pi(z)`, `_180_over_pi(z) = 180/oftype(z, pi)`;
`base/math.jl:213-215,238`. -/
def rad2deg (z : F64) : F64 := F64.mul z (F64.div (F64.ofInt 180) piF64)

/-- `fourthroot(x::Number) = sqrt(sqrt(x))`; `base/math.jl:685`. -/
def fourthroot (x : F64) : Jl F64 := do
  let s ← F64.sqrt x
  F64.sqrt s

/-- `exponent(x::Real)` on a `Rational{Int64}` `num//den`: `float(x)` is
`float(x.num)/float(x.den)` (`base/rational.jl:204`), then `exponent(::Float64)`;
`base/math.jl:1322-1331`. -/
def exponentRat (num den : JInt .i64) : Jl Int :=
  F64.exponent (F64.div (F64.ofJInt num) (F64.ofJInt den))

end JuliaLean.MathFuncs
