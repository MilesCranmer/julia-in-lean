import JuliaLean.MathFuncs.Trig
import JuliaLean.MathFuncs.Cbrt
import JuliaLean.MathFuncs.Rem2pi

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000

/-!
Properties of `sinpi`, `cospi`, `sincospi`, `tanpi`, `cbrt`, `rem2pi`, `mod2pi` and
`rem_pio2_kernel` on Float64.
-/

namespace JuliaLean.MathFuncs

open JuliaLean.Float

/-- `sincospi` docstring, `base/special/trig.jl:995`: "Simultaneously compute
`sinpi(x)` and `cospi(x)`", for every non-infinite Float64. -/
def sincospiConsistent : Prop := ∀ x : F64, F64.isinf x = false →
  sincospi x = ((sinpi x).bind fun s => (cospi x).map fun c => (s, c))

/-- `cospi` is even: `cospi(-x) === cospi(x)` for every Float64 (`cos(π(-x)) = cos(πx)`). -/
def cospiEven : Prop := ∀ x : F64, cospi (F64.neg x) = cospi x

/-- `sinpi` is odd: `sinpi(-x) === -sinpi(x)` for every non-NaN Float64. -/
def sinpiOdd : Prop := ∀ x : F64, F64.isnan x = false →
  sinpi (F64.neg x) = (sinpi x).map F64.neg

/-- `sinpi`/`cospi`/`tanpi`/`sincospi` docstrings (`base/special/trig.jl:930,964,1037,998`):
"Throw a DomainError if isinf(x), return a T(NaN) if isnan(x)". -/
def piTrigSpecial : Prop := ∀ x : F64,
  (F64.isinf x = true →
    (∃ m, sinpi x = .error (.domainError m)) ∧ (∃ m, cospi x = .error (.domainError m)) ∧
    (∃ m, tanpi x = .error (.domainError m)) ∧ (∃ m, sincospi x = .error (.domainError m))) ∧
  (F64.isnan x = true →
    (∃ r, sinpi x = .ok r ∧ F64.isnan r = true) ∧ (∃ r, cospi x = .ok r ∧ F64.isnan r = true) ∧
    (∃ r, tanpi x = .ok r ∧ F64.isnan r = true) ∧
    (∃ r s, sincospi x = .ok (r, s) ∧ F64.isnan r = true ∧ F64.isnan s = true))

/-- Large arguments: every Float64 with `|x| ≥ 2^53` is an even integer, so
`sinpi(x) === copysign(0.0, x)`, `cospi(x) == 1` and `tanpi(x) === copysign(0.0, x)`
(`base/special/trig.jl:941,975,1054`). -/
def piTrigLarge : Prop := ∀ x : F64, F64.isfinite x = true →
  F64.le (F64.ofBits 0x4340000000000000) (F64.abs x) = true →
  sinpi x = .ok (copysign F64.zero x) ∧ cospi x = .ok F64.one ∧
    tanpi x = .ok (copysign F64.zero x)

/-- `rem2pi` docstring, `base/math.jl:1193-1195`: the value `x - 2π*round(x/(2π), r)`.
When that quotient is zero the result is `x` itself: for `|x| < π` with RoundNearest,
`0 ≤ x < 2π` with RoundDown, `-2π < x ≤ 0` with RoundUp, and `|x| ≤ 2π` with
RoundToZero (tested here against the binary64 neighbours of π and 2π that Julia uses). -/
def rem2piSmallExact : Prop := ∀ x : F64, F64.isfinite x = true →
  (F64.le (F64.abs x) piRoundDown = true → rem2pi x .RoundNearest = .ok x) ∧
  (F64.le F64.zero x = true → F64.lt x pi4o2H = true → rem2pi x .RoundDown = .ok x) ∧
  (F64.le x F64.zero = true → F64.lt (F64.neg pi4o2H) x = true → rem2pi x .RoundUp = .ok x) ∧
  (F64.le (F64.abs x) pi4o2H = true → rem2pi x .RoundToZero = .ok x)

/-- `rem2pi` of a NaN is NaN and of an infinity is NaN, for each of the four modes with a
Float64 method (`base/special/rem2pi.jl:15-16,41-42,69-70,101-102`). -/
def rem2piNonfinite : Prop := ∀ x : F64, ∀ m : Rounding, m ≠ .RoundNearestTiesAway →
  F64.isfinite x = false → ∃ r, rem2pi x m = .ok r ∧ F64.isnan r = true

/-- IEEE 754 `rootn(x, 3)` special values: `cbrt(±0) === ±0`, `cbrt(±Inf) === ±Inf`, and
`cbrt(NaN)` is NaN (`base/special/cbrt.jl:144-150`). -/
def cbrtSpecial : Prop := ∀ s : Bool,
  cbrt (F64.zero s) = F64.zero s ∧ cbrt (F64.inf s) = F64.inf s ∧
    F64.isnan (cbrt (if s then F64.neg F64.nan else F64.nan)) = true

/-- `cbrt` is exact on perfect cubes: `cbrt(Float64(k)^3) == k` for `1 ≤ k ≤ 1024`. -/
def cbrtExactCubes : Prop := ∀ k : Fin 1024,
  cbrt (F64.ofInt (((k : Int) + 1)^3)) = F64.ofInt ((k : Int) + 1) ∧
    cbrt (F64.ofInt (-((k : Int) + 1)^3)) = F64.ofInt (-((k : Int) + 1))

/-- `rem_pio2_kernel` docstring, `base/special/rem_pio2.jl:218`: "`k` is positive if
`x > 0` and is negative if `x ≤ 0`", for every finite Float64. -/
def remPio2KernelSign : Prop := ∀ x : F64, F64.isfinite x = true →
  (F64.lt F64.zero x = true → 0 < (remPio2Kernel x).1) ∧
  (F64.le x F64.zero = true → (remPio2Kernel x).1 < 0)

theorem remPio2KernelSign_refuted : ¬ remPio2KernelSign := by
  intro h
  have hh := (h (F64.neg (F64.ofBits 0x7E51EB2D66005835)) (by decide +kernel)).2 (by decide +kernel)
  exact absurd hh (by decide +kernel)

end JuliaLean.MathFuncs
