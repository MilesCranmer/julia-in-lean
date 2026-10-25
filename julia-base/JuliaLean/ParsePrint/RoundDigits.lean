import JuliaLean.Float.Extras

/-!
`round(x; digits)` and `round(x; sigdigits)` for `Float64` with a negative
effective digit count (`base/floatfuncs.jl:56-148` at master `bbfa0ce4150`,
unchanged from 1.13.2).

`round(x, r; digits=d)` with `d < 0` is `_round_step(x, 10.0^-d, r)`, and
`round(x, r; sigdigits=s)` is `_round_digits(x, r, s - hidigit(x, 10), 10)`.
The power `10.0^k` (`Float64^Int`, `base/math.jl`) and the `log10` inside `hidigit`
are not modelled: the step is passed in, and the property takes it to be the
correctly rounded `10^k` (the reproducer checks `10.0^308 == 1e308`).
-/

namespace JuliaLean.ParsePrint.RoundDigits

open JuliaLean JuliaLean.Float

/-- `_round_step(x, step, r)`, `base/floatfuncs.jl:101-114`. -/
def roundStep (x step : F64) (r : Rounding) : F64 :=
  let y := F64.mul (F64.round (F64.div x step) r) step
  if !F64.isfinite y then
    if F64.lt F64.zero x then (if r = .RoundUp then F64.inf else F64.zero)
    else if F64.lt x F64.zero then (if r = .RoundDown then F64.inf true else F64.zero true)
    else x
  else y

/-- `round(x, r; digits=-k)` for `k ≥ 1`, `base/floatfuncs.jl:73-74,126-128`, given
Julia's value `pow = 10.0^k` of the step. -/
def roundDigitsNeg (x pow : F64) (r : Rounding) : F64 :=
  if !F64.isfinite x then x else roundStep x pow r

/-- Rounding a finite `x` with `x ≥ 10^k` to a multiple of `10^k`
(`round(x; digits=-k)`, docstring `base/rounding.jl:341-349`) never gives zero: the
nearest multiple is at least `10^k`. -/
def RoundDigitsNonzero : Prop := ∀ (x : F64) (k : Nat),
  1 ≤ k → F64.isfinite (F64.ofInt (10 ^ k)) = true → F64.isfinite x = true →
  F64.le (F64.ofInt (10 ^ k)) x = true →
  F64.iszero (roundDigitsNeg x (F64.ofInt (10 ^ k)) .RoundNearest) = false

theorem roundDigitsNonzero_refuted : ¬ RoundDigitsNonzero := by
  intro h
  have bad := h F64.floatmax 308 (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  have : F64.iszero (roundDigitsNeg F64.floatmax (F64.ofInt (10 ^ 308)) .RoundNearest) = true := by
    decide +kernel
  rw [this] at bad
  exact absurd bad (by decide)

end JuliaLean.ParsePrint.RoundDigits
