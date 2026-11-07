import JuliaLean.base.mpfr

/-!
`BigFloat` at master `bbfa0ce4150` (`base/mpfr.jl`).

MPFR calls are exact primitives: each returns the exact result correctly rounded to the
destination precision in the requested rounding mode (MPFR 4.2 manual §4.4 "Rounding" and
§5 "MPFR Interface"). Julia sets the exponent range to its maximum (`base/mpfr.jl:47-56`),
so exponents are unbounded here. A finite nonzero value is `m * 2^e` with `m` odd.
-/


namespace JuliaLean.BigNums

open JuliaLean JuliaLean.Promotion

/-- `BigFloat(q, r; precision = p)` is `q` correctly rounded to `p` bits in direction `r` (the
`BigFloat` docstring, `base/mpfr.jl:258-263`), for every nonzero normalized finite rational. -/
def BigFloatOfRationalRounded : Prop :=
  ∀ (p : Nat) (r : MPFRMode) (num : Int) (den : Nat),
    1 ≤ p → 0 < den → num ≠ 0 → Nat.gcd num.natAbs den = 1 →
    ofRational p r num den = roundP p r num den

theorem bigFloatOfRationalRounded_refuted : ¬ BigFloatOfRationalRounded := by
  intro h
  have := h 2 .rndN 1 5 (by decide) (by decide) (by decide) (by decide)
  revert this
  decide +kernel


/-- `cmp(x::BigFloat, y::Float64)` follows the total order implemented by `isless` (the `cmp`
docstring, `base/operators.jl:508-511`). -/
def CmpBigFloatIsless : Prop :=
  ∀ (x : BF) (y : Fl double),
    cmpF64 x y = (if islessBF x (ofF64 y) then -1 else if islessBF (ofF64 y) x then 1 else 0)

theorem cmpBigFloatIsless_refuted : ¬ CmpBigFloatIsless := by
  intro h
  have := h (.zero true) (Fl.zero false)
  revert this
  decide +kernel


/-- `round(Int64, x, r)` for a finite BigFloat `x` rounds the value in direction `r` for every
`RoundingMode`, throwing `InexactError` only when the result does not fit (the `round`
docstring, `base/rounding.jl:331-350`). -/
def RoundBigFloatAllModes : Prop :=
  ∀ (m e : Int) (r : RMode), m ≠ 0 →
    roundToInt .i64 (.fin m e) r =
      match JInt.convert (IntTy.i64.name) .i64 (roundIntSpec r (BF.fin m e).toRat.1 (BF.fin m e).toRat.2) with
      | .ok v => .ok v
      | .error _ => .error (.inexactError "round")

theorem roundBigFloatAllModes_refuted : ¬ RoundBigFloatAllModes := by
  intro h
  have := h 5 (-1) .nearestTiesAway (by decide)
  revert this
  decide +kernel

end JuliaLean.BigNums
