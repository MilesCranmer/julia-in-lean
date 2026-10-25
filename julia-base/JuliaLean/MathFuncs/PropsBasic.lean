import JuliaLean.MathFuncs.Basic

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000

/-!
Properties of the short `base/math.jl` functions and their refutations.
-/

namespace JuliaLean.MathFuncs

open JuliaLean.Float

/-- `2^e ≤ n/d` for natural `n` and positive `d`. -/
def twoPowLe (e : Int) (n d : Nat) : Prop :=
  if e ≥ 0 then 2^e.toNat * d ≤ n else d ≤ n * 2^(-e).toNat

instance (e : Int) (n d : Nat) : Decidable (twoPowLe e n d) := by
  unfold twoPowLe; split <;> exact inferInstance

/-- `exponent(x::Real)` docstring, `base/math.jl:903`: the largest integer `y` with
`2^y ≤ abs(x)`, for every nonzero `Rational{Int64}` `num//den` in lowest terms. -/
def exponentRationalDefinition : Prop := ∀ num den : JInt .i64,
  0 < den.val → num.val ≠ 0 → Nat.gcd num.val.natAbs den.val.natAbs = 1 →
  ∃ e, exponentRat num den = .ok e ∧
    twoPowLe e num.val.natAbs den.val.natAbs ∧ ¬ twoPowLe (e + 1) num.val.natAbs den.val.natAbs

theorem exponentRationalDefinition_refuted : ¬ exponentRationalDefinition := by
  intro h
  obtain ⟨e, he, hle, _⟩ := h (JInt.wrap .i64 (2^63 - 1)) (JInt.wrap .i64 (2^62))
    (by decide) (by decide) (by decide)
  have hval : exponentRat (JInt.wrap .i64 (2^63 - 1)) (JInt.wrap .i64 (2^62)) = .ok 1 := by
    decide
  rw [hval] at he
  cases he
  exact absurd hle (by decide)

/-- Squared midpoint test: `h` is a binary64 value nearest to `√(sn/sd)` when `sn/sd` lies
between the squares of the midpoints from `h` to its two neighbours (the lower bound is
dropped at zero). -/
def nearestSqrt (h : F64) (sn : Nat) (sd : Nat) : Bool :=
  let r := F64.toRat h
  let up := F64.toRat (F64.nextfloat h)
  let dn := F64.toRat (F64.prevfloat h)
  let hiN := r.1 * (up.2 : Int) + up.1 * (r.2 : Int)
  let hiD := 2 * r.2 * up.2
  let loN := r.1 * (dn.2 : Int) + dn.1 * (r.2 : Int)
  let loD := 2 * r.2 * dn.2
  F64.isfinite h && !F64.signbit h &&
    decide ((sn : Int) * (hiD * hiD : Nat) ≤ hiN * hiN * (sd : Int)) &&
    (decide (loN ≤ 0) || decide (loN * loN * (sd : Int) ≤ (sn : Int) * (loD * loD : Nat)))

/-- `x^2 + y^2` as an exact fraction of naturals. -/
def sumSquares (x y : F64) : Nat × Nat :=
  let a := F64.toRat x
  let b := F64.toRat y
  (a.1.natAbs^2 * b.2^2 + b.1.natAbs^2 * a.2^2, a.2^2 * b.2^2)

/-- Source comment at `base/math.jl:770`: with hardware fma, `hypot(x, y)` "is correctly
rounded", i.e. a binary64 value nearest to `√(x²+y²)` for all finite `x`, `y`. -/
def hypotCorrectlyRounded : Prop := ∀ x y : F64,
  F64.isfinite x = true → F64.isfinite y = true →
  F64.isinf (hypot x y) = false →
  nearestSqrt (hypot x y) (sumSquares x y).1 (sumSquares x y).2 = true

theorem hypotCorrectlyRounded_refuted : ¬ hypotCorrectlyRounded := by
  intro h
  have hh := h (F64.ofBits 0xb0013fa26efd2) (F64.ofBits 0x1424c28a4)
    (by decide) (by decide) (by decide)
  exact absurd hh (by decide)

/-- `evalpoly` docstring, `base/math.jl:55`: `evalpoly(x, p)` evaluates `∑ₖ x^(k-1) p[k]`,
which for an empty coefficient tuple is the empty sum, a zero. -/
def evalpolyEmptyZero : Prop := ∀ x : F64,
  ∃ z, evalpoly x [] = .ok z ∧ F64.iszero z = true

theorem evalpolyEmptyZero_refuted : ¬ evalpolyEmptyZero := by
  intro h
  obtain ⟨z, hz, _⟩ := h F64.one
  simp [evalpoly] at hz

/-- `copysign` docstring, `base/number.jl:260`: `copysign(x, y)` has the magnitude of `x` and
the sign of `y`, for every pair of nonzero `Int64` values. -/
def copysignMagnitudeSign : Prop := ∀ x y : JInt .i64, x.val ≠ 0 → y.val ≠ 0 →
  (copysignInt x y).val.natAbs = x.val.natAbs ∧ ((copysignInt x y).val < 0 ↔ y.val < 0)

theorem copysignMagnitudeSign_refuted : ¬ copysignMagnitudeSign := by
  intro h
  have hh := h (JInt.typemin .i64) (JInt.wrap .i64 1) (by decide) (by decide)
  exact absurd hh.2 (by decide)

/-- IEEE 754-2019 `minimum`/`maximum`, the `min_float`/`max_float` intrinsics of
`base/math.jl:838-839`: a NaN argument makes `min`, `max` and both parts of `minmax` NaN. -/
def minMaxNaN : Prop := ∀ x y : F64, (F64.isnan x || F64.isnan y) = true →
  F64.isnan (fmin x y) = true ∧ F64.isnan (fmax x y) = true ∧
    F64.isnan (fminmax x y).1 = true ∧ F64.isnan (fminmax x y).2 = true

/-- `min`/`max` docstrings, `base/operators.jl:542,560` ("with respect to `isless`"), on
non-NaN Float64 arguments, so `-0.0` is below `+0.0`. -/
def minMaxIsless : Prop := ∀ x y : F64, F64.isnan x = false → F64.isnan y = false →
  fmin x y = (if F64.isless y x then y else x) ∧ fmax x y = (if F64.isless y x then x else y)

/-- `clamp` docstring, `base/intfuncs.jl:1438-1439`: return `x` if `lo <= x <= hi`, `hi`
if `x > hi`, `lo` if `x < lo` (for `lo <= hi`), for non-NaN Float64 arguments. -/
def clampSpec : Prop := ∀ x lo hi : F64,
  F64.isnan x = false → F64.isnan lo = false → F64.isnan hi = false →
  (F64.le lo x = true → F64.le x hi = true → clamp x lo hi = x) ∧
  (F64.lt hi x = true → clamp x lo hi = hi) ∧
  (F64.lt x lo = true → F64.le lo hi = true → clamp x lo hi = lo)

/-- `copysign` docstring, `base/number.jl:260`, for Float64: the magnitude (all bits but
the sign) of `x` and the sign bit of `y`, including zeros and NaNs. -/
def copysignFloatSpec : Prop := ∀ x y : F64,
  F64.signbit (copysign x y) = F64.signbit y ∧ F64.abs (copysign x y) = F64.abs x

/-- `flipsign` docstring, `base/number.jl:244`, for Float64: `x` with its sign flipped if
`y` is negative (sign bit set). -/
def flipsignFloatSpec : Prop := ∀ x y : F64,
  F64.abs (flipsign x y) = F64.abs x ∧ F64.signbit (flipsign x y) = (F64.signbit x != F64.signbit y)

/-- Comment at `base/math.jl:743` ("Return Inf if either or both inputs is Inf (Compliance
with IEEE754)") and `base/math.jl:820` ("return Inf even if an argument is NaN"): `hypot`
of arguments including an infinity is `Inf`. -/
def hypotInf : Prop :=
  (∀ x y : F64, (F64.isinf x || F64.isinf y) = true → hypot x y = F64.inf) ∧
  (∀ xs : List F64, xs.any F64.isinf = true → hypotN xs = F64.inf)

/-- `hypot` docstring, `base/math.jl:690` (`√(|x|²+|y|²)`): the result does not depend on
the signs of the arguments. -/
def hypotSignInvariant : Prop := ∀ x y : F64,
  hypot (F64.neg x) y = hypot x y ∧ hypot x (F64.neg y) = hypot x y

/-- `evalpoly` with one coefficient returns that coefficient (`base/math.jl:55`, the sum
`p[1]`), for every `x` including NaN and infinities. -/
def evalpolyOne : Prop := ∀ x c : F64, evalpoly x [c] = .ok c

/-- `min` docstring, `base/operators.jl:560`: "Return the minimum of the arguments, with
respect to `isless`", for all Float64 arguments (`isless` orders NaN last). -/
def minIslessAll : Prop := ∀ x y : F64,
  F64.isequal (fmin x y) (if F64.isless y x then y else x) = true

theorem minIslessAll_refuted : ¬ minIslessAll := by
  intro h
  exact absurd (h F64.nan F64.one) (by decide)

end JuliaLean.MathFuncs
