import JuliaLean.FloatFuncs.Round
import JuliaLean.FloatFuncs.Isapprox

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000

/-!
Properties of `round`/`isapprox` that fail, each with the concrete counterexample that the
reproducer `repro/<id>.jl` confirms on Julia 1.13.2 and master.
-/

namespace JuliaLean.FloatFuncs

open JuliaLean JuliaLean.Float JuliaLean.MathFuncs

/-- `|p - r| ≤ |q - r|` for exact rationals `(numerator, positive denominator)`. -/
def ratDistLe (p q r : Int × Nat) : Bool :=
  decide ((p.1 * r.2 - r.1 * p.2).natAbs * (q.2 * r.2) ≤ (q.1 * r.2 - r.1 * q.2).natAbs * (p.2 * r.2))

/-- `round(Float32, x::Float64)` rounds to the integer representable in Float32 that is
nearest to `x` (`base/rounding.jl:352-354`): no finite integral Float32 `c` is closer. -/
def RoundToF32Nearest : Prop := ∀ (x : F64) (c : MathFuncs.F32),
  F64.isfinite x = true → MathFuncs.F32.isfinite c = true →
  (MathFuncs.F32.toRat c).1 % ((MathFuncs.F32.toRat c).2 : Int) = 0 →
  MathFuncs.F32.isfinite (roundToF32 x .Nearest) = true →
  ratDistLe (MathFuncs.F32.toRat (roundToF32 x .Nearest)) (MathFuncs.F32.toRat c) (F64.toRat x) = true

/-- `x = 16777217.3`, `c = 16777218f0`: Julia returns `16777216f0`. -/
theorem roundToF32Nearest_refuted : ¬ RoundToF32Nearest := by
  intro h
  have bad := h (F64.ofBits 0x4170000014cccccd) (BitVec.ofNat 32 0x4b800001)
    (by decide) (by decide) (by decide) (by decide +kernel)
  revert bad
  decide +kernel

/-- `floor(x; sigdigits=1)` of a value `1 ≤ x < 1e22` is its leading digit times a power
of ten, so it is never zero (`base/rounding.jl:344-345,451-452`). -/
def FloorSigdigitsNonzero : Prop := ∀ x v : F64,
  F64.le F64.one x = true → F64.lt x (F64.ofInt (10^22)) = true →
  roundSigdigits x .Down (JInt.wrap .i64 1) = .ok v → F64.iszero v = false

/-- `x = prevfloat(1000.0)`: `floor(x; sigdigits=1) == 0.0`. -/
theorem floorSigdigitsNonzero_refuted : ¬ FloorSigdigitsNonzero := by
  intro h
  have bad := h (F64.ofBits 0x408f3fffffffffff) (F64.zero false) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  revert bad
  decide

/-- `ceil(x; digits=-k)` of a positive finite `x` is a positive multiple of `10^k`, hence at
least Julia's step `10.0^k` (`base/rounding.jl:341-342,468-474`), for `1 ≤ k ≤ 22`. -/
def CeilDigitsAbove : Prop := ∀ (x v : F64) (k : Nat), 1 ≤ k → k ≤ 22 →
  F64.isfinite x = true → F64.lt (F64.zero false) x = true →
  roundDigitsKw x .Up (JInt.wrap .i64 (-(k : Int))) = .ok v →
  F64.le (powFI (F64.ofInt 10) k) v = true

/-- `x = nextfloat(0.0)`, `k = 1`: `ceil(x; digits=-1) == 0.0`. -/
theorem ceilDigitsAbove_refuted : ¬ CeilDigitsAbove := by
  intro h
  have bad := h (F64.ofBits 1) (F64.zero false) 1 (by decide) (by decide) (by decide)
    (by decide) (by decide +kernel)
  revert bad
  decide +kernel

/-- `isapprox(x::Int64, y::Int64; atol, rtol)` returns
`x == y || abs(x - y) <= max(atol, rtol * max(abs(x), abs(y)))` computed exactly
(`base/floatfuncs.jl:166-170`), never an exception. -/
def IntIsapproxFormula : Prop := ∀ x y atol rtol : JInt .i64,
  isapproxI64 x y atol rtol =
    .ok (decide (x.val = y.val ∨
      ((x.val - y.val).natAbs : Int) ≤
        max atol.val (rtol.val * ((max x.val.natAbs y.val.natAbs : Nat) : Int))))

/-- `isapprox(1, 2; rtol=-1)` throws `InexactError` on master. -/
theorem intIsapproxFormula_refuted : ¬ IntIsapproxFormula := by
  intro h
  have bad := h (JInt.wrap .i64 1) (JInt.wrap .i64 2) (JInt.wrap .i64 0) (JInt.wrap .i64 (-1))
  revert bad
  decide

/-- Rounding to `s` significant digits is idempotent: rounding the result again to `s`
significant digits returns it unchanged (`base/rounding.jl:344-345`), for `1 ≤ s ≤ 17`. -/
def SigdigitsIdempotent : Prop := ∀ (x y : F64) (s : Nat), 1 ≤ s → s ≤ 17 →
  F64.isfinite x = true → roundSigdigits x .Nearest (JInt.wrap .i64 s) = .ok y →
  roundSigdigits y .Nearest (JInt.wrap .i64 s) = .ok y

/-- `x = 9.526624812270413e-145`, `s = 1`: `y = 1.0e-144`, and `round(y; sigdigits=1)` is
`1.0000000000000001e-144`. -/
theorem sigdigitsIdempotent_refuted : ¬ SigdigitsIdempotent := by
  intro h
  have bad := h (F64.ofBits 0x2207cab23592d675) (F64.ofBits 0x2208f9574dcf8a70) 1
    (by decide) (by decide) (by decide) (by decide +kernel)
  revert bad
  decide +kernel

end JuliaLean.FloatFuncs
