import JuliaLean.MathFuncs.Pow
import JuliaLean.MathFuncs.Rem2pi
import JuliaLean.MathFuncs.Float32

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000

/-!
Refuted properties of `^`, `exp2(::Int128)` and `rem2pi(::Float32)`.
-/

namespace JuliaLean.MathFuncs

open JuliaLean.Float

/-- IEEE 754-2019 §9.2.1 `pow(±0, y)` for odd integer `y`, and agreement with the
Integer-exponent method `(-0.0)^n` (`base/special/pow.jl:7-31,58-75`): for every odd
integer `n` with `|n| < 2^53`, `(-0.0)^Float64(n)` is a negative zero or `-Inf`. -/
def powNegZeroOddSign : Prop := ∀ n : Int, n % 2 = 1 → n.natAbs < 2^53 →
  ∃ r, powFF (F64.neg F64.zero) (F64.ofInt n) = .ok r ∧ F64.signbit r = true

theorem powNegZeroOddSign_refuted : ¬ powNegZeroOddSign := by
  intro h
  obtain ⟨r, hr, hs⟩ := h 24577 (by decide) (by decide)
  have hv : powFF (F64.neg F64.zero) (F64.ofInt 24577) = .ok F64.zero := by decide
  rw [hv] at hr
  cases hr
  exact absurd hs (by decide)

/-- `exp2` docstring, `base/special/exp.jl:354` (`2^x`): for every `Int128` exponent
below `-1074`, `exp2(x)` rounds to `+0.0`. -/
def exp2Int128Underflow : Prop := ∀ x : JInt .i128, x.val < -1074 → exp2Int x = F64.zero

theorem exp2Int128Underflow_refuted : ¬ exp2Int128Underflow := by
  intro h
  exact absurd (h (JInt.wrap .i128 (-2^64 - 1069)) (by decide)) (by decide)

/-- `mod2pi(x::Float32) = rem2pi(x, RoundDown) = Float32(rem2pi(Float64(x), RoundDown))`;
`base/math.jl:1241`, `base/special/rem2pi.jl:133`. -/
def mod2pi32 (x : F32) : F32 := toF32 (mod2pi (ofF32 x))

/-- `mod2pi` docstring, `base/math.jl:1223`: the result lies in `[0, 2π)`, for every
finite `Float32`. The upper end is checked against `6.28318530717958648 > 2π`, a
weaker condition than the docstring's. -/
def rem2piFloat32Range : Prop := ∀ x : F32, F32.isfinite x = true →
  0 ≤ (F32.toRat (mod2pi32 x)).1 ∧
    (F32.toRat (mod2pi32 x)).1 * 10^17 < 628318530717958648 * ((F32.toRat (mod2pi32 x)).2 : Int)

theorem rem2piFloat32Range_refuted : ¬ rem2piFloat32Range := by
  intro h
  have hh := h (BitVec.ofNat 32 0x80000001) (by decide)
  exact absurd hh.2 (by decide)

end JuliaLean.MathFuncs
