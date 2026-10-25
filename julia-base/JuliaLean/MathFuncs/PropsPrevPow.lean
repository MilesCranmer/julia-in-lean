import JuliaLean.MathFuncs.PrevPow

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000

namespace JuliaLean.MathFuncs

open JuliaLean.Float

/-- `prevpow` docstring, `base/intfuncs.jl:674`: "The largest `a^n` not greater than `x`",
weakened to `prevpow(a, x) <= x`, for every finite Float32 `a > 1` and finite Float64
`x ≥ 1` for which `prevpow` returns. -/
def prevpowLe : Prop := ∀ a : F32, ∀ x : F64,
  F32.isfinite a = true → F64.lt F64.one (ofF32 a) = true →
  F64.isfinite x = true → F64.le F64.one x = true →
  ∀ r, prevpow32 a x = .ok r → F64.le (ofF32 r) x = true

theorem prevpowLe_refuted : ¬ prevpowLe := by
  intro h
  have hh := h (BitVec.ofNat 32 0x40000000) (F64.ofBits 0x48078287f49c4a1d)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (BitVec.ofNat 32 0x7f800000) (by decide +kernel)
  exact absurd hh (by decide +kernel)

end JuliaLean.MathFuncs
