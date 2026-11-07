import JuliaLean.base.div

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000

namespace JuliaLean.Float

/-- The strict RoundDown remainder interval promised by `base/div.jl:95-97`. -/
def remDownBound : Prop := ∀ x y : F64,
  F64.isfinite x = true → F64.isfinite y = true → F64.lt (F64.zero false) y = true →
  F64.le (F64.zero false) (F64.remMode x y .RoundDown) = true ∧
  F64.lt (F64.remMode x y .RoundDown) y = true

theorem remDownBound_refuted : ¬ remDownBound := by
  intro h
  have hh := h (F64.ofBits 0x8000000000000001) F64.one
    (by decide) (by decide) (by decide)
  have bad : F64.lt
    (F64.remMode (F64.ofBits 0x8000000000000001) F64.one .RoundDown) F64.one = false := by decide
  rw [bad] at hh
  exact Bool.false_ne_true hh.2

end JuliaLean.Float
