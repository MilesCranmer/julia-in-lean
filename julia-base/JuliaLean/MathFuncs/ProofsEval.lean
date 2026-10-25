import JuliaLean.MathFuncs.ProofsEvalLog2Lo
import JuliaLean.MathFuncs.ProofsEvalLog2Hi
import JuliaLean.MathFuncs.ProofsEvalExp2Lo
import JuliaLean.MathFuncs.ProofsEvalExp2Hi

/-!
Proofs of the finite properties in `PropsUniversal` by kernel evaluation. The 2098-case
properties are checked in `ProofsEvalLog2Lo/Hi` and `ProofsEvalExp2Lo/Hi`.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000

namespace JuliaLean.MathFuncs

open JuliaLean.Float

theorem expZero_proven : expZero := by
  unfold expZero; decide +kernel

theorem logOne_proven : logOne := by
  refine ⟨fun b => ?_, ?_⟩
  · cases b <;> decide +kernel
  · decide +kernel

theorem logZero_proven : logZero := by
  refine ⟨fun b => ?_, ?_⟩
  · cases b <;> decide +kernel
  · decide +kernel

theorem powZeroNegOne_proven : powZeroNegOne := by
  intro s; cases s <;> decide +kernel

theorem exp10Log10Exact_proven : exp10Log10Exact := by
  unfold exp10Log10Exact; decide +kernel

theorem log2Pow2Exact_proven : log2Pow2Exact := fun k => by
  have hk := k.isLt
  apply of_decide_eq_true
  by_cases h : k.val < 1049
  · exact log2Pow2Check_0_1049 k.val (by omega) h
  · exact log2Pow2Check_1049_2098 k.val (by omega) hk

theorem exp2IntegerExact_proven : exp2IntegerExact := fun k => by
  have hk := k.isLt
  apply of_decide_eq_true
  by_cases h : k.val < 1049
  · exact exp2IntegerCheck_0_1049 k.val (by omega) h
  · exact exp2IntegerCheck_1049_2098 k.val (by omega) hk

end JuliaLean.MathFuncs
