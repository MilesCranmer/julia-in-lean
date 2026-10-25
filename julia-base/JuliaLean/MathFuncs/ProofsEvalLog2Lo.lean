import JuliaLean.MathFuncs.ProofsEvalBase

/-! Kernel evaluation of `log2Pow2Check` on the offsets `[0, 1049)`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000

namespace JuliaLean.MathFuncs

open JuliaLean.Float

theorem log2Pow2Check_0_0 : chunkOk log2Pow2Check 0 100 = true := by decide +kernel

theorem log2Pow2Check_0_1 : chunkOk log2Pow2Check 100 100 = true := by decide +kernel

theorem log2Pow2Check_0_2 : chunkOk log2Pow2Check 200 100 = true := by decide +kernel

theorem log2Pow2Check_0_3 : chunkOk log2Pow2Check 300 100 = true := by decide +kernel

theorem log2Pow2Check_0_4 : chunkOk log2Pow2Check 400 100 = true := by decide +kernel

theorem log2Pow2Check_0_5 : chunkOk log2Pow2Check 500 100 = true := by decide +kernel

theorem log2Pow2Check_0_6 : chunkOk log2Pow2Check 600 100 = true := by decide +kernel

theorem log2Pow2Check_0_7 : chunkOk log2Pow2Check 700 100 = true := by decide +kernel

theorem log2Pow2Check_0_8 : chunkOk log2Pow2Check 800 100 = true := by decide +kernel

theorem log2Pow2Check_0_9 : chunkOk log2Pow2Check 900 100 = true := by decide +kernel

theorem log2Pow2Check_0_10 : chunkOk log2Pow2Check 1000 49 = true := by decide +kernel

theorem log2Pow2Check_0_1049 (n : Nat) (h1 : 0 ≤ n) (h2 : n < 1049) : log2Pow2Check n = true := by
  by_cases h0 : n < 100
  · exact chunkOk_spec log2Pow2Check_0_0 (by omega) (by omega)
  by_cases h1 : n < 200
  · exact chunkOk_spec log2Pow2Check_0_1 (by omega) (by omega)
  by_cases h2 : n < 300
  · exact chunkOk_spec log2Pow2Check_0_2 (by omega) (by omega)
  by_cases h3 : n < 400
  · exact chunkOk_spec log2Pow2Check_0_3 (by omega) (by omega)
  by_cases h4 : n < 500
  · exact chunkOk_spec log2Pow2Check_0_4 (by omega) (by omega)
  by_cases h5 : n < 600
  · exact chunkOk_spec log2Pow2Check_0_5 (by omega) (by omega)
  by_cases h6 : n < 700
  · exact chunkOk_spec log2Pow2Check_0_6 (by omega) (by omega)
  by_cases h7 : n < 800
  · exact chunkOk_spec log2Pow2Check_0_7 (by omega) (by omega)
  by_cases h8 : n < 900
  · exact chunkOk_spec log2Pow2Check_0_8 (by omega) (by omega)
  by_cases h9 : n < 1000
  · exact chunkOk_spec log2Pow2Check_0_9 (by omega) (by omega)
  exact chunkOk_spec log2Pow2Check_0_10 (by omega) (by omega)

end JuliaLean.MathFuncs
