import JuliaLean.MathFuncs.ProofsEvalBase

/-! Kernel evaluation of `exp2IntegerCheck` on the offsets `[1049, 2098)`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000

namespace JuliaLean.MathFuncs

open JuliaLean.Float

theorem exp2IntegerCheck_1049_0 : chunkOk exp2IntegerCheck 1049 100 = true := by decide +kernel

theorem exp2IntegerCheck_1049_1 : chunkOk exp2IntegerCheck 1149 100 = true := by decide +kernel

theorem exp2IntegerCheck_1049_2 : chunkOk exp2IntegerCheck 1249 100 = true := by decide +kernel

theorem exp2IntegerCheck_1049_3 : chunkOk exp2IntegerCheck 1349 100 = true := by decide +kernel

theorem exp2IntegerCheck_1049_4 : chunkOk exp2IntegerCheck 1449 100 = true := by decide +kernel

theorem exp2IntegerCheck_1049_5 : chunkOk exp2IntegerCheck 1549 100 = true := by decide +kernel

theorem exp2IntegerCheck_1049_6 : chunkOk exp2IntegerCheck 1649 100 = true := by decide +kernel

theorem exp2IntegerCheck_1049_7 : chunkOk exp2IntegerCheck 1749 100 = true := by decide +kernel

theorem exp2IntegerCheck_1049_8 : chunkOk exp2IntegerCheck 1849 100 = true := by decide +kernel

theorem exp2IntegerCheck_1049_9 : chunkOk exp2IntegerCheck 1949 100 = true := by decide +kernel

theorem exp2IntegerCheck_1049_10 : chunkOk exp2IntegerCheck 2049 49 = true := by decide +kernel

theorem exp2IntegerCheck_1049_2098 (n : Nat) (h1 : 1049 ≤ n) (h2 : n < 2098) : exp2IntegerCheck n = true := by
  by_cases h0 : n < 1149
  · exact chunkOk_spec exp2IntegerCheck_1049_0 (by omega) (by omega)
  by_cases h1 : n < 1249
  · exact chunkOk_spec exp2IntegerCheck_1049_1 (by omega) (by omega)
  by_cases h2 : n < 1349
  · exact chunkOk_spec exp2IntegerCheck_1049_2 (by omega) (by omega)
  by_cases h3 : n < 1449
  · exact chunkOk_spec exp2IntegerCheck_1049_3 (by omega) (by omega)
  by_cases h4 : n < 1549
  · exact chunkOk_spec exp2IntegerCheck_1049_4 (by omega) (by omega)
  by_cases h5 : n < 1649
  · exact chunkOk_spec exp2IntegerCheck_1049_5 (by omega) (by omega)
  by_cases h6 : n < 1749
  · exact chunkOk_spec exp2IntegerCheck_1049_6 (by omega) (by omega)
  by_cases h7 : n < 1849
  · exact chunkOk_spec exp2IntegerCheck_1049_7 (by omega) (by omega)
  by_cases h8 : n < 1949
  · exact chunkOk_spec exp2IntegerCheck_1049_8 (by omega) (by omega)
  by_cases h9 : n < 2049
  · exact chunkOk_spec exp2IntegerCheck_1049_9 (by omega) (by omega)
  exact chunkOk_spec exp2IntegerCheck_1049_10 (by omega) (by omega)

end JuliaLean.MathFuncs
