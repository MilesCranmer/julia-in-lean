import JuliaLean.MathFuncs.PropsSpecial
import JuliaLean.MathFuncs.ProofsEvalBase

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000

namespace JuliaLean.MathFuncs
open JuliaLean.Float

def intExp2Check (n : Nat) : Bool :=
  decide (exp2Int (JInt.wrap .i64 ((n : Int) - 1074)) =
    F64.ldexp F64.one ((n : Int) - 1074))

theorem intExp2Chunk0 : chunkOk intExp2Check 0 100 = true := by decide +kernel

theorem intExp2Chunk1 : chunkOk intExp2Check 100 100 = true := by decide +kernel

theorem intExp2Chunk2 : chunkOk intExp2Check 200 100 = true := by decide +kernel

theorem intExp2Chunk3 : chunkOk intExp2Check 300 100 = true := by decide +kernel

theorem intExp2Chunk4 : chunkOk intExp2Check 400 100 = true := by decide +kernel

theorem intExp2Chunk5 : chunkOk intExp2Check 500 100 = true := by decide +kernel

theorem intExp2Chunk6 : chunkOk intExp2Check 600 100 = true := by decide +kernel

theorem intExp2Chunk7 : chunkOk intExp2Check 700 100 = true := by decide +kernel

theorem intExp2Chunk8 : chunkOk intExp2Check 800 100 = true := by decide +kernel

theorem intExp2Chunk9 : chunkOk intExp2Check 900 100 = true := by decide +kernel

theorem intExp2Chunk10 : chunkOk intExp2Check 1000 100 = true := by decide +kernel

theorem intExp2Chunk11 : chunkOk intExp2Check 1100 100 = true := by decide +kernel

theorem intExp2Chunk12 : chunkOk intExp2Check 1200 100 = true := by decide +kernel

theorem intExp2Chunk13 : chunkOk intExp2Check 1300 100 = true := by decide +kernel

theorem intExp2Chunk14 : chunkOk intExp2Check 1400 100 = true := by decide +kernel

theorem intExp2Chunk15 : chunkOk intExp2Check 1500 100 = true := by decide +kernel

theorem intExp2Chunk16 : chunkOk intExp2Check 1600 100 = true := by decide +kernel

theorem intExp2Chunk17 : chunkOk intExp2Check 1700 100 = true := by decide +kernel

theorem intExp2Chunk18 : chunkOk intExp2Check 1800 100 = true := by decide +kernel

theorem intExp2Chunk19 : chunkOk intExp2Check 1900 100 = true := by decide +kernel

theorem intExp2Chunk20 : chunkOk intExp2Check 2000 98 = true := by decide +kernel

theorem intExp2Check_all (n : Nat) (hn : n < 2098) : intExp2Check n = true := by
  by_cases h0 : n < 100
  · exact chunkOk_spec intExp2Chunk0 (by omega) (by omega)
  by_cases h1 : n < 200
  · exact chunkOk_spec intExp2Chunk1 (by omega) (by omega)
  by_cases h2 : n < 300
  · exact chunkOk_spec intExp2Chunk2 (by omega) (by omega)
  by_cases h3 : n < 400
  · exact chunkOk_spec intExp2Chunk3 (by omega) (by omega)
  by_cases h4 : n < 500
  · exact chunkOk_spec intExp2Chunk4 (by omega) (by omega)
  by_cases h5 : n < 600
  · exact chunkOk_spec intExp2Chunk5 (by omega) (by omega)
  by_cases h6 : n < 700
  · exact chunkOk_spec intExp2Chunk6 (by omega) (by omega)
  by_cases h7 : n < 800
  · exact chunkOk_spec intExp2Chunk7 (by omega) (by omega)
  by_cases h8 : n < 900
  · exact chunkOk_spec intExp2Chunk8 (by omega) (by omega)
  by_cases h9 : n < 1000
  · exact chunkOk_spec intExp2Chunk9 (by omega) (by omega)
  by_cases h10 : n < 1100
  · exact chunkOk_spec intExp2Chunk10 (by omega) (by omega)
  by_cases h11 : n < 1200
  · exact chunkOk_spec intExp2Chunk11 (by omega) (by omega)
  by_cases h12 : n < 1300
  · exact chunkOk_spec intExp2Chunk12 (by omega) (by omega)
  by_cases h13 : n < 1400
  · exact chunkOk_spec intExp2Chunk13 (by omega) (by omega)
  by_cases h14 : n < 1500
  · exact chunkOk_spec intExp2Chunk14 (by omega) (by omega)
  by_cases h15 : n < 1600
  · exact chunkOk_spec intExp2Chunk15 (by omega) (by omega)
  by_cases h16 : n < 1700
  · exact chunkOk_spec intExp2Chunk16 (by omega) (by omega)
  by_cases h17 : n < 1800
  · exact chunkOk_spec intExp2Chunk17 (by omega) (by omega)
  by_cases h18 : n < 1900
  · exact chunkOk_spec intExp2Chunk18 (by omega) (by omega)
  by_cases h19 : n < 2000
  · exact chunkOk_spec intExp2Chunk19 (by omega) (by omega)
  exact chunkOk_spec intExp2Chunk20 (by omega) (by omega)

theorem exp2Int_same_i64 (t : IntTy) (x : JInt t)
    (lo : -1074 ≤ x.val) (hi : x.val ≤ 1023) :
    exp2Int x = exp2Int (JInt.wrap .i64 x.val) := by
  have hv : (JInt.wrap .i64 x.val).val = x.val := by
    change wrapInt .i64 x.val = x.val
    apply wrapInt_of_inRange
    simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
    omega
  by_cases hs : x.val ≤ -1023
  · have hp : (JInt.wrap (IntTy.promote t .i64) (x.val + 1074)).val = x.val + 1074 := by
      apply wrapInt_of_inRange
      cases t <;> simp [IntTy.promote, IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] <;> omega
    have hq : (JInt.wrap (IntTy.promote .i64 .i64) (x.val + 1074)).val = x.val + 1074 := by
      change wrapInt (IntTy.promote .i64 .i64) (x.val + 1074) = x.val + 1074
      apply wrapInt_of_inRange
      simp [IntTy.promote, IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
      omega
    simp [exp2Int, hv, hp, hq, show ¬ x.val > 1023 by omega,
      show ¬ x.val < -1074 by omega, hs]
  · simp [exp2Int, hv, show ¬ x.val > 1023 by omega,
      show ¬ x.val < -1074 by omega, hs]

theorem exp2BitIntegerExact_proven : exp2BitIntegerExact := by
  intro t x
  by_cases hi : x.val > 1023
  · simp [exp2Int, hi]
  by_cases lo : x.val < -1074
  · simp [exp2Int, hi, lo]
  simp only [hi, lo, ↓reduceIte]
  rw [exp2Int_same_i64 t x (by omega) (by omega)]
  let n := (x.val + 1074).toNat
  have hn : n < 2098 := by dsimp [n]; omega
  have hnval : (n : Int) - 1074 = x.val := by dsimp [n]; omega
  have h := intExp2Check_all n hn
  have h' := of_decide_eq_true h
  change exp2Int (JInt.wrap .i64 ((n : Int) - 1074)) =
    F64.ldexp F64.one ((n : Int) - 1074) at h'
  simpa [hnval] using h'

end JuliaLean.MathFuncs
