import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel checks of `ssaOK` on the 3-block lowered-code CFGs 25 to 32 of `juliaCFGs 3`,
each CFG in four parts so that each kernel check stays within memory. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_24_0 : ssaOKPart (cfg3 24) 0 = true := by decide +kernel
theorem ssa3p_24_1 : ssaOKPart (cfg3 24) 1 = true := by decide +kernel
theorem ssa3p_24_2 : ssaOKPart (cfg3 24) 2 = true := by decide +kernel
theorem ssa3p_24_3 : ssaOKPart (cfg3 24) 3 = true := by decide +kernel
theorem ssa3c_24 : ssaOK (cfg3 24) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_24_0 ssa3p_24_1 ssa3p_24_2 ssa3p_24_3

theorem ssa3p_25_0 : ssaOKPart (cfg3 25) 0 = true := by decide +kernel
theorem ssa3p_25_1 : ssaOKPart (cfg3 25) 1 = true := by decide +kernel
theorem ssa3p_25_2 : ssaOKPart (cfg3 25) 2 = true := by decide +kernel
theorem ssa3p_25_3 : ssaOKPart (cfg3 25) 3 = true := by decide +kernel
theorem ssa3c_25 : ssaOK (cfg3 25) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_25_0 ssa3p_25_1 ssa3p_25_2 ssa3p_25_3

theorem ssa3p_26_0 : ssaOKPart (cfg3 26) 0 = true := by decide +kernel
theorem ssa3p_26_1 : ssaOKPart (cfg3 26) 1 = true := by decide +kernel
theorem ssa3p_26_2 : ssaOKPart (cfg3 26) 2 = true := by decide +kernel
theorem ssa3p_26_3 : ssaOKPart (cfg3 26) 3 = true := by decide +kernel
theorem ssa3c_26 : ssaOK (cfg3 26) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_26_0 ssa3p_26_1 ssa3p_26_2 ssa3p_26_3

theorem ssa3p_27_0 : ssaOKPart (cfg3 27) 0 = true := by decide +kernel
theorem ssa3p_27_1 : ssaOKPart (cfg3 27) 1 = true := by decide +kernel
theorem ssa3p_27_2 : ssaOKPart (cfg3 27) 2 = true := by decide +kernel
theorem ssa3p_27_3 : ssaOKPart (cfg3 27) 3 = true := by decide +kernel
theorem ssa3c_27 : ssaOK (cfg3 27) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_27_0 ssa3p_27_1 ssa3p_27_2 ssa3p_27_3

theorem ssa3p_28_0 : ssaOKPart (cfg3 28) 0 = true := by decide +kernel
theorem ssa3p_28_1 : ssaOKPart (cfg3 28) 1 = true := by decide +kernel
theorem ssa3p_28_2 : ssaOKPart (cfg3 28) 2 = true := by decide +kernel
theorem ssa3p_28_3 : ssaOKPart (cfg3 28) 3 = true := by decide +kernel
theorem ssa3c_28 : ssaOK (cfg3 28) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_28_0 ssa3p_28_1 ssa3p_28_2 ssa3p_28_3

theorem ssa3p_29_0 : ssaOKPart (cfg3 29) 0 = true := by decide +kernel
theorem ssa3p_29_1 : ssaOKPart (cfg3 29) 1 = true := by decide +kernel
theorem ssa3p_29_2 : ssaOKPart (cfg3 29) 2 = true := by decide +kernel
theorem ssa3p_29_3 : ssaOKPart (cfg3 29) 3 = true := by decide +kernel
theorem ssa3c_29 : ssaOK (cfg3 29) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_29_0 ssa3p_29_1 ssa3p_29_2 ssa3p_29_3

theorem ssa3p_30_0 : ssaOKPart (cfg3 30) 0 = true := by decide +kernel
theorem ssa3p_30_1 : ssaOKPart (cfg3 30) 1 = true := by decide +kernel
theorem ssa3p_30_2 : ssaOKPart (cfg3 30) 2 = true := by decide +kernel
theorem ssa3p_30_3 : ssaOKPart (cfg3 30) 3 = true := by decide +kernel
theorem ssa3c_30 : ssaOK (cfg3 30) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_30_0 ssa3p_30_1 ssa3p_30_2 ssa3p_30_3

theorem ssa3p_31_0 : ssaOKPart (cfg3 31) 0 = true := by decide +kernel
theorem ssa3p_31_1 : ssaOKPart (cfg3 31) 1 = true := by decide +kernel
theorem ssa3p_31_2 : ssaOKPart (cfg3 31) 2 = true := by decide +kernel
theorem ssa3p_31_3 : ssaOKPart (cfg3 31) 3 = true := by decide +kernel
theorem ssa3c_31 : ssaOK (cfg3 31) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_31_0 ssa3p_31_1 ssa3p_31_2 ssa3p_31_3

theorem ssa_3_24 : (((juliaCFGs 3).drop 24).take 2).all ssaOK = true := by
  have hl : ((juliaCFGs 3).drop 24).take 2 = [cfg3 24, cfg3 25] := by decide +kernel
  rw [hl]
  simp only [List.all_cons, List.all_nil, ssa3c_24, ssa3c_25, Bool.and_self]
theorem ssa_3_26 : (((juliaCFGs 3).drop 26).take 2).all ssaOK = true := by
  have hl : ((juliaCFGs 3).drop 26).take 2 = [cfg3 26, cfg3 27] := by decide +kernel
  rw [hl]
  simp only [List.all_cons, List.all_nil, ssa3c_26, ssa3c_27, Bool.and_self]
theorem ssa_3_28 : (((juliaCFGs 3).drop 28).take 2).all ssaOK = true := by
  have hl : ((juliaCFGs 3).drop 28).take 2 = [cfg3 28, cfg3 29] := by decide +kernel
  rw [hl]
  simp only [List.all_cons, List.all_nil, ssa3c_28, ssa3c_29, Bool.and_self]
theorem ssa_3_30 : (((juliaCFGs 3).drop 30).take 2).all ssaOK = true := by
  have hl : ((juliaCFGs 3).drop 30).take 2 = [cfg3 30, cfg3 31] := by decide +kernel
  rw [hl]
  simp only [List.all_cons, List.all_nil, ssa3c_30, ssa3c_31, Bool.and_self]

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
