import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel checks of `ssaOK` on the 3-block lowered-code CFGs 33 to 40 of `juliaCFGs 3`,
each CFG in four parts so that each kernel check stays within memory. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_32_0 : ssaOKPart (cfg3 32) 0 = true := by decide +kernel
theorem ssa3p_32_1 : ssaOKPart (cfg3 32) 1 = true := by decide +kernel
theorem ssa3p_32_2 : ssaOKPart (cfg3 32) 2 = true := by decide +kernel
theorem ssa3p_32_3 : ssaOKPart (cfg3 32) 3 = true := by decide +kernel
theorem ssa3c_32 : ssaOK (cfg3 32) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_32_0 ssa3p_32_1 ssa3p_32_2 ssa3p_32_3

theorem ssa3p_33_0 : ssaOKPart (cfg3 33) 0 = true := by decide +kernel
theorem ssa3p_33_1 : ssaOKPart (cfg3 33) 1 = true := by decide +kernel
theorem ssa3p_33_2 : ssaOKPart (cfg3 33) 2 = true := by decide +kernel
theorem ssa3p_33_3 : ssaOKPart (cfg3 33) 3 = true := by decide +kernel
theorem ssa3c_33 : ssaOK (cfg3 33) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_33_0 ssa3p_33_1 ssa3p_33_2 ssa3p_33_3

theorem ssa3p_34_0 : ssaOKPart (cfg3 34) 0 = true := by decide +kernel
theorem ssa3p_34_1 : ssaOKPart (cfg3 34) 1 = true := by decide +kernel
theorem ssa3p_34_2 : ssaOKPart (cfg3 34) 2 = true := by decide +kernel
theorem ssa3p_34_3 : ssaOKPart (cfg3 34) 3 = true := by decide +kernel
theorem ssa3c_34 : ssaOK (cfg3 34) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_34_0 ssa3p_34_1 ssa3p_34_2 ssa3p_34_3

theorem ssa3p_35_0 : ssaOKPart (cfg3 35) 0 = true := by decide +kernel
theorem ssa3p_35_1 : ssaOKPart (cfg3 35) 1 = true := by decide +kernel
theorem ssa3p_35_2 : ssaOKPart (cfg3 35) 2 = true := by decide +kernel
theorem ssa3p_35_3 : ssaOKPart (cfg3 35) 3 = true := by decide +kernel
theorem ssa3c_35 : ssaOK (cfg3 35) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_35_0 ssa3p_35_1 ssa3p_35_2 ssa3p_35_3

theorem ssa3p_36_0 : ssaOKPart (cfg3 36) 0 = true := by decide +kernel
theorem ssa3p_36_1 : ssaOKPart (cfg3 36) 1 = true := by decide +kernel
theorem ssa3p_36_2 : ssaOKPart (cfg3 36) 2 = true := by decide +kernel
theorem ssa3p_36_3 : ssaOKPart (cfg3 36) 3 = true := by decide +kernel
theorem ssa3c_36 : ssaOK (cfg3 36) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_36_0 ssa3p_36_1 ssa3p_36_2 ssa3p_36_3

theorem ssa3p_37_0 : ssaOKPart (cfg3 37) 0 = true := by decide +kernel
theorem ssa3p_37_1 : ssaOKPart (cfg3 37) 1 = true := by decide +kernel
theorem ssa3p_37_2 : ssaOKPart (cfg3 37) 2 = true := by decide +kernel
theorem ssa3p_37_3 : ssaOKPart (cfg3 37) 3 = true := by decide +kernel
theorem ssa3c_37 : ssaOK (cfg3 37) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_37_0 ssa3p_37_1 ssa3p_37_2 ssa3p_37_3

theorem ssa3p_38_0 : ssaOKPart (cfg3 38) 0 = true := by decide +kernel
theorem ssa3p_38_1 : ssaOKPart (cfg3 38) 1 = true := by decide +kernel
theorem ssa3p_38_2 : ssaOKPart (cfg3 38) 2 = true := by decide +kernel
theorem ssa3p_38_3 : ssaOKPart (cfg3 38) 3 = true := by decide +kernel
theorem ssa3c_38 : ssaOK (cfg3 38) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_38_0 ssa3p_38_1 ssa3p_38_2 ssa3p_38_3

theorem ssa3p_39_0 : ssaOKPart (cfg3 39) 0 = true := by decide +kernel
theorem ssa3p_39_1 : ssaOKPart (cfg3 39) 1 = true := by decide +kernel
theorem ssa3p_39_2 : ssaOKPart (cfg3 39) 2 = true := by decide +kernel
theorem ssa3p_39_3 : ssaOKPart (cfg3 39) 3 = true := by decide +kernel
theorem ssa3c_39 : ssaOK (cfg3 39) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_39_0 ssa3p_39_1 ssa3p_39_2 ssa3p_39_3

theorem ssa_3_32 : (((juliaCFGs 3).drop 32).take 2).all ssaOK = true := by
  have hl : ((juliaCFGs 3).drop 32).take 2 = [cfg3 32, cfg3 33] := by decide +kernel
  rw [hl]
  simp only [List.all_cons, List.all_nil, ssa3c_32, ssa3c_33, Bool.and_self]
theorem ssa_3_34 : (((juliaCFGs 3).drop 34).take 2).all ssaOK = true := by
  have hl : ((juliaCFGs 3).drop 34).take 2 = [cfg3 34, cfg3 35] := by decide +kernel
  rw [hl]
  simp only [List.all_cons, List.all_nil, ssa3c_34, ssa3c_35, Bool.and_self]
theorem ssa_3_36 : (((juliaCFGs 3).drop 36).take 2).all ssaOK = true := by
  have hl : ((juliaCFGs 3).drop 36).take 2 = [cfg3 36, cfg3 37] := by decide +kernel
  rw [hl]
  simp only [List.all_cons, List.all_nil, ssa3c_36, ssa3c_37, Bool.and_self]
theorem ssa_3_38 : (((juliaCFGs 3).drop 38).take 2).all ssaOK = true := by
  have hl : ((juliaCFGs 3).drop 38).take 2 = [cfg3 38, cfg3 39] := by decide +kernel
  rw [hl]
  simp only [List.all_cons, List.all_nil, ssa3c_38, ssa3c_39, Bool.and_self]

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
