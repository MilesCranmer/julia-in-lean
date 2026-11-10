import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Common

/-! Kernel checks of `ssaOK` on the lowered-code CFGs with 1 and 2 blocks. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa_1 : (juliaCFGs 1).all ssaOK = true := by decide +kernel
theorem ssa_2_0 : (((juliaCFGs 2).drop 0).take 2).all ssaOK = true := by decide +kernel
theorem ssa_2_2 : (((juliaCFGs 2).drop 2).take 2).all ssaOK = true := by decide +kernel
theorem ssa_2_4 : (((juliaCFGs 2).drop 4).take 2).all ssaOK = true := by decide +kernel
theorem ssa_2_6 : (((juliaCFGs 2).drop 6).take 2).all ssaOK = true := by decide +kernel
theorem ssa_2_8 : (((juliaCFGs 2).drop 8).take 2).all ssaOK = true := by decide +kernel
theorem ssa_2_10 : (((juliaCFGs 2).drop 10).take 2).all ssaOK = true := by decide +kernel

theorem ssa_2 : (juliaCFGs 2).all ssaOK = true := by
  have h := (all_drop_of_chunk ssaOK (juliaCFGs 2) 0 ssa_2_0 (all_drop_of_chunk ssaOK (juliaCFGs 2) 2 ssa_2_2 (all_drop_of_chunk ssaOK (juliaCFGs 2) 4 ssa_2_4 (all_drop_of_chunk ssaOK (juliaCFGs 2) 6 ssa_2_6 (all_drop_of_chunk ssaOK (juliaCFGs 2) 8 ssa_2_8 (all_drop_of_chunk ssaOK (juliaCFGs 2) 10 ssa_2_10 (by decide +kernel : ((juliaCFGs 2).drop 12).all ssaOK = true)))))))
  simpa using h

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
