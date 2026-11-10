import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel checks of `semOK` on the lowered-code CFGs with 1 and 2 blocks. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem_1 : (juliaCFGs 1).all semOK = true := by decide +kernel
theorem sem_2_0 : (((juliaCFGs 2).drop 0).take 2).all semOK = true := by decide +kernel
theorem sem_2_2 : (((juliaCFGs 2).drop 2).take 2).all semOK = true := by decide +kernel
theorem sem_2_4 : (((juliaCFGs 2).drop 4).take 2).all semOK = true := by decide +kernel
theorem sem_2_6 : (((juliaCFGs 2).drop 6).take 2).all semOK = true := by decide +kernel
theorem sem_2_8 : (((juliaCFGs 2).drop 8).take 2).all semOK = true := by decide +kernel
theorem sem_2_10 : (((juliaCFGs 2).drop 10).take 2).all semOK = true := by decide +kernel

theorem sem_2 : (juliaCFGs 2).all semOK = true := by
  have h := (all_drop_of_chunk semOK (juliaCFGs 2) 0 sem_2_0 (all_drop_of_chunk semOK (juliaCFGs 2) 2 sem_2_2 (all_drop_of_chunk semOK (juliaCFGs 2) 4 sem_2_4 (all_drop_of_chunk semOK (juliaCFGs 2) 6 sem_2_6 (all_drop_of_chunk semOK (juliaCFGs 2) 8 sem_2_8 (all_drop_of_chunk semOK (juliaCFGs 2) 10 sem_2_10 (by decide +kernel : ((juliaCFGs 2).drop 12).all semOK = true)))))))
  simpa using h

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
