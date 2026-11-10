import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.Pruned.Common

/-! Kernel check of `prunedOK` on `slice3 [2]`. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem pruned_3_2_0 : ((slice3b [2] []).all fun c => prunedOK (mkBlocks c.1 c.2)) = true := by
  decide +kernel
theorem pruned_3_2_1 : ((slice3b [2] [3]).all fun c => prunedOK (mkBlocks c.1 c.2)) = true := by
  decide +kernel
theorem pruned_3_2_2 : ((slice3b [2] [2]).all fun c => prunedOK (mkBlocks c.1 c.2)) = true := by
  decide +kernel
theorem pruned_3_2_3 : ((slice3b [2] [2, 3]).all fun c => prunedOK (mkBlocks c.1 c.2)) = true := by
  decide +kernel
theorem pruned_3_2_4 : ((slice3b [2] [1]).all fun c => prunedOK (mkBlocks c.1 c.2)) = true := by
  decide +kernel
theorem pruned_3_2_5 : ((slice3b [2] [1, 3]).all fun c => prunedOK (mkBlocks c.1 c.2)) = true := by
  decide +kernel
theorem pruned_3_2_6 : ((slice3b [2] [1, 2]).all fun c => prunedOK (mkBlocks c.1 c.2)) = true := by
  decide +kernel
theorem pruned_3_2_7 : ((slice3b [2] [1, 2, 3]).all fun c => prunedOK (mkBlocks c.1 c.2)) = true := by
  decide +kernel

theorem pruned_3_2 : ((slice3 [2]).all fun c => prunedOK (mkBlocks c.1 c.2)) = true :=
  slice3_of_sub _ _ pruned_3_2_0 pruned_3_2_1 pruned_3_2_2 pruned_3_2_3 pruned_3_2_4 pruned_3_2_5 pruned_3_2_6 pruned_3_2_7

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
