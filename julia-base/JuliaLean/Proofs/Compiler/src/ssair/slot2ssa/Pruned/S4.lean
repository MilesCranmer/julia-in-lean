import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.Pruned.Common

/-! Kernel check of `prunedOK` on `slice3 [1]`. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem pruned_3_4_0 : ((slice3b [1] []).all fun c => prunedOK (mkBlocks c.1 c.2)) = true := by
  decide +kernel
theorem pruned_3_4_1 : ((slice3b [1] [3]).all fun c => prunedOK (mkBlocks c.1 c.2)) = true := by
  decide +kernel
theorem pruned_3_4_2 : ((slice3b [1] [2]).all fun c => prunedOK (mkBlocks c.1 c.2)) = true := by
  decide +kernel
theorem pruned_3_4_3 : ((slice3b [1] [2, 3]).all fun c => prunedOK (mkBlocks c.1 c.2)) = true := by
  decide +kernel
theorem pruned_3_4_4 : ((slice3b [1] [1]).all fun c => prunedOK (mkBlocks c.1 c.2)) = true := by
  decide +kernel
theorem pruned_3_4_5 : ((slice3b [1] [1, 3]).all fun c => prunedOK (mkBlocks c.1 c.2)) = true := by
  decide +kernel
theorem pruned_3_4_6 : ((slice3b [1] [1, 2]).all fun c => prunedOK (mkBlocks c.1 c.2)) = true := by
  decide +kernel
theorem pruned_3_4_7 : ((slice3b [1] [1, 2, 3]).all fun c => prunedOK (mkBlocks c.1 c.2)) = true := by
  decide +kernel

theorem pruned_3_4 : ((slice3 [1]).all fun c => prunedOK (mkBlocks c.1 c.2)) = true :=
  slice3_of_sub _ _ pruned_3_4_0 pruned_3_4_1 pruned_3_4_2 pruned_3_4_3 pruned_3_4_4 pruned_3_4_5 pruned_3_4_6 pruned_3_4_7

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
