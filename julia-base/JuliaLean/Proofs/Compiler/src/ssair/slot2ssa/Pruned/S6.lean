import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.Pruned.Common

/-! Kernel check of `prunedOK` on `slice3 [1, 2]`. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem pruned_3_6_0 : ((slice3b [1, 2] []).all fun c => prunedOK (mkBlocks c.1 c.2)) = true := by
  decide +kernel
theorem pruned_3_6_1 : ((slice3b [1, 2] [3]).all fun c => prunedOK (mkBlocks c.1 c.2)) = true := by
  decide +kernel
theorem pruned_3_6_2 : ((slice3b [1, 2] [2]).all fun c => prunedOK (mkBlocks c.1 c.2)) = true := by
  decide +kernel
theorem pruned_3_6_3 : ((slice3b [1, 2] [2, 3]).all fun c => prunedOK (mkBlocks c.1 c.2)) = true := by
  decide +kernel
theorem pruned_3_6_4 : ((slice3b [1, 2] [1]).all fun c => prunedOK (mkBlocks c.1 c.2)) = true := by
  decide +kernel
theorem pruned_3_6_5 : ((slice3b [1, 2] [1, 3]).all fun c => prunedOK (mkBlocks c.1 c.2)) = true := by
  decide +kernel
theorem pruned_3_6_6 : ((slice3b [1, 2] [1, 2]).all fun c => prunedOK (mkBlocks c.1 c.2)) = true := by
  decide +kernel
theorem pruned_3_6_7 : ((slice3b [1, 2] [1, 2, 3]).all fun c => prunedOK (mkBlocks c.1 c.2)) = true := by
  decide +kernel

theorem pruned_3_6 : ((slice3 [1, 2]).all fun c => prunedOK (mkBlocks c.1 c.2)) = true :=
  slice3_of_sub _ _ pruned_3_6_0 pruned_3_6_1 pruned_3_6_2 pruned_3_6_3 pruned_3_6_4 pruned_3_6_5 pruned_3_6_6 pruned_3_6_7

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
