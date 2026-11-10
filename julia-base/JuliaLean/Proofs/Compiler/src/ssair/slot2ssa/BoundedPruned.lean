import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.Pruned.S0
import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.Pruned.S1
import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.Pruned.S2
import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.Pruned.S3
import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.Pruned.S4
import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.Pruned.S5
import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.Pruned.S6
import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.Pruned.S7

/-! Exhaustive kernel evaluation of `PrunedPhisSmall` over `cfgsUpTo3`: the 1- and 2-block CFGs
here, the 3-block CFGs of `slice3` in `Pruned/S0` to `Pruned/S7`, one slice of 64 CFGs each,
split again into eight kernel checks, and `lower3` here in six checks. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem pruned_12 : (smallCFGs12.all fun c => prunedOK (mkBlocks c.1 c.2)) = true := by
  decide +kernel

theorem pruned_lower_0 : ((lower3.drop 0).take 8).all (fun c => prunedOK (mkBlocks c.1 c.2)) = true := by
  decide +kernel
theorem pruned_lower_8 : ((lower3.drop 8).take 8).all (fun c => prunedOK (mkBlocks c.1 c.2)) = true := by
  decide +kernel
theorem pruned_lower_16 : ((lower3.drop 16).take 8).all (fun c => prunedOK (mkBlocks c.1 c.2)) = true := by
  decide +kernel
theorem pruned_lower_24 : ((lower3.drop 24).take 8).all (fun c => prunedOK (mkBlocks c.1 c.2)) = true := by
  decide +kernel
theorem pruned_lower_32 : ((lower3.drop 32).take 8).all (fun c => prunedOK (mkBlocks c.1 c.2)) = true := by
  decide +kernel
theorem pruned_lower_40 : ((lower3.drop 40).take 8).all (fun c => prunedOK (mkBlocks c.1 c.2)) = true := by
  decide +kernel

theorem pruned_lower : (lower3.all fun c => prunedOK (mkBlocks c.1 c.2)) = true := by
  have h := all_drop_of_take _ lower3 0 8 pruned_lower_0 <|
    all_drop_of_take _ lower3 8 8 pruned_lower_8 <|
    all_drop_of_take _ lower3 16 8 pruned_lower_16 <|
    all_drop_of_take _ lower3 24 8 pruned_lower_24 <|
    all_drop_of_take _ lower3 32 8 pruned_lower_32 <|
    all_drop_of_take _ lower3 40 8 pruned_lower_40
      (by decide +kernel : (lower3.drop 48).all (fun c => prunedOK (mkBlocks c.1 c.2)) = true)
  simpa using h

theorem prunedPhisSmall_proven : PrunedPhisSmall :=
  cfgsUpTo3_of_slices (fun c => prunedOK (mkBlocks c.1 c.2)) pruned_12
    pruned_3_0 pruned_3_1 pruned_3_2 pruned_3_3 pruned_3_4 pruned_3_5 pruned_3_6 pruned_3_7
    pruned_lower

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
