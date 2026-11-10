import JuliaLean.Proofs.Compiler.src.ssair.domtree.Props

/-! Exhaustive kernel evaluation of `KillEdgeSmall`, `CfgEditSmall` over `smallCFGs`, one
slice at a time so that each kernel check stays small. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.domtree

open JuliaLean.Compiler.ssair

theorem killEdge_12 : (smallCFGs12.all fun c => killOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem killEdge_3_0 : ((slice3 []).all fun c => killOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem killEdge_3_1 : ((slice3 [3]).all fun c => killOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem killEdge_3_2 : ((slice3 [2]).all fun c => killOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem killEdge_3_3 : ((slice3 [2, 3]).all fun c => killOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem killEdge_3_4 : ((slice3 [1]).all fun c => killOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem killEdge_3_5 : ((slice3 [1, 3]).all fun c => killOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem killEdge_3_6 : ((slice3 [1, 2]).all fun c => killOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem killEdge_3_7 : ((slice3 [1, 2, 3]).all fun c => killOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem killEdge_lower : (lower3.all fun c => killOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem killEdge_branch : (branchCFGs.all fun c => killOK (mkBlocks c.1 c.2)) = true := by decide +kernel

theorem killEdgeSmall_proven : KillEdgeSmall :=
  smallCFGs_of_slices (fun c => killOK (mkBlocks c.1 c.2)) killEdge_12
    killEdge_3_0 killEdge_3_1 killEdge_3_2 killEdge_3_3 killEdge_3_4 killEdge_3_5 killEdge_3_6 killEdge_3_7 killEdge_lower killEdge_branch

theorem cfgEdit_12 : (smallCFGs12.all fun c => cfgEditOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem cfgEdit_3_0 : ((slice3 []).all fun c => cfgEditOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem cfgEdit_3_1 : ((slice3 [3]).all fun c => cfgEditOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem cfgEdit_3_2 : ((slice3 [2]).all fun c => cfgEditOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem cfgEdit_3_3 : ((slice3 [2, 3]).all fun c => cfgEditOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem cfgEdit_3_4 : ((slice3 [1]).all fun c => cfgEditOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem cfgEdit_3_5 : ((slice3 [1, 3]).all fun c => cfgEditOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem cfgEdit_3_6 : ((slice3 [1, 2]).all fun c => cfgEditOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem cfgEdit_3_7 : ((slice3 [1, 2, 3]).all fun c => cfgEditOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem cfgEdit_lower : (lower3.all fun c => cfgEditOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem cfgEdit_branch : (branchCFGs.all fun c => cfgEditOK (mkBlocks c.1 c.2)) = true := by decide +kernel

theorem cfgEditSmall_proven : CfgEditSmall :=
  smallCFGs_of_slices (fun c => cfgEditOK (mkBlocks c.1 c.2)) cfgEdit_12
    cfgEdit_3_0 cfgEdit_3_1 cfgEdit_3_2 cfgEdit_3_3 cfgEdit_3_4 cfgEdit_3_5 cfgEdit_3_6 cfgEdit_3_7 cfgEdit_lower cfgEdit_branch

end JuliaLean.Proofs.Compiler.src.ssair.domtree
