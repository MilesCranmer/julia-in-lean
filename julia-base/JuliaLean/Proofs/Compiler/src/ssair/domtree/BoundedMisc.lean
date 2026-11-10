import JuliaLean.Proofs.Compiler.src.ssair.domtree.Props

/-! Exhaustive kernel evaluation of `CompressWorklistSmall`, `NaiveIdomsSmall`, `RenameNodesSmall` over `smallCFGs`, one
slice at a time so that each kernel check stays small. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.domtree

open JuliaLean.Compiler.ssair

theorem compressWorklist_12 : (smallCFGs12.all fun c => compressOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem compressWorklist_3_0 : ((slice3 []).all fun c => compressOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem compressWorklist_3_1 : ((slice3 [3]).all fun c => compressOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem compressWorklist_3_2 : ((slice3 [2]).all fun c => compressOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem compressWorklist_3_3 : ((slice3 [2, 3]).all fun c => compressOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem compressWorklist_3_4 : ((slice3 [1]).all fun c => compressOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem compressWorklist_3_5 : ((slice3 [1, 3]).all fun c => compressOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem compressWorklist_3_6 : ((slice3 [1, 2]).all fun c => compressOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem compressWorklist_3_7 : ((slice3 [1, 2, 3]).all fun c => compressOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem compressWorklist_lower : (lower3.all fun c => compressOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem compressWorklist_branch : (branchCFGs.all fun c => compressOK (mkBlocks c.1 c.2)) = true := by decide +kernel

theorem compressWorklistSmall_proven : CompressWorklistSmall :=
  smallCFGs_of_slices (fun c => compressOK (mkBlocks c.1 c.2)) compressWorklist_12
    compressWorklist_3_0 compressWorklist_3_1 compressWorklist_3_2 compressWorklist_3_3 compressWorklist_3_4 compressWorklist_3_5 compressWorklist_3_6 compressWorklist_3_7 compressWorklist_lower compressWorklist_branch

theorem naiveIdoms_12 : (smallCFGs12.all fun c => naiveOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem naiveIdoms_3_0 : ((slice3 []).all fun c => naiveOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem naiveIdoms_3_1 : ((slice3 [3]).all fun c => naiveOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem naiveIdoms_3_2 : ((slice3 [2]).all fun c => naiveOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem naiveIdoms_3_3 : ((slice3 [2, 3]).all fun c => naiveOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem naiveIdoms_3_4 : ((slice3 [1]).all fun c => naiveOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem naiveIdoms_3_5 : ((slice3 [1, 3]).all fun c => naiveOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem naiveIdoms_3_6 : ((slice3 [1, 2]).all fun c => naiveOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem naiveIdoms_3_7 : ((slice3 [1, 2, 3]).all fun c => naiveOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem naiveIdoms_lower : (lower3.all fun c => naiveOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem naiveIdoms_branch : (branchCFGs.all fun c => naiveOK (mkBlocks c.1 c.2)) = true := by decide +kernel

theorem naiveIdomsSmall_proven : NaiveIdomsSmall :=
  smallCFGs_of_slices (fun c => naiveOK (mkBlocks c.1 c.2)) naiveIdoms_12
    naiveIdoms_3_0 naiveIdoms_3_1 naiveIdoms_3_2 naiveIdoms_3_3 naiveIdoms_3_4 naiveIdoms_3_5 naiveIdoms_3_6 naiveIdoms_3_7 naiveIdoms_lower naiveIdoms_branch

theorem renameNodes_12 : (smallCFGs12.all fun c => renameOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem renameNodes_3_0 : ((slice3 []).all fun c => renameOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem renameNodes_3_1 : ((slice3 [3]).all fun c => renameOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem renameNodes_3_2 : ((slice3 [2]).all fun c => renameOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem renameNodes_3_3 : ((slice3 [2, 3]).all fun c => renameOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem renameNodes_3_4 : ((slice3 [1]).all fun c => renameOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem renameNodes_3_5 : ((slice3 [1, 3]).all fun c => renameOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem renameNodes_3_6 : ((slice3 [1, 2]).all fun c => renameOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem renameNodes_3_7 : ((slice3 [1, 2, 3]).all fun c => renameOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem renameNodes_lower : (lower3.all fun c => renameOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem renameNodes_branch : (branchCFGs.all fun c => renameOK (mkBlocks c.1 c.2)) = true := by decide +kernel

theorem renameNodesSmall_proven : RenameNodesSmall :=
  smallCFGs_of_slices (fun c => renameOK (mkBlocks c.1 c.2)) renameNodes_12
    renameNodes_3_0 renameNodes_3_1 renameNodes_3_2 renameNodes_3_3 renameNodes_3_4 renameNodes_3_5 renameNodes_3_6 renameNodes_3_7 renameNodes_lower renameNodes_branch

end JuliaLean.Proofs.Compiler.src.ssair.domtree
