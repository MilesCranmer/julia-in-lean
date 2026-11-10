import JuliaLean.Proofs.Compiler.src.ssair.domtree.Props

/-! Exhaustive kernel evaluation of `DeleteEdgeSoundSmall` over `smallCFGs`, one
slice at a time so that each kernel check stays small. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.domtree

open JuliaLean.Compiler.ssair

theorem deleteEdgeSound_12 : (smallCFGs12.all fun c => deleteSoundOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem deleteEdgeSound_3_0 : ((slice3 []).all fun c => deleteSoundOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem deleteEdgeSound_3_1 : ((slice3 [3]).all fun c => deleteSoundOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem deleteEdgeSound_3_2 : ((slice3 [2]).all fun c => deleteSoundOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem deleteEdgeSound_3_3 : ((slice3 [2, 3]).all fun c => deleteSoundOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem deleteEdgeSound_3_4 : ((slice3 [1]).all fun c => deleteSoundOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem deleteEdgeSound_3_5 : ((slice3 [1, 3]).all fun c => deleteSoundOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem deleteEdgeSound_3_6 : ((slice3 [1, 2]).all fun c => deleteSoundOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem deleteEdgeSound_3_7 : ((slice3 [1, 2, 3]).all fun c => deleteSoundOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem deleteEdgeSound_lower : (lower3.all fun c => deleteSoundOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem deleteEdgeSound_branch : (branchCFGs.all fun c => deleteSoundOK (mkBlocks c.1 c.2)) = true := by decide +kernel

theorem deleteEdgeSoundSmall_proven : DeleteEdgeSoundSmall :=
  smallCFGs_of_slices (fun c => deleteSoundOK (mkBlocks c.1 c.2)) deleteEdgeSound_12
    deleteEdgeSound_3_0 deleteEdgeSound_3_1 deleteEdgeSound_3_2 deleteEdgeSound_3_3 deleteEdgeSound_3_4 deleteEdgeSound_3_5 deleteEdgeSound_3_6 deleteEdgeSound_3_7 deleteEdgeSound_lower deleteEdgeSound_branch

end JuliaLean.Proofs.Compiler.src.ssair.domtree
