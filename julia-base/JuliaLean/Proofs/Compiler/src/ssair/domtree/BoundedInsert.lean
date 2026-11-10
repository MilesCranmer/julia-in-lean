import JuliaLean.Proofs.Compiler.src.ssair.domtree.Props

/-! Exhaustive kernel evaluation of `InsertEdgeSmall` over `smallCFGs`, one
slice at a time so that each kernel check stays small. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.domtree

open JuliaLean.Compiler.ssair

theorem insertEdge_12 : (smallCFGs12.all fun c => insertOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem insertEdge_3_0 : ((slice3 []).all fun c => insertOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem insertEdge_3_1 : ((slice3 [3]).all fun c => insertOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem insertEdge_3_2 : ((slice3 [2]).all fun c => insertOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem insertEdge_3_3 : ((slice3 [2, 3]).all fun c => insertOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem insertEdge_3_4 : ((slice3 [1]).all fun c => insertOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem insertEdge_3_5 : ((slice3 [1, 3]).all fun c => insertOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem insertEdge_3_6 : ((slice3 [1, 2]).all fun c => insertOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem insertEdge_3_7 : ((slice3 [1, 2, 3]).all fun c => insertOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem insertEdge_lower : (lower3.all fun c => insertOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem insertEdge_b_fwdRec : ((branchFwdRec.map fun s => (s, [1])).all fun c => insertOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem insertEdge_b_fwdUpd : ((branchFwdUpd.map fun s => (s, [1])).all fun c => insertOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem insertEdge_b_postRec : ((branchPostRec.map fun s => (s, [1])).all fun c => insertOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem insertEdge_b_postUpd : ((branchPostUpd.map fun s => (s, [1])).all fun c => insertOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem insertEdge_b_chains : ((branchChains.map fun s => (s, [1])).all fun c => insertOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem insertEdge_b_cex : (branchCex.all fun c => insertOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem insertEdge_branch : (branchCFGs.all fun c => insertOK (mkBlocks c.1 c.2)) = true :=
  branchCFGs_of_parts (fun c => insertOK (mkBlocks c.1 c.2)) insertEdge_b_fwdRec insertEdge_b_fwdUpd insertEdge_b_postRec insertEdge_b_postUpd insertEdge_b_chains insertEdge_b_cex

theorem insertEdgeSmall_proven : InsertEdgeSmall :=
  smallCFGs_of_slices (fun c => insertOK (mkBlocks c.1 c.2)) insertEdge_12
    insertEdge_3_0 insertEdge_3_1 insertEdge_3_2 insertEdge_3_3 insertEdge_3_4 insertEdge_3_5 insertEdge_3_6 insertEdge_3_7 insertEdge_lower insertEdge_branch

end JuliaLean.Proofs.Compiler.src.ssair.domtree
