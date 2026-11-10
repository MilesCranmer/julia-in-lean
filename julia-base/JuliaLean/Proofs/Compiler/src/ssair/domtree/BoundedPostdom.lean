import JuliaLean.Proofs.Compiler.src.ssair.domtree.Props

/-! Exhaustive kernel evaluation of `ConstructPostdomtreeSmall` over `smallCFGs`, one
slice at a time so that each kernel check stays small. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.domtree

open JuliaLean.Compiler.ssair

theorem constructPostdomtree_12 : (smallCFGs12.all fun c => constructOK (mkBlocks c.1 c.2) true) = true := by decide +kernel
theorem constructPostdomtree_3_0 : ((slice3 []).all fun c => constructOK (mkBlocks c.1 c.2) true) = true := by decide +kernel
theorem constructPostdomtree_3_1 : ((slice3 [3]).all fun c => constructOK (mkBlocks c.1 c.2) true) = true := by decide +kernel
theorem constructPostdomtree_3_2 : ((slice3 [2]).all fun c => constructOK (mkBlocks c.1 c.2) true) = true := by decide +kernel
theorem constructPostdomtree_3_3 : ((slice3 [2, 3]).all fun c => constructOK (mkBlocks c.1 c.2) true) = true := by decide +kernel
theorem constructPostdomtree_3_4 : ((slice3 [1]).all fun c => constructOK (mkBlocks c.1 c.2) true) = true := by decide +kernel
theorem constructPostdomtree_3_5 : ((slice3 [1, 3]).all fun c => constructOK (mkBlocks c.1 c.2) true) = true := by decide +kernel
theorem constructPostdomtree_3_6 : ((slice3 [1, 2]).all fun c => constructOK (mkBlocks c.1 c.2) true) = true := by decide +kernel
theorem constructPostdomtree_3_7 : ((slice3 [1, 2, 3]).all fun c => constructOK (mkBlocks c.1 c.2) true) = true := by decide +kernel
theorem constructPostdomtree_lower : (lower3.all fun c => constructOK (mkBlocks c.1 c.2) true) = true := by decide +kernel
theorem constructPostdomtree_branch : (branchCFGs.all fun c => constructOK (mkBlocks c.1 c.2) true) = true := by decide +kernel

theorem constructPostdomtreeSmall_proven : ConstructPostdomtreeSmall :=
  smallCFGs_of_slices (fun c => constructOK (mkBlocks c.1 c.2) true) constructPostdomtree_12
    constructPostdomtree_3_0 constructPostdomtree_3_1 constructPostdomtree_3_2 constructPostdomtree_3_3 constructPostdomtree_3_4 constructPostdomtree_3_5 constructPostdomtree_3_6 constructPostdomtree_3_7 constructPostdomtree_lower constructPostdomtree_branch

end JuliaLean.Proofs.Compiler.src.ssair.domtree
