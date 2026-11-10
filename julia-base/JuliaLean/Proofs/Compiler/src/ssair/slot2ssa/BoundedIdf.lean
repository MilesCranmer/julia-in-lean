import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.Props

/-! Exhaustive kernel evaluation of `IdfSmall` over `cfgsUpTo3`, one slice at a time so that
each kernel check stays small. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem idf_12 : (smallCFGs12.all fun c => idfOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem idf_3_0 : ((slice3 []).all fun c => idfOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem idf_3_1 : ((slice3 [3]).all fun c => idfOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem idf_3_2 : ((slice3 [2]).all fun c => idfOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem idf_3_3 : ((slice3 [2, 3]).all fun c => idfOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem idf_3_4 : ((slice3 [1]).all fun c => idfOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem idf_3_5 : ((slice3 [1, 3]).all fun c => idfOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem idf_3_6 : ((slice3 [1, 2]).all fun c => idfOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem idf_3_7 : ((slice3 [1, 2, 3]).all fun c => idfOK (mkBlocks c.1 c.2)) = true := by decide +kernel
theorem idf_lower : (lower3.all fun c => idfOK (mkBlocks c.1 c.2)) = true := by decide +kernel

theorem idfSmall_proven : IdfSmall :=
  cfgsUpTo3_of_slices (fun c => idfOK (mkBlocks c.1 c.2)) idf_12
    idf_3_0 idf_3_1 idf_3_2 idf_3_3 idf_3_4 idf_3_5 idf_3_6 idf_3_7 idf_lower

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
