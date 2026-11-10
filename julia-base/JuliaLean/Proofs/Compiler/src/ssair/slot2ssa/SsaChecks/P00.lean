import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Common

/-! Kernel checks of `ssaOK` on the 3-block lowered-code CFGs 1 to 8 of `juliaCFGs 3`. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa_3_0 : (((juliaCFGs 3).drop 0).take 2).all ssaOK = true := by
  decide +kernel
theorem ssa_3_2 : (((juliaCFGs 3).drop 2).take 2).all ssaOK = true := by
  decide +kernel
theorem ssa_3_4 : (((juliaCFGs 3).drop 4).take 2).all ssaOK = true := by
  decide +kernel
theorem ssa_3_6 : (((juliaCFGs 3).drop 6).take 2).all ssaOK = true := by
  decide +kernel

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
