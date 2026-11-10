import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Common

/-! Kernel checks of `ssaOK` on the 3-block lowered-code CFGs 9 to 16 of `juliaCFGs 3`. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa_3_8 : (((juliaCFGs 3).drop 8).take 2).all ssaOK = true := by
  decide +kernel
theorem ssa_3_10 : (((juliaCFGs 3).drop 10).take 2).all ssaOK = true := by
  decide +kernel
theorem ssa_3_12 : (((juliaCFGs 3).drop 12).take 2).all ssaOK = true := by
  decide +kernel
theorem ssa_3_14 : (((juliaCFGs 3).drop 14).take 2).all ssaOK = true := by
  decide +kernel

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
