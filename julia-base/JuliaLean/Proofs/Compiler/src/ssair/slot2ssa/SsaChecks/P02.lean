import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Common

/-! Kernel checks of `ssaOK` on the 3-block lowered-code CFGs 17 to 24 of `juliaCFGs 3`. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa_3_16 : (((juliaCFGs 3).drop 16).take 2).all ssaOK = true := by
  decide +kernel
theorem ssa_3_18 : (((juliaCFGs 3).drop 18).take 2).all ssaOK = true := by
  decide +kernel
theorem ssa_3_20 : (((juliaCFGs 3).drop 20).take 2).all ssaOK = true := by
  decide +kernel
theorem ssa_3_22 : (((juliaCFGs 3).drop 22).take 2).all ssaOK = true := by
  decide +kernel

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
