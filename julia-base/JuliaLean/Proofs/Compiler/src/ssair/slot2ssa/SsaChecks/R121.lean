import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 121 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_121_0 : ssaOKPart (cfg3 121) 0 = true := by decide +kernel
theorem ssa3p_121_1 : ssaOKPart (cfg3 121) 1 = true := by decide +kernel
theorem ssa3p_121_2 : ssaOKPart (cfg3 121) 2 = true := by decide +kernel
theorem ssa3p_121_3 : ssaOKPart (cfg3 121) 3 = true := by decide +kernel

theorem ssa3c_121 : ssaOK (cfg3 121) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_121_0 ssa3p_121_1 ssa3p_121_2 ssa3p_121_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
