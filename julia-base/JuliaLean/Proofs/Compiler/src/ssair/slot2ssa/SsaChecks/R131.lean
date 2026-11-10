import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 131 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_131_0 : ssaOKPart (cfg3 131) 0 = true := by decide +kernel
theorem ssa3p_131_1 : ssaOKPart (cfg3 131) 1 = true := by decide +kernel
theorem ssa3p_131_2 : ssaOKPart (cfg3 131) 2 = true := by decide +kernel
theorem ssa3p_131_3 : ssaOKPart (cfg3 131) 3 = true := by decide +kernel

theorem ssa3c_131 : ssaOK (cfg3 131) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_131_0 ssa3p_131_1 ssa3p_131_2 ssa3p_131_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
