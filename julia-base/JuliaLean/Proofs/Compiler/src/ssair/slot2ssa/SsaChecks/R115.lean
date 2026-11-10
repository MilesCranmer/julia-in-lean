import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 115 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_115_0 : ssaOKPart (cfg3 115) 0 = true := by decide +kernel
theorem ssa3p_115_1 : ssaOKPart (cfg3 115) 1 = true := by decide +kernel
theorem ssa3p_115_2 : ssaOKPart (cfg3 115) 2 = true := by decide +kernel
theorem ssa3p_115_3 : ssaOKPart (cfg3 115) 3 = true := by decide +kernel

theorem ssa3c_115 : ssaOK (cfg3 115) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_115_0 ssa3p_115_1 ssa3p_115_2 ssa3p_115_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
