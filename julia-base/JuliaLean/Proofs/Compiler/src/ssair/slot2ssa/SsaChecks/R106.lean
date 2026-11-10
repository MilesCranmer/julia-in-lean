import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 106 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_106_0 : ssaOKPart (cfg3 106) 0 = true := by decide +kernel
theorem ssa3p_106_1 : ssaOKPart (cfg3 106) 1 = true := by decide +kernel
theorem ssa3p_106_2 : ssaOKPart (cfg3 106) 2 = true := by decide +kernel
theorem ssa3p_106_3 : ssaOKPart (cfg3 106) 3 = true := by decide +kernel

theorem ssa3c_106 : ssaOK (cfg3 106) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_106_0 ssa3p_106_1 ssa3p_106_2 ssa3p_106_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
