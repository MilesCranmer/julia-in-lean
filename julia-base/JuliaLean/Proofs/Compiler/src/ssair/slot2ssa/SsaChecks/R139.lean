import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 139 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_139_0 : ssaOKPart (cfg3 139) 0 = true := by decide +kernel
theorem ssa3p_139_1 : ssaOKPart (cfg3 139) 1 = true := by decide +kernel
theorem ssa3p_139_2 : ssaOKPart (cfg3 139) 2 = true := by decide +kernel
theorem ssa3p_139_3 : ssaOKPart (cfg3 139) 3 = true := by decide +kernel

theorem ssa3c_139 : ssaOK (cfg3 139) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_139_0 ssa3p_139_1 ssa3p_139_2 ssa3p_139_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
