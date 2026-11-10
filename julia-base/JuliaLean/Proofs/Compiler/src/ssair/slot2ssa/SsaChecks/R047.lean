import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 47 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_47_0 : ssaOKPart (cfg3 47) 0 = true := by decide +kernel
theorem ssa3p_47_1 : ssaOKPart (cfg3 47) 1 = true := by decide +kernel
theorem ssa3p_47_2 : ssaOKPart (cfg3 47) 2 = true := by decide +kernel
theorem ssa3p_47_3 : ssaOKPart (cfg3 47) 3 = true := by decide +kernel

theorem ssa3c_47 : ssaOK (cfg3 47) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_47_0 ssa3p_47_1 ssa3p_47_2 ssa3p_47_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
