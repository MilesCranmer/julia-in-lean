import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 138 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_138_0 : ssaOKPart (cfg3 138) 0 = true := by decide +kernel
theorem ssa3p_138_1 : ssaOKPart (cfg3 138) 1 = true := by decide +kernel
theorem ssa3p_138_2 : ssaOKPart (cfg3 138) 2 = true := by decide +kernel
theorem ssa3p_138_3 : ssaOKPart (cfg3 138) 3 = true := by decide +kernel

theorem ssa3c_138 : ssaOK (cfg3 138) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_138_0 ssa3p_138_1 ssa3p_138_2 ssa3p_138_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
