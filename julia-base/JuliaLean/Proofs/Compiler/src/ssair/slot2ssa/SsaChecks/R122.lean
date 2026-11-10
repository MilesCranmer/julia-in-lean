import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 122 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_122_0 : ssaOKPart (cfg3 122) 0 = true := by decide +kernel
theorem ssa3p_122_1 : ssaOKPart (cfg3 122) 1 = true := by decide +kernel
theorem ssa3p_122_2 : ssaOKPart (cfg3 122) 2 = true := by decide +kernel
theorem ssa3p_122_3 : ssaOKPart (cfg3 122) 3 = true := by decide +kernel

theorem ssa3c_122 : ssaOK (cfg3 122) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_122_0 ssa3p_122_1 ssa3p_122_2 ssa3p_122_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
