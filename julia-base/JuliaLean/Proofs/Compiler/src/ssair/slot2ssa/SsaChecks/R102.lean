import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 102 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_102_0 : ssaOKPart (cfg3 102) 0 = true := by decide +kernel
theorem ssa3p_102_1 : ssaOKPart (cfg3 102) 1 = true := by decide +kernel
theorem ssa3p_102_2 : ssaOKPart (cfg3 102) 2 = true := by decide +kernel
theorem ssa3p_102_3 : ssaOKPart (cfg3 102) 3 = true := by decide +kernel

theorem ssa3c_102 : ssaOK (cfg3 102) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_102_0 ssa3p_102_1 ssa3p_102_2 ssa3p_102_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
