import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 58 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_58_0 : ssaOKPart (cfg3 58) 0 = true := by decide +kernel
theorem ssa3p_58_1 : ssaOKPart (cfg3 58) 1 = true := by decide +kernel
theorem ssa3p_58_2 : ssaOKPart (cfg3 58) 2 = true := by decide +kernel
theorem ssa3p_58_3 : ssaOKPart (cfg3 58) 3 = true := by decide +kernel

theorem ssa3c_58 : ssaOK (cfg3 58) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_58_0 ssa3p_58_1 ssa3p_58_2 ssa3p_58_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
