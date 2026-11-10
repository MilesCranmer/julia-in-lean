import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 143 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_143_0 : ssaOKPart (cfg3 143) 0 = true := by decide +kernel
theorem ssa3p_143_1 : ssaOKPart (cfg3 143) 1 = true := by decide +kernel
theorem ssa3p_143_2 : ssaOKPart (cfg3 143) 2 = true := by decide +kernel
theorem ssa3p_143_3 : ssaOKPart (cfg3 143) 3 = true := by decide +kernel

theorem ssa3c_143 : ssaOK (cfg3 143) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_143_0 ssa3p_143_1 ssa3p_143_2 ssa3p_143_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
