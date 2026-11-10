import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 135 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_135_0 : ssaOKPart (cfg3 135) 0 = true := by decide +kernel
theorem ssa3p_135_1 : ssaOKPart (cfg3 135) 1 = true := by decide +kernel
theorem ssa3p_135_2 : ssaOKPart (cfg3 135) 2 = true := by decide +kernel
theorem ssa3p_135_3 : ssaOKPart (cfg3 135) 3 = true := by decide +kernel

theorem ssa3c_135 : ssaOK (cfg3 135) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_135_0 ssa3p_135_1 ssa3p_135_2 ssa3p_135_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
