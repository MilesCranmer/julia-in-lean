import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 105 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_105_0 : ssaOKPart (cfg3 105) 0 = true := by decide +kernel
theorem ssa3p_105_1 : ssaOKPart (cfg3 105) 1 = true := by decide +kernel
theorem ssa3p_105_2 : ssaOKPart (cfg3 105) 2 = true := by decide +kernel
theorem ssa3p_105_3 : ssaOKPart (cfg3 105) 3 = true := by decide +kernel

theorem ssa3c_105 : ssaOK (cfg3 105) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_105_0 ssa3p_105_1 ssa3p_105_2 ssa3p_105_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
