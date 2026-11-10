import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 124 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_124_0 : ssaOKPart (cfg3 124) 0 = true := by decide +kernel
theorem ssa3p_124_1 : ssaOKPart (cfg3 124) 1 = true := by decide +kernel
theorem ssa3p_124_2 : ssaOKPart (cfg3 124) 2 = true := by decide +kernel
theorem ssa3p_124_3 : ssaOKPart (cfg3 124) 3 = true := by decide +kernel

theorem ssa3c_124 : ssaOK (cfg3 124) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_124_0 ssa3p_124_1 ssa3p_124_2 ssa3p_124_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
