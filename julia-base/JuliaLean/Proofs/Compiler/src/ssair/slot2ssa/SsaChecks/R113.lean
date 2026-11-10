import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 113 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_113_0 : ssaOKPart (cfg3 113) 0 = true := by decide +kernel
theorem ssa3p_113_1 : ssaOKPart (cfg3 113) 1 = true := by decide +kernel
theorem ssa3p_113_2 : ssaOKPart (cfg3 113) 2 = true := by decide +kernel
theorem ssa3p_113_3 : ssaOKPart (cfg3 113) 3 = true := by decide +kernel

theorem ssa3c_113 : ssaOK (cfg3 113) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_113_0 ssa3p_113_1 ssa3p_113_2 ssa3p_113_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
