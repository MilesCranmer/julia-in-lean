import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 84 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_84_0 : ssaOKPart (cfg3 84) 0 = true := by decide +kernel
theorem ssa3p_84_1 : ssaOKPart (cfg3 84) 1 = true := by decide +kernel
theorem ssa3p_84_2 : ssaOKPart (cfg3 84) 2 = true := by decide +kernel
theorem ssa3p_84_3 : ssaOKPart (cfg3 84) 3 = true := by decide +kernel

theorem ssa3c_84 : ssaOK (cfg3 84) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_84_0 ssa3p_84_1 ssa3p_84_2 ssa3p_84_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
