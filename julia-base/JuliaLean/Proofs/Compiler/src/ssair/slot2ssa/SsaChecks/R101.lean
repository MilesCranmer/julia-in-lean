import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 101 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_101_0 : ssaOKPart (cfg3 101) 0 = true := by decide +kernel
theorem ssa3p_101_1 : ssaOKPart (cfg3 101) 1 = true := by decide +kernel
theorem ssa3p_101_2 : ssaOKPart (cfg3 101) 2 = true := by decide +kernel
theorem ssa3p_101_3 : ssaOKPart (cfg3 101) 3 = true := by decide +kernel

theorem ssa3c_101 : ssaOK (cfg3 101) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_101_0 ssa3p_101_1 ssa3p_101_2 ssa3p_101_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
