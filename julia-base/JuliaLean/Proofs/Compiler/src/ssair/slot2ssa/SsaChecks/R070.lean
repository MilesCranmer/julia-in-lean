import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 70 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_70_0 : ssaOKPart (cfg3 70) 0 = true := by decide +kernel
theorem ssa3p_70_1 : ssaOKPart (cfg3 70) 1 = true := by decide +kernel
theorem ssa3p_70_2 : ssaOKPart (cfg3 70) 2 = true := by decide +kernel
theorem ssa3p_70_3 : ssaOKPart (cfg3 70) 3 = true := by decide +kernel

theorem ssa3c_70 : ssaOK (cfg3 70) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_70_0 ssa3p_70_1 ssa3p_70_2 ssa3p_70_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
