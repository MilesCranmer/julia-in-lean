import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 46 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_46_0 : ssaOKPart (cfg3 46) 0 = true := by decide +kernel
theorem ssa3p_46_1 : ssaOKPart (cfg3 46) 1 = true := by decide +kernel
theorem ssa3p_46_2 : ssaOKPart (cfg3 46) 2 = true := by decide +kernel
theorem ssa3p_46_3 : ssaOKPart (cfg3 46) 3 = true := by decide +kernel

theorem ssa3c_46 : ssaOK (cfg3 46) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_46_0 ssa3p_46_1 ssa3p_46_2 ssa3p_46_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
