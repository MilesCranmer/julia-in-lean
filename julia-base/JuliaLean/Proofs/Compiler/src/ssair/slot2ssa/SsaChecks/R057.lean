import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 57 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_57_0 : ssaOKPart (cfg3 57) 0 = true := by decide +kernel
theorem ssa3p_57_1 : ssaOKPart (cfg3 57) 1 = true := by decide +kernel
theorem ssa3p_57_2 : ssaOKPart (cfg3 57) 2 = true := by decide +kernel
theorem ssa3p_57_3 : ssaOKPart (cfg3 57) 3 = true := by decide +kernel

theorem ssa3c_57 : ssaOK (cfg3 57) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_57_0 ssa3p_57_1 ssa3p_57_2 ssa3p_57_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
