import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 41 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_41_0 : ssaOKPart (cfg3 41) 0 = true := by decide +kernel
theorem ssa3p_41_1 : ssaOKPart (cfg3 41) 1 = true := by decide +kernel
theorem ssa3p_41_2 : ssaOKPart (cfg3 41) 2 = true := by decide +kernel
theorem ssa3p_41_3 : ssaOKPart (cfg3 41) 3 = true := by decide +kernel

theorem ssa3c_41 : ssaOK (cfg3 41) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_41_0 ssa3p_41_1 ssa3p_41_2 ssa3p_41_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
