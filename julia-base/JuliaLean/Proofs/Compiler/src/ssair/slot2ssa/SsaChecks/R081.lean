import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 81 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_81_0 : ssaOKPart (cfg3 81) 0 = true := by decide +kernel
theorem ssa3p_81_1 : ssaOKPart (cfg3 81) 1 = true := by decide +kernel
theorem ssa3p_81_2 : ssaOKPart (cfg3 81) 2 = true := by decide +kernel
theorem ssa3p_81_3 : ssaOKPart (cfg3 81) 3 = true := by decide +kernel

theorem ssa3c_81 : ssaOK (cfg3 81) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_81_0 ssa3p_81_1 ssa3p_81_2 ssa3p_81_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
