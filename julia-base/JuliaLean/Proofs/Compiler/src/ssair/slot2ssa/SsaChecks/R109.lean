import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 109 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_109_0 : ssaOKPart (cfg3 109) 0 = true := by decide +kernel
theorem ssa3p_109_1 : ssaOKPart (cfg3 109) 1 = true := by decide +kernel
theorem ssa3p_109_2 : ssaOKPart (cfg3 109) 2 = true := by decide +kernel
theorem ssa3p_109_3 : ssaOKPart (cfg3 109) 3 = true := by decide +kernel

theorem ssa3c_109 : ssaOK (cfg3 109) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_109_0 ssa3p_109_1 ssa3p_109_2 ssa3p_109_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
