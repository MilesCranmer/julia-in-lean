import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 120 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_120_0 : ssaOKPart (cfg3 120) 0 = true := by decide +kernel
theorem ssa3p_120_1 : ssaOKPart (cfg3 120) 1 = true := by decide +kernel
theorem ssa3p_120_2 : ssaOKPart (cfg3 120) 2 = true := by decide +kernel
theorem ssa3p_120_3 : ssaOKPart (cfg3 120) 3 = true := by decide +kernel

theorem ssa3c_120 : ssaOK (cfg3 120) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_120_0 ssa3p_120_1 ssa3p_120_2 ssa3p_120_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
