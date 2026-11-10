import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 50 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_50_0 : ssaOKPart (cfg3 50) 0 = true := by decide +kernel
theorem ssa3p_50_1 : ssaOKPart (cfg3 50) 1 = true := by decide +kernel
theorem ssa3p_50_2 : ssaOKPart (cfg3 50) 2 = true := by decide +kernel
theorem ssa3p_50_3 : ssaOKPart (cfg3 50) 3 = true := by decide +kernel

theorem ssa3c_50 : ssaOK (cfg3 50) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_50_0 ssa3p_50_1 ssa3p_50_2 ssa3p_50_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
