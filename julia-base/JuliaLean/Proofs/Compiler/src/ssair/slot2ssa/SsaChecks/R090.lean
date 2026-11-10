import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 90 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_90_0 : ssaOKPart (cfg3 90) 0 = true := by decide +kernel
theorem ssa3p_90_1 : ssaOKPart (cfg3 90) 1 = true := by decide +kernel
theorem ssa3p_90_2 : ssaOKPart (cfg3 90) 2 = true := by decide +kernel
theorem ssa3p_90_3 : ssaOKPart (cfg3 90) 3 = true := by decide +kernel

theorem ssa3c_90 : ssaOK (cfg3 90) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_90_0 ssa3p_90_1 ssa3p_90_2 ssa3p_90_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
