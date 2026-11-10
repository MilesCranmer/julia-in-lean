import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 75 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_75_0 : ssaOKPart (cfg3 75) 0 = true := by decide +kernel
theorem ssa3p_75_1 : ssaOKPart (cfg3 75) 1 = true := by decide +kernel
theorem ssa3p_75_2 : ssaOKPart (cfg3 75) 2 = true := by decide +kernel
theorem ssa3p_75_3 : ssaOKPart (cfg3 75) 3 = true := by decide +kernel

theorem ssa3c_75 : ssaOK (cfg3 75) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_75_0 ssa3p_75_1 ssa3p_75_2 ssa3p_75_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
