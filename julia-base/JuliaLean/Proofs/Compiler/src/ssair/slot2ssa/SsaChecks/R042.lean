import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 42 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_42_0 : ssaOKPart (cfg3 42) 0 = true := by decide +kernel
theorem ssa3p_42_1 : ssaOKPart (cfg3 42) 1 = true := by decide +kernel
theorem ssa3p_42_2 : ssaOKPart (cfg3 42) 2 = true := by decide +kernel
theorem ssa3p_42_3 : ssaOKPart (cfg3 42) 3 = true := by decide +kernel

theorem ssa3c_42 : ssaOK (cfg3 42) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_42_0 ssa3p_42_1 ssa3p_42_2 ssa3p_42_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
