import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 49 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_49_0 : ssaOKPart (cfg3 49) 0 = true := by decide +kernel
theorem ssa3p_49_1 : ssaOKPart (cfg3 49) 1 = true := by decide +kernel
theorem ssa3p_49_2 : ssaOKPart (cfg3 49) 2 = true := by decide +kernel
theorem ssa3p_49_3 : ssaOKPart (cfg3 49) 3 = true := by decide +kernel

theorem ssa3c_49 : ssaOK (cfg3 49) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_49_0 ssa3p_49_1 ssa3p_49_2 ssa3p_49_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
