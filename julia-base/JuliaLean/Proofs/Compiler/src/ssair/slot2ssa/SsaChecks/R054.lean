import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 54 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_54_0 : ssaOKPart (cfg3 54) 0 = true := by decide +kernel
theorem ssa3p_54_1 : ssaOKPart (cfg3 54) 1 = true := by decide +kernel
theorem ssa3p_54_2 : ssaOKPart (cfg3 54) 2 = true := by decide +kernel
theorem ssa3p_54_3 : ssaOKPart (cfg3 54) 3 = true := by decide +kernel

theorem ssa3c_54 : ssaOK (cfg3 54) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_54_0 ssa3p_54_1 ssa3p_54_2 ssa3p_54_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
