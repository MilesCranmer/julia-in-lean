import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 66 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_66_0 : ssaOKPart (cfg3 66) 0 = true := by decide +kernel
theorem ssa3p_66_1 : ssaOKPart (cfg3 66) 1 = true := by decide +kernel
theorem ssa3p_66_2 : ssaOKPart (cfg3 66) 2 = true := by decide +kernel
theorem ssa3p_66_3 : ssaOKPart (cfg3 66) 3 = true := by decide +kernel

theorem ssa3c_66 : ssaOK (cfg3 66) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_66_0 ssa3p_66_1 ssa3p_66_2 ssa3p_66_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
