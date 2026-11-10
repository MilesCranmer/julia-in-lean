import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 72 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_72_0 : ssaOKPart (cfg3 72) 0 = true := by decide +kernel
theorem ssa3p_72_1 : ssaOKPart (cfg3 72) 1 = true := by decide +kernel
theorem ssa3p_72_2 : ssaOKPart (cfg3 72) 2 = true := by decide +kernel
theorem ssa3p_72_3 : ssaOKPart (cfg3 72) 3 = true := by decide +kernel

theorem ssa3c_72 : ssaOK (cfg3 72) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_72_0 ssa3p_72_1 ssa3p_72_2 ssa3p_72_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
