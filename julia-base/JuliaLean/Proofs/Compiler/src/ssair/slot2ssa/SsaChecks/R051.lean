import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 51 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_51_0 : ssaOKPart (cfg3 51) 0 = true := by decide +kernel
theorem ssa3p_51_1 : ssaOKPart (cfg3 51) 1 = true := by decide +kernel
theorem ssa3p_51_2 : ssaOKPart (cfg3 51) 2 = true := by decide +kernel
theorem ssa3p_51_3 : ssaOKPart (cfg3 51) 3 = true := by decide +kernel

theorem ssa3c_51 : ssaOK (cfg3 51) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_51_0 ssa3p_51_1 ssa3p_51_2 ssa3p_51_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
