import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 45 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_45_0 : ssaOKPart (cfg3 45) 0 = true := by decide +kernel
theorem ssa3p_45_1 : ssaOKPart (cfg3 45) 1 = true := by decide +kernel
theorem ssa3p_45_2 : ssaOKPart (cfg3 45) 2 = true := by decide +kernel
theorem ssa3p_45_3 : ssaOKPart (cfg3 45) 3 = true := by decide +kernel

theorem ssa3c_45 : ssaOK (cfg3 45) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_45_0 ssa3p_45_1 ssa3p_45_2 ssa3p_45_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
