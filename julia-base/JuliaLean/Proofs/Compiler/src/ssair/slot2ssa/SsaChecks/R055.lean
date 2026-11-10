import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 55 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_55_0 : ssaOKPart (cfg3 55) 0 = true := by decide +kernel
theorem ssa3p_55_1 : ssaOKPart (cfg3 55) 1 = true := by decide +kernel
theorem ssa3p_55_2 : ssaOKPart (cfg3 55) 2 = true := by decide +kernel
theorem ssa3p_55_3 : ssaOKPart (cfg3 55) 3 = true := by decide +kernel

theorem ssa3c_55 : ssaOK (cfg3 55) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_55_0 ssa3p_55_1 ssa3p_55_2 ssa3p_55_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
