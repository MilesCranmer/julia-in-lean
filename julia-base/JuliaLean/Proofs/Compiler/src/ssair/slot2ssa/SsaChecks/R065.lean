import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 65 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_65_0 : ssaOKPart (cfg3 65) 0 = true := by decide +kernel
theorem ssa3p_65_1 : ssaOKPart (cfg3 65) 1 = true := by decide +kernel
theorem ssa3p_65_2 : ssaOKPart (cfg3 65) 2 = true := by decide +kernel
theorem ssa3p_65_3 : ssaOKPart (cfg3 65) 3 = true := by decide +kernel

theorem ssa3c_65 : ssaOK (cfg3 65) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_65_0 ssa3p_65_1 ssa3p_65_2 ssa3p_65_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
