import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 125 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_125_0 : ssaOKPart (cfg3 125) 0 = true := by decide +kernel
theorem ssa3p_125_1 : ssaOKPart (cfg3 125) 1 = true := by decide +kernel
theorem ssa3p_125_2 : ssaOKPart (cfg3 125) 2 = true := by decide +kernel
theorem ssa3p_125_3 : ssaOKPart (cfg3 125) 3 = true := by decide +kernel

theorem ssa3c_125 : ssaOK (cfg3 125) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_125_0 ssa3p_125_1 ssa3p_125_2 ssa3p_125_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
