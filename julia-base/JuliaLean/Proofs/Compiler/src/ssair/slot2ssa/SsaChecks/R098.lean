import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 98 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_98_0 : ssaOKPart (cfg3 98) 0 = true := by decide +kernel
theorem ssa3p_98_1 : ssaOKPart (cfg3 98) 1 = true := by decide +kernel
theorem ssa3p_98_2 : ssaOKPart (cfg3 98) 2 = true := by decide +kernel
theorem ssa3p_98_3 : ssaOKPart (cfg3 98) 3 = true := by decide +kernel

theorem ssa3c_98 : ssaOK (cfg3 98) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_98_0 ssa3p_98_1 ssa3p_98_2 ssa3p_98_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
