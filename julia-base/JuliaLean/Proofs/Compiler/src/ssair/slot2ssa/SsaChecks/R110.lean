import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 110 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_110_0 : ssaOKPart (cfg3 110) 0 = true := by decide +kernel
theorem ssa3p_110_1 : ssaOKPart (cfg3 110) 1 = true := by decide +kernel
theorem ssa3p_110_2 : ssaOKPart (cfg3 110) 2 = true := by decide +kernel
theorem ssa3p_110_3 : ssaOKPart (cfg3 110) 3 = true := by decide +kernel

theorem ssa3c_110 : ssaOK (cfg3 110) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_110_0 ssa3p_110_1 ssa3p_110_2 ssa3p_110_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
