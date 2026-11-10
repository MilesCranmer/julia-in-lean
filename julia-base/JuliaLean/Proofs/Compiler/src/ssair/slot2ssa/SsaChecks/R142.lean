import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 142 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_142_0 : ssaOKPart (cfg3 142) 0 = true := by decide +kernel
theorem ssa3p_142_1 : ssaOKPart (cfg3 142) 1 = true := by decide +kernel
theorem ssa3p_142_2 : ssaOKPart (cfg3 142) 2 = true := by decide +kernel
theorem ssa3p_142_3 : ssaOKPart (cfg3 142) 3 = true := by decide +kernel

theorem ssa3c_142 : ssaOK (cfg3 142) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_142_0 ssa3p_142_1 ssa3p_142_2 ssa3p_142_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
