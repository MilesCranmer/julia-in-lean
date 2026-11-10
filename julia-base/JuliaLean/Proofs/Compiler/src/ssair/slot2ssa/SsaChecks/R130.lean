import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 130 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_130_0 : ssaOKPart (cfg3 130) 0 = true := by decide +kernel
theorem ssa3p_130_1 : ssaOKPart (cfg3 130) 1 = true := by decide +kernel
theorem ssa3p_130_2 : ssaOKPart (cfg3 130) 2 = true := by decide +kernel
theorem ssa3p_130_3 : ssaOKPart (cfg3 130) 3 = true := by decide +kernel

theorem ssa3c_130 : ssaOK (cfg3 130) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_130_0 ssa3p_130_1 ssa3p_130_2 ssa3p_130_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
