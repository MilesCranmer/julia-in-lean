import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 130 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_130_0 : semOKPart (cfg3 130) 0 = true := by decide +kernel
theorem sem3p_130_1 : semOKPart (cfg3 130) 1 = true := by decide +kernel
theorem sem3p_130_2 : semOKPart (cfg3 130) 2 = true := by decide +kernel
theorem sem3p_130_3 : semOKPart (cfg3 130) 3 = true := by decide +kernel

theorem sem3c_130 : semOK (cfg3 130) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_130_0 sem3p_130_1 sem3p_130_2 sem3p_130_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
