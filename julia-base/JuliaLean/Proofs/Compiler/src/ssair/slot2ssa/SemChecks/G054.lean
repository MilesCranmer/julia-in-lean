import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 54 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_54_0 : semOKPart (cfg3 54) 0 = true := by decide +kernel
theorem sem3p_54_1 : semOKPart (cfg3 54) 1 = true := by decide +kernel
theorem sem3p_54_2 : semOKPart (cfg3 54) 2 = true := by decide +kernel
theorem sem3p_54_3 : semOKPart (cfg3 54) 3 = true := by decide +kernel

theorem sem3c_54 : semOK (cfg3 54) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_54_0 sem3p_54_1 sem3p_54_2 sem3p_54_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
