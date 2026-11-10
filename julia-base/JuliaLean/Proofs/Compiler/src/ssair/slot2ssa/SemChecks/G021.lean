import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 21 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_21_0 : semOKPart (cfg3 21) 0 = true := by decide +kernel
theorem sem3p_21_1 : semOKPart (cfg3 21) 1 = true := by decide +kernel
theorem sem3p_21_2 : semOKPart (cfg3 21) 2 = true := by decide +kernel
theorem sem3p_21_3 : semOKPart (cfg3 21) 3 = true := by decide +kernel

theorem sem3c_21 : semOK (cfg3 21) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_21_0 sem3p_21_1 sem3p_21_2 sem3p_21_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
