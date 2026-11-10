import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 36 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_36_0 : semOKPart (cfg3 36) 0 = true := by decide +kernel
theorem sem3p_36_1 : semOKPart (cfg3 36) 1 = true := by decide +kernel
theorem sem3p_36_2 : semOKPart (cfg3 36) 2 = true := by decide +kernel
theorem sem3p_36_3 : semOKPart (cfg3 36) 3 = true := by decide +kernel

theorem sem3c_36 : semOK (cfg3 36) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_36_0 sem3p_36_1 sem3p_36_2 sem3p_36_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
