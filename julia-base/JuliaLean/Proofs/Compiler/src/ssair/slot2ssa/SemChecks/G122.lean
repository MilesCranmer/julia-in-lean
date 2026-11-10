import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 122 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_122_0 : semOKPart (cfg3 122) 0 = true := by decide +kernel
theorem sem3p_122_1 : semOKPart (cfg3 122) 1 = true := by decide +kernel
theorem sem3p_122_2 : semOKPart (cfg3 122) 2 = true := by decide +kernel
theorem sem3p_122_3 : semOKPart (cfg3 122) 3 = true := by decide +kernel

theorem sem3c_122 : semOK (cfg3 122) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_122_0 sem3p_122_1 sem3p_122_2 sem3p_122_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
