import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 9 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_9_0 : semOKPart (cfg3 9) 0 = true := by decide +kernel
theorem sem3p_9_1 : semOKPart (cfg3 9) 1 = true := by decide +kernel
theorem sem3p_9_2 : semOKPart (cfg3 9) 2 = true := by decide +kernel
theorem sem3p_9_3 : semOKPart (cfg3 9) 3 = true := by decide +kernel

theorem sem3c_9 : semOK (cfg3 9) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_9_0 sem3p_9_1 sem3p_9_2 sem3p_9_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
