import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 124 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_124_0 : semOKPart (cfg3 124) 0 = true := by decide +kernel
theorem sem3p_124_1 : semOKPart (cfg3 124) 1 = true := by decide +kernel
theorem sem3p_124_2 : semOKPart (cfg3 124) 2 = true := by decide +kernel
theorem sem3p_124_3 : semOKPart (cfg3 124) 3 = true := by decide +kernel

theorem sem3c_124 : semOK (cfg3 124) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_124_0 sem3p_124_1 sem3p_124_2 sem3p_124_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
