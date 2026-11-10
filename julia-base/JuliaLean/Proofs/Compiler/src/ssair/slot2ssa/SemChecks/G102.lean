import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 102 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_102_0 : semOKPart (cfg3 102) 0 = true := by decide +kernel
theorem sem3p_102_1 : semOKPart (cfg3 102) 1 = true := by decide +kernel
theorem sem3p_102_2 : semOKPart (cfg3 102) 2 = true := by decide +kernel
theorem sem3p_102_3 : semOKPart (cfg3 102) 3 = true := by decide +kernel

theorem sem3c_102 : semOK (cfg3 102) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_102_0 sem3p_102_1 sem3p_102_2 sem3p_102_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
