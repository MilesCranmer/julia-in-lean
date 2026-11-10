import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 81 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_81_0 : semOKPart (cfg3 81) 0 = true := by decide +kernel
theorem sem3p_81_1 : semOKPart (cfg3 81) 1 = true := by decide +kernel
theorem sem3p_81_2 : semOKPart (cfg3 81) 2 = true := by decide +kernel
theorem sem3p_81_3 : semOKPart (cfg3 81) 3 = true := by decide +kernel

theorem sem3c_81 : semOK (cfg3 81) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_81_0 sem3p_81_1 sem3p_81_2 sem3p_81_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
