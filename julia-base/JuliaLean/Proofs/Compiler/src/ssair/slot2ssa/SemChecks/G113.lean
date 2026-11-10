import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 113 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_113_0 : semOKPart (cfg3 113) 0 = true := by decide +kernel
theorem sem3p_113_1 : semOKPart (cfg3 113) 1 = true := by decide +kernel
theorem sem3p_113_2 : semOKPart (cfg3 113) 2 = true := by decide +kernel
theorem sem3p_113_3 : semOKPart (cfg3 113) 3 = true := by decide +kernel

theorem sem3c_113 : semOK (cfg3 113) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_113_0 sem3p_113_1 sem3p_113_2 sem3p_113_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
