import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 84 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_84_0 : semOKPart (cfg3 84) 0 = true := by decide +kernel
theorem sem3p_84_1 : semOKPart (cfg3 84) 1 = true := by decide +kernel
theorem sem3p_84_2 : semOKPart (cfg3 84) 2 = true := by decide +kernel
theorem sem3p_84_3 : semOKPart (cfg3 84) 3 = true := by decide +kernel

theorem sem3c_84 : semOK (cfg3 84) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_84_0 sem3p_84_1 sem3p_84_2 sem3p_84_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
