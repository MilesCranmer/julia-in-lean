import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 66 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_66_0 : semOKPart (cfg3 66) 0 = true := by decide +kernel
theorem sem3p_66_1 : semOKPart (cfg3 66) 1 = true := by decide +kernel
theorem sem3p_66_2 : semOKPart (cfg3 66) 2 = true := by decide +kernel
theorem sem3p_66_3 : semOKPart (cfg3 66) 3 = true := by decide +kernel

theorem sem3c_66 : semOK (cfg3 66) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_66_0 sem3p_66_1 sem3p_66_2 sem3p_66_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
