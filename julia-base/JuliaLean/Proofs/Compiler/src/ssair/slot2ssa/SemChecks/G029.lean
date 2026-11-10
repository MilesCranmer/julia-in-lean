import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 29 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_29_0 : semOKPart (cfg3 29) 0 = true := by decide +kernel
theorem sem3p_29_1 : semOKPart (cfg3 29) 1 = true := by decide +kernel
theorem sem3p_29_2 : semOKPart (cfg3 29) 2 = true := by decide +kernel
theorem sem3p_29_3 : semOKPart (cfg3 29) 3 = true := by decide +kernel

theorem sem3c_29 : semOK (cfg3 29) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_29_0 sem3p_29_1 sem3p_29_2 sem3p_29_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
