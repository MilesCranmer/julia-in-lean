import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 3 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_3_0 : semOKPart (cfg3 3) 0 = true := by decide +kernel
theorem sem3p_3_1 : semOKPart (cfg3 3) 1 = true := by decide +kernel
theorem sem3p_3_2 : semOKPart (cfg3 3) 2 = true := by decide +kernel
theorem sem3p_3_3 : semOKPart (cfg3 3) 3 = true := by decide +kernel

theorem sem3c_3 : semOK (cfg3 3) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_3_0 sem3p_3_1 sem3p_3_2 sem3p_3_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
