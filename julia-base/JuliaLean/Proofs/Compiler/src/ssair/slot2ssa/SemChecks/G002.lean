import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 2 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_2_0 : semOKPart (cfg3 2) 0 = true := by decide +kernel
theorem sem3p_2_1 : semOKPart (cfg3 2) 1 = true := by decide +kernel
theorem sem3p_2_2 : semOKPart (cfg3 2) 2 = true := by decide +kernel
theorem sem3p_2_3 : semOKPart (cfg3 2) 3 = true := by decide +kernel

theorem sem3c_2 : semOK (cfg3 2) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_2_0 sem3p_2_1 sem3p_2_2 sem3p_2_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
