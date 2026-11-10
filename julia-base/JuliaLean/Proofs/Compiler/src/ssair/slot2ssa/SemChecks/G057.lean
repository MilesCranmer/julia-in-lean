import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 57 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_57_0 : semOKPart (cfg3 57) 0 = true := by decide +kernel
theorem sem3p_57_1 : semOKPart (cfg3 57) 1 = true := by decide +kernel
theorem sem3p_57_2 : semOKPart (cfg3 57) 2 = true := by decide +kernel
theorem sem3p_57_3 : semOKPart (cfg3 57) 3 = true := by decide +kernel

theorem sem3c_57 : semOK (cfg3 57) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_57_0 sem3p_57_1 sem3p_57_2 sem3p_57_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
