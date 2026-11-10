import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 111 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_111_0 : semOKPart (cfg3 111) 0 = true := by decide +kernel
theorem sem3p_111_1 : semOKPart (cfg3 111) 1 = true := by decide +kernel
theorem sem3p_111_2 : semOKPart (cfg3 111) 2 = true := by decide +kernel
theorem sem3p_111_3 : semOKPart (cfg3 111) 3 = true := by decide +kernel

theorem sem3c_111 : semOK (cfg3 111) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_111_0 sem3p_111_1 sem3p_111_2 sem3p_111_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
