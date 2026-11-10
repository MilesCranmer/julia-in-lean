import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 8 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_8_0 : semOKPart (cfg3 8) 0 = true := by decide +kernel
theorem sem3p_8_1 : semOKPart (cfg3 8) 1 = true := by decide +kernel
theorem sem3p_8_2 : semOKPart (cfg3 8) 2 = true := by decide +kernel
theorem sem3p_8_3 : semOKPart (cfg3 8) 3 = true := by decide +kernel

theorem sem3c_8 : semOK (cfg3 8) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_8_0 sem3p_8_1 sem3p_8_2 sem3p_8_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
