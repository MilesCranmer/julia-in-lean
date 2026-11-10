import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 123 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_123_0 : semOKPart (cfg3 123) 0 = true := by decide +kernel
theorem sem3p_123_1 : semOKPart (cfg3 123) 1 = true := by decide +kernel
theorem sem3p_123_2 : semOKPart (cfg3 123) 2 = true := by decide +kernel
theorem sem3p_123_3 : semOKPart (cfg3 123) 3 = true := by decide +kernel

theorem sem3c_123 : semOK (cfg3 123) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_123_0 sem3p_123_1 sem3p_123_2 sem3p_123_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
