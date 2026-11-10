import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 42 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_42_0 : semOKPart (cfg3 42) 0 = true := by decide +kernel
theorem sem3p_42_1 : semOKPart (cfg3 42) 1 = true := by decide +kernel
theorem sem3p_42_2 : semOKPart (cfg3 42) 2 = true := by decide +kernel
theorem sem3p_42_3 : semOKPart (cfg3 42) 3 = true := by decide +kernel

theorem sem3c_42 : semOK (cfg3 42) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_42_0 sem3p_42_1 sem3p_42_2 sem3p_42_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
