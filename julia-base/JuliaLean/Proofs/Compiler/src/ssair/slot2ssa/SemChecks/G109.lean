import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 109 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_109_0 : semOKPart (cfg3 109) 0 = true := by decide +kernel
theorem sem3p_109_1 : semOKPart (cfg3 109) 1 = true := by decide +kernel
theorem sem3p_109_2 : semOKPart (cfg3 109) 2 = true := by decide +kernel
theorem sem3p_109_3 : semOKPart (cfg3 109) 3 = true := by decide +kernel

theorem sem3c_109 : semOK (cfg3 109) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_109_0 sem3p_109_1 sem3p_109_2 sem3p_109_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
