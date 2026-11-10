import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 105 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_105_0 : semOKPart (cfg3 105) 0 = true := by decide +kernel
theorem sem3p_105_1 : semOKPart (cfg3 105) 1 = true := by decide +kernel
theorem sem3p_105_2 : semOKPart (cfg3 105) 2 = true := by decide +kernel
theorem sem3p_105_3 : semOKPart (cfg3 105) 3 = true := by decide +kernel

theorem sem3c_105 : semOK (cfg3 105) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_105_0 sem3p_105_1 sem3p_105_2 sem3p_105_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
