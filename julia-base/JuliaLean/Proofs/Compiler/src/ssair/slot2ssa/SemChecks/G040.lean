import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 40 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_40_0 : semOKPart (cfg3 40) 0 = true := by decide +kernel
theorem sem3p_40_1 : semOKPart (cfg3 40) 1 = true := by decide +kernel
theorem sem3p_40_2 : semOKPart (cfg3 40) 2 = true := by decide +kernel
theorem sem3p_40_3 : semOKPart (cfg3 40) 3 = true := by decide +kernel

theorem sem3c_40 : semOK (cfg3 40) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_40_0 sem3p_40_1 sem3p_40_2 sem3p_40_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
