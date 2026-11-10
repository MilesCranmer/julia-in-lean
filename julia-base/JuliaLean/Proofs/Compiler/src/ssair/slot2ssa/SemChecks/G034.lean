import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 34 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_34_0 : semOKPart (cfg3 34) 0 = true := by decide +kernel
theorem sem3p_34_1 : semOKPart (cfg3 34) 1 = true := by decide +kernel
theorem sem3p_34_2 : semOKPart (cfg3 34) 2 = true := by decide +kernel
theorem sem3p_34_3 : semOKPart (cfg3 34) 3 = true := by decide +kernel

theorem sem3c_34 : semOK (cfg3 34) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_34_0 sem3p_34_1 sem3p_34_2 sem3p_34_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
