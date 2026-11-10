import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 26 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_26_0 : semOKPart (cfg3 26) 0 = true := by decide +kernel
theorem sem3p_26_1 : semOKPart (cfg3 26) 1 = true := by decide +kernel
theorem sem3p_26_2 : semOKPart (cfg3 26) 2 = true := by decide +kernel
theorem sem3p_26_3 : semOKPart (cfg3 26) 3 = true := by decide +kernel

theorem sem3c_26 : semOK (cfg3 26) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_26_0 sem3p_26_1 sem3p_26_2 sem3p_26_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
