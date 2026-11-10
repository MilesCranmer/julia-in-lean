import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 10 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_10_0 : semOKPart (cfg3 10) 0 = true := by decide +kernel
theorem sem3p_10_1 : semOKPart (cfg3 10) 1 = true := by decide +kernel
theorem sem3p_10_2 : semOKPart (cfg3 10) 2 = true := by decide +kernel
theorem sem3p_10_3 : semOKPart (cfg3 10) 3 = true := by decide +kernel

theorem sem3c_10 : semOK (cfg3 10) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_10_0 sem3p_10_1 sem3p_10_2 sem3p_10_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
