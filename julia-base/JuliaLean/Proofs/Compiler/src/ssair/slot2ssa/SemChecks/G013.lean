import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 13 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_13_0 : semOKPart (cfg3 13) 0 = true := by decide +kernel
theorem sem3p_13_1 : semOKPart (cfg3 13) 1 = true := by decide +kernel
theorem sem3p_13_2 : semOKPart (cfg3 13) 2 = true := by decide +kernel
theorem sem3p_13_3 : semOKPart (cfg3 13) 3 = true := by decide +kernel

theorem sem3c_13 : semOK (cfg3 13) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_13_0 sem3p_13_1 sem3p_13_2 sem3p_13_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
