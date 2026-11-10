import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 23 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_23_0 : semOKPart (cfg3 23) 0 = true := by decide +kernel
theorem sem3p_23_1 : semOKPart (cfg3 23) 1 = true := by decide +kernel
theorem sem3p_23_2 : semOKPart (cfg3 23) 2 = true := by decide +kernel
theorem sem3p_23_3 : semOKPart (cfg3 23) 3 = true := by decide +kernel

theorem sem3c_23 : semOK (cfg3 23) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_23_0 sem3p_23_1 sem3p_23_2 sem3p_23_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
