import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 31 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_31_0 : semOKPart (cfg3 31) 0 = true := by decide +kernel
theorem sem3p_31_1 : semOKPart (cfg3 31) 1 = true := by decide +kernel
theorem sem3p_31_2 : semOKPart (cfg3 31) 2 = true := by decide +kernel
theorem sem3p_31_3 : semOKPart (cfg3 31) 3 = true := by decide +kernel

theorem sem3c_31 : semOK (cfg3 31) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_31_0 sem3p_31_1 sem3p_31_2 sem3p_31_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
