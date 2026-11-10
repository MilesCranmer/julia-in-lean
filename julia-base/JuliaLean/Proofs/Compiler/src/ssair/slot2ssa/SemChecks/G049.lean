import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 49 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_49_0 : semOKPart (cfg3 49) 0 = true := by decide +kernel
theorem sem3p_49_1 : semOKPart (cfg3 49) 1 = true := by decide +kernel
theorem sem3p_49_2 : semOKPart (cfg3 49) 2 = true := by decide +kernel
theorem sem3p_49_3 : semOKPart (cfg3 49) 3 = true := by decide +kernel

theorem sem3c_49 : semOK (cfg3 49) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_49_0 sem3p_49_1 sem3p_49_2 sem3p_49_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
