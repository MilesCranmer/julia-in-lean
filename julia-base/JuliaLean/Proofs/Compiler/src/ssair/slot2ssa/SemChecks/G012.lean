import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 12 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_12_0 : semOKPart (cfg3 12) 0 = true := by decide +kernel
theorem sem3p_12_1 : semOKPart (cfg3 12) 1 = true := by decide +kernel
theorem sem3p_12_2 : semOKPart (cfg3 12) 2 = true := by decide +kernel
theorem sem3p_12_3 : semOKPart (cfg3 12) 3 = true := by decide +kernel

theorem sem3c_12 : semOK (cfg3 12) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_12_0 sem3p_12_1 sem3p_12_2 sem3p_12_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
