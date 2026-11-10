import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 30 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_30_0 : semOKPart (cfg3 30) 0 = true := by decide +kernel
theorem sem3p_30_1 : semOKPart (cfg3 30) 1 = true := by decide +kernel
theorem sem3p_30_2 : semOKPart (cfg3 30) 2 = true := by decide +kernel
theorem sem3p_30_3 : semOKPart (cfg3 30) 3 = true := by decide +kernel

theorem sem3c_30 : semOK (cfg3 30) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_30_0 sem3p_30_1 sem3p_30_2 sem3p_30_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
