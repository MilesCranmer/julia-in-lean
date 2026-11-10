import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 90 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_90_0 : semOKPart (cfg3 90) 0 = true := by decide +kernel
theorem sem3p_90_1 : semOKPart (cfg3 90) 1 = true := by decide +kernel
theorem sem3p_90_2 : semOKPart (cfg3 90) 2 = true := by decide +kernel
theorem sem3p_90_3 : semOKPart (cfg3 90) 3 = true := by decide +kernel

theorem sem3c_90 : semOK (cfg3 90) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_90_0 sem3p_90_1 sem3p_90_2 sem3p_90_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
