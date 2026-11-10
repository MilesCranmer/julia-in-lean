import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 93 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_93_0 : semOKPart (cfg3 93) 0 = true := by decide +kernel
theorem sem3p_93_1 : semOKPart (cfg3 93) 1 = true := by decide +kernel
theorem sem3p_93_2 : semOKPart (cfg3 93) 2 = true := by decide +kernel
theorem sem3p_93_3 : semOKPart (cfg3 93) 3 = true := by decide +kernel

theorem sem3c_93 : semOK (cfg3 93) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_93_0 sem3p_93_1 sem3p_93_2 sem3p_93_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
