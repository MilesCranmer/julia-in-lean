import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 121 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_121_0 : semOKPart (cfg3 121) 0 = true := by decide +kernel
theorem sem3p_121_1 : semOKPart (cfg3 121) 1 = true := by decide +kernel
theorem sem3p_121_2 : semOKPart (cfg3 121) 2 = true := by decide +kernel
theorem sem3p_121_3 : semOKPart (cfg3 121) 3 = true := by decide +kernel

theorem sem3c_121 : semOK (cfg3 121) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_121_0 sem3p_121_1 sem3p_121_2 sem3p_121_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
