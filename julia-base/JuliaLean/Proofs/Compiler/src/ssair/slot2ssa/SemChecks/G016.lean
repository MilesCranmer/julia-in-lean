import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 16 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_16_0 : semOKPart (cfg3 16) 0 = true := by decide +kernel
theorem sem3p_16_1 : semOKPart (cfg3 16) 1 = true := by decide +kernel
theorem sem3p_16_2 : semOKPart (cfg3 16) 2 = true := by decide +kernel
theorem sem3p_16_3 : semOKPart (cfg3 16) 3 = true := by decide +kernel

theorem sem3c_16 : semOK (cfg3 16) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_16_0 sem3p_16_1 sem3p_16_2 sem3p_16_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
