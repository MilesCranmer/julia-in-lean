import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 143 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_143_0 : semOKPart (cfg3 143) 0 = true := by decide +kernel
theorem sem3p_143_1 : semOKPart (cfg3 143) 1 = true := by decide +kernel
theorem sem3p_143_2 : semOKPart (cfg3 143) 2 = true := by decide +kernel
theorem sem3p_143_3 : semOKPart (cfg3 143) 3 = true := by decide +kernel

theorem sem3c_143 : semOK (cfg3 143) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_143_0 sem3p_143_1 sem3p_143_2 sem3p_143_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
