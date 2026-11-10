import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 58 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_58_0 : semOKPart (cfg3 58) 0 = true := by decide +kernel
theorem sem3p_58_1 : semOKPart (cfg3 58) 1 = true := by decide +kernel
theorem sem3p_58_2 : semOKPart (cfg3 58) 2 = true := by decide +kernel
theorem sem3p_58_3 : semOKPart (cfg3 58) 3 = true := by decide +kernel

theorem sem3c_58 : semOK (cfg3 58) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_58_0 sem3p_58_1 sem3p_58_2 sem3p_58_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
