import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 116 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_116_0 : semOKPart (cfg3 116) 0 = true := by decide +kernel
theorem sem3p_116_1 : semOKPart (cfg3 116) 1 = true := by decide +kernel
theorem sem3p_116_2 : semOKPart (cfg3 116) 2 = true := by decide +kernel
theorem sem3p_116_3 : semOKPart (cfg3 116) 3 = true := by decide +kernel

theorem sem3c_116 : semOK (cfg3 116) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_116_0 sem3p_116_1 sem3p_116_2 sem3p_116_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
