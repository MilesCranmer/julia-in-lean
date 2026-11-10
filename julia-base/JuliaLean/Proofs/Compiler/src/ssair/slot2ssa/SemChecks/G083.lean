import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 83 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_83_0 : semOKPart (cfg3 83) 0 = true := by decide +kernel
theorem sem3p_83_1 : semOKPart (cfg3 83) 1 = true := by decide +kernel
theorem sem3p_83_2 : semOKPart (cfg3 83) 2 = true := by decide +kernel
theorem sem3p_83_3 : semOKPart (cfg3 83) 3 = true := by decide +kernel

theorem sem3c_83 : semOK (cfg3 83) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_83_0 sem3p_83_1 sem3p_83_2 sem3p_83_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
