import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 135 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_135_0 : semOKPart (cfg3 135) 0 = true := by decide +kernel
theorem sem3p_135_1 : semOKPart (cfg3 135) 1 = true := by decide +kernel
theorem sem3p_135_2 : semOKPart (cfg3 135) 2 = true := by decide +kernel
theorem sem3p_135_3 : semOKPart (cfg3 135) 3 = true := by decide +kernel

theorem sem3c_135 : semOK (cfg3 135) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_135_0 sem3p_135_1 sem3p_135_2 sem3p_135_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
