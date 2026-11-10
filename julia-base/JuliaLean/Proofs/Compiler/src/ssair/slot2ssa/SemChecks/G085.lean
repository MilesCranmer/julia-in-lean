import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 85 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_85_0 : semOKPart (cfg3 85) 0 = true := by decide +kernel
theorem sem3p_85_1 : semOKPart (cfg3 85) 1 = true := by decide +kernel
theorem sem3p_85_2 : semOKPart (cfg3 85) 2 = true := by decide +kernel
theorem sem3p_85_3 : semOKPart (cfg3 85) 3 = true := by decide +kernel

theorem sem3c_85 : semOK (cfg3 85) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_85_0 sem3p_85_1 sem3p_85_2 sem3p_85_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
