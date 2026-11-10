import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 5 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_5_0 : semOKPart (cfg3 5) 0 = true := by decide +kernel
theorem sem3p_5_1 : semOKPart (cfg3 5) 1 = true := by decide +kernel
theorem sem3p_5_2 : semOKPart (cfg3 5) 2 = true := by decide +kernel
theorem sem3p_5_3 : semOKPart (cfg3 5) 3 = true := by decide +kernel

theorem sem3c_5 : semOK (cfg3 5) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_5_0 sem3p_5_1 sem3p_5_2 sem3p_5_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
