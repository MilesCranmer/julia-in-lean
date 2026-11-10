import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 6 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_6_0 : semOKPart (cfg3 6) 0 = true := by decide +kernel
theorem sem3p_6_1 : semOKPart (cfg3 6) 1 = true := by decide +kernel
theorem sem3p_6_2 : semOKPart (cfg3 6) 2 = true := by decide +kernel
theorem sem3p_6_3 : semOKPart (cfg3 6) 3 = true := by decide +kernel

theorem sem3c_6 : semOK (cfg3 6) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_6_0 sem3p_6_1 sem3p_6_2 sem3p_6_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
