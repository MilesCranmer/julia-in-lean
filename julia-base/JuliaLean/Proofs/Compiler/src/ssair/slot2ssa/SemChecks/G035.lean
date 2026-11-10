import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 35 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_35_0 : semOKPart (cfg3 35) 0 = true := by decide +kernel
theorem sem3p_35_1 : semOKPart (cfg3 35) 1 = true := by decide +kernel
theorem sem3p_35_2 : semOKPart (cfg3 35) 2 = true := by decide +kernel
theorem sem3p_35_3 : semOKPart (cfg3 35) 3 = true := by decide +kernel

theorem sem3c_35 : semOK (cfg3 35) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_35_0 sem3p_35_1 sem3p_35_2 sem3p_35_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
