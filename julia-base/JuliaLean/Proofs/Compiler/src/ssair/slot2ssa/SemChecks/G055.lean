import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 55 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_55_0 : semOKPart (cfg3 55) 0 = true := by decide +kernel
theorem sem3p_55_1 : semOKPart (cfg3 55) 1 = true := by decide +kernel
theorem sem3p_55_2 : semOKPart (cfg3 55) 2 = true := by decide +kernel
theorem sem3p_55_3 : semOKPart (cfg3 55) 3 = true := by decide +kernel

theorem sem3c_55 : semOK (cfg3 55) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_55_0 sem3p_55_1 sem3p_55_2 sem3p_55_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
