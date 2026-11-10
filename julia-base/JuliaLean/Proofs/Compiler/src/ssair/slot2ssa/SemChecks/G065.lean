import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 65 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_65_0 : semOKPart (cfg3 65) 0 = true := by decide +kernel
theorem sem3p_65_1 : semOKPart (cfg3 65) 1 = true := by decide +kernel
theorem sem3p_65_2 : semOKPart (cfg3 65) 2 = true := by decide +kernel
theorem sem3p_65_3 : semOKPart (cfg3 65) 3 = true := by decide +kernel

theorem sem3c_65 : semOK (cfg3 65) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_65_0 sem3p_65_1 sem3p_65_2 sem3p_65_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
