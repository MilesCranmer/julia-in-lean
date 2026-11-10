import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 125 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_125_0 : semOKPart (cfg3 125) 0 = true := by decide +kernel
theorem sem3p_125_1 : semOKPart (cfg3 125) 1 = true := by decide +kernel
theorem sem3p_125_2 : semOKPart (cfg3 125) 2 = true := by decide +kernel
theorem sem3p_125_3 : semOKPart (cfg3 125) 3 = true := by decide +kernel

theorem sem3c_125 : semOK (cfg3 125) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_125_0 sem3p_125_1 sem3p_125_2 sem3p_125_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
