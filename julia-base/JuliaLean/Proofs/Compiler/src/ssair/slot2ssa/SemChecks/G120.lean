import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 120 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_120_0 : semOKPart (cfg3 120) 0 = true := by decide +kernel
theorem sem3p_120_1 : semOKPart (cfg3 120) 1 = true := by decide +kernel
theorem sem3p_120_2 : semOKPart (cfg3 120) 2 = true := by decide +kernel
theorem sem3p_120_3 : semOKPart (cfg3 120) 3 = true := by decide +kernel

theorem sem3c_120 : semOK (cfg3 120) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_120_0 sem3p_120_1 sem3p_120_2 sem3p_120_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
