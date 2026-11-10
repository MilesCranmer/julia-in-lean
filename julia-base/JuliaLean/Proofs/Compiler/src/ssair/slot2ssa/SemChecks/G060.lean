import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 60 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_60_0 : semOKPart (cfg3 60) 0 = true := by decide +kernel
theorem sem3p_60_1 : semOKPart (cfg3 60) 1 = true := by decide +kernel
theorem sem3p_60_2 : semOKPart (cfg3 60) 2 = true := by decide +kernel
theorem sem3p_60_3 : semOKPart (cfg3 60) 3 = true := by decide +kernel

theorem sem3c_60 : semOK (cfg3 60) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_60_0 sem3p_60_1 sem3p_60_2 sem3p_60_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
