import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 82 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_82_0 : semOKPart (cfg3 82) 0 = true := by decide +kernel
theorem sem3p_82_1 : semOKPart (cfg3 82) 1 = true := by decide +kernel
theorem sem3p_82_2 : semOKPart (cfg3 82) 2 = true := by decide +kernel
theorem sem3p_82_3 : semOKPart (cfg3 82) 3 = true := by decide +kernel

theorem sem3c_82 : semOK (cfg3 82) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_82_0 sem3p_82_1 sem3p_82_2 sem3p_82_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
