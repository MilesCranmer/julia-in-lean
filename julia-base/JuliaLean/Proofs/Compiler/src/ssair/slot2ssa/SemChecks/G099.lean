import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 99 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_99_0 : semOKPart (cfg3 99) 0 = true := by decide +kernel
theorem sem3p_99_1 : semOKPart (cfg3 99) 1 = true := by decide +kernel
theorem sem3p_99_2 : semOKPart (cfg3 99) 2 = true := by decide +kernel
theorem sem3p_99_3 : semOKPart (cfg3 99) 3 = true := by decide +kernel

theorem sem3c_99 : semOK (cfg3 99) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_99_0 sem3p_99_1 sem3p_99_2 sem3p_99_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
