import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 61 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_61_0 : semOKPart (cfg3 61) 0 = true := by decide +kernel
theorem sem3p_61_1 : semOKPart (cfg3 61) 1 = true := by decide +kernel
theorem sem3p_61_2 : semOKPart (cfg3 61) 2 = true := by decide +kernel
theorem sem3p_61_3 : semOKPart (cfg3 61) 3 = true := by decide +kernel

theorem sem3c_61 : semOK (cfg3 61) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_61_0 sem3p_61_1 sem3p_61_2 sem3p_61_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
