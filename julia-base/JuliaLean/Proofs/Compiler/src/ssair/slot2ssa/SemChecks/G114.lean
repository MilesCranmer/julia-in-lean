import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 114 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_114_0 : semOKPart (cfg3 114) 0 = true := by decide +kernel
theorem sem3p_114_1 : semOKPart (cfg3 114) 1 = true := by decide +kernel
theorem sem3p_114_2 : semOKPart (cfg3 114) 2 = true := by decide +kernel
theorem sem3p_114_3 : semOKPart (cfg3 114) 3 = true := by decide +kernel

theorem sem3c_114 : semOK (cfg3 114) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_114_0 sem3p_114_1 sem3p_114_2 sem3p_114_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
