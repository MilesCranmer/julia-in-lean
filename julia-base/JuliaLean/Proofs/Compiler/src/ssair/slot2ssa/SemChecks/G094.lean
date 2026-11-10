import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 94 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_94_0 : semOKPart (cfg3 94) 0 = true := by decide +kernel
theorem sem3p_94_1 : semOKPart (cfg3 94) 1 = true := by decide +kernel
theorem sem3p_94_2 : semOKPart (cfg3 94) 2 = true := by decide +kernel
theorem sem3p_94_3 : semOKPart (cfg3 94) 3 = true := by decide +kernel

theorem sem3c_94 : semOK (cfg3 94) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_94_0 sem3p_94_1 sem3p_94_2 sem3p_94_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
