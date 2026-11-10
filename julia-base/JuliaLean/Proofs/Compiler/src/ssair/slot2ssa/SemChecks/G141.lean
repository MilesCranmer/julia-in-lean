import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 141 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_141_0 : semOKPart (cfg3 141) 0 = true := by decide +kernel
theorem sem3p_141_1 : semOKPart (cfg3 141) 1 = true := by decide +kernel
theorem sem3p_141_2 : semOKPart (cfg3 141) 2 = true := by decide +kernel
theorem sem3p_141_3 : semOKPart (cfg3 141) 3 = true := by decide +kernel

theorem sem3c_141 : semOK (cfg3 141) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_141_0 sem3p_141_1 sem3p_141_2 sem3p_141_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
