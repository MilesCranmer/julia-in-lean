import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 95 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_95_0 : semOKPart (cfg3 95) 0 = true := by decide +kernel
theorem sem3p_95_1 : semOKPart (cfg3 95) 1 = true := by decide +kernel
theorem sem3p_95_2 : semOKPart (cfg3 95) 2 = true := by decide +kernel
theorem sem3p_95_3 : semOKPart (cfg3 95) 3 = true := by decide +kernel

theorem sem3c_95 : semOK (cfg3 95) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_95_0 sem3p_95_1 sem3p_95_2 sem3p_95_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
