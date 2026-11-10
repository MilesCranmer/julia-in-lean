import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 4 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_4_0 : semOKPart (cfg3 4) 0 = true := by decide +kernel
theorem sem3p_4_1 : semOKPart (cfg3 4) 1 = true := by decide +kernel
theorem sem3p_4_2 : semOKPart (cfg3 4) 2 = true := by decide +kernel
theorem sem3p_4_3 : semOKPart (cfg3 4) 3 = true := by decide +kernel

theorem sem3c_4 : semOK (cfg3 4) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_4_0 sem3p_4_1 sem3p_4_2 sem3p_4_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
