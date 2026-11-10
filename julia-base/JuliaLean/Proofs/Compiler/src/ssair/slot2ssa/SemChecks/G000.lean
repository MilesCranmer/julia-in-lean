import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 0 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_0_0 : semOKPart (cfg3 0) 0 = true := by decide +kernel
theorem sem3p_0_1 : semOKPart (cfg3 0) 1 = true := by decide +kernel
theorem sem3p_0_2 : semOKPart (cfg3 0) 2 = true := by decide +kernel
theorem sem3p_0_3 : semOKPart (cfg3 0) 3 = true := by decide +kernel

theorem sem3c_0 : semOK (cfg3 0) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_0_0 sem3p_0_1 sem3p_0_2 sem3p_0_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
