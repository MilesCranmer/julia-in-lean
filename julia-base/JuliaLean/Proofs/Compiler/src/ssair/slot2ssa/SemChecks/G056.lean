import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 56 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_56_0 : semOKPart (cfg3 56) 0 = true := by decide +kernel
theorem sem3p_56_1 : semOKPart (cfg3 56) 1 = true := by decide +kernel
theorem sem3p_56_2 : semOKPart (cfg3 56) 2 = true := by decide +kernel
theorem sem3p_56_3 : semOKPart (cfg3 56) 3 = true := by decide +kernel

theorem sem3c_56 : semOK (cfg3 56) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_56_0 sem3p_56_1 sem3p_56_2 sem3p_56_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
