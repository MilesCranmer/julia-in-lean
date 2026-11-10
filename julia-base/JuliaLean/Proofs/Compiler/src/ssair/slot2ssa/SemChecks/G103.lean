import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 103 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_103_0 : semOKPart (cfg3 103) 0 = true := by decide +kernel
theorem sem3p_103_1 : semOKPart (cfg3 103) 1 = true := by decide +kernel
theorem sem3p_103_2 : semOKPart (cfg3 103) 2 = true := by decide +kernel
theorem sem3p_103_3 : semOKPart (cfg3 103) 3 = true := by decide +kernel

theorem sem3c_103 : semOK (cfg3 103) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_103_0 sem3p_103_1 sem3p_103_2 sem3p_103_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
