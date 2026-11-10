import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 37 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_37_0 : semOKPart (cfg3 37) 0 = true := by decide +kernel
theorem sem3p_37_1 : semOKPart (cfg3 37) 1 = true := by decide +kernel
theorem sem3p_37_2 : semOKPart (cfg3 37) 2 = true := by decide +kernel
theorem sem3p_37_3 : semOKPart (cfg3 37) 3 = true := by decide +kernel

theorem sem3c_37 : semOK (cfg3 37) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_37_0 sem3p_37_1 sem3p_37_2 sem3p_37_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
