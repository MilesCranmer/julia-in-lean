import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 91 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_91_0 : semOKPart (cfg3 91) 0 = true := by decide +kernel
theorem sem3p_91_1 : semOKPart (cfg3 91) 1 = true := by decide +kernel
theorem sem3p_91_2 : semOKPart (cfg3 91) 2 = true := by decide +kernel
theorem sem3p_91_3 : semOKPart (cfg3 91) 3 = true := by decide +kernel

theorem sem3c_91 : semOK (cfg3 91) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_91_0 sem3p_91_1 sem3p_91_2 sem3p_91_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
