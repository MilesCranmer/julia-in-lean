import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 11 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_11_0 : semOKPart (cfg3 11) 0 = true := by decide +kernel
theorem sem3p_11_1 : semOKPart (cfg3 11) 1 = true := by decide +kernel
theorem sem3p_11_2 : semOKPart (cfg3 11) 2 = true := by decide +kernel
theorem sem3p_11_3 : semOKPart (cfg3 11) 3 = true := by decide +kernel

theorem sem3c_11 : semOK (cfg3 11) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_11_0 sem3p_11_1 sem3p_11_2 sem3p_11_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
