import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 47 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_47_0 : semOKPart (cfg3 47) 0 = true := by decide +kernel
theorem sem3p_47_1 : semOKPart (cfg3 47) 1 = true := by decide +kernel
theorem sem3p_47_2 : semOKPart (cfg3 47) 2 = true := by decide +kernel
theorem sem3p_47_3 : semOKPart (cfg3 47) 3 = true := by decide +kernel

theorem sem3c_47 : semOK (cfg3 47) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_47_0 sem3p_47_1 sem3p_47_2 sem3p_47_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
