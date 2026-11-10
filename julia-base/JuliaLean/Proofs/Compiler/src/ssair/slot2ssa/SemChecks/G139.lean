import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 139 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_139_0 : semOKPart (cfg3 139) 0 = true := by decide +kernel
theorem sem3p_139_1 : semOKPart (cfg3 139) 1 = true := by decide +kernel
theorem sem3p_139_2 : semOKPart (cfg3 139) 2 = true := by decide +kernel
theorem sem3p_139_3 : semOKPart (cfg3 139) 3 = true := by decide +kernel

theorem sem3c_139 : semOK (cfg3 139) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_139_0 sem3p_139_1 sem3p_139_2 sem3p_139_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
