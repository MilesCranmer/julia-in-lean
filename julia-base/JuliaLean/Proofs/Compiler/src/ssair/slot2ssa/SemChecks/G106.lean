import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 106 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_106_0 : semOKPart (cfg3 106) 0 = true := by decide +kernel
theorem sem3p_106_1 : semOKPart (cfg3 106) 1 = true := by decide +kernel
theorem sem3p_106_2 : semOKPart (cfg3 106) 2 = true := by decide +kernel
theorem sem3p_106_3 : semOKPart (cfg3 106) 3 = true := by decide +kernel

theorem sem3c_106 : semOK (cfg3 106) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_106_0 sem3p_106_1 sem3p_106_2 sem3p_106_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
