import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 78 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_78_0 : semOKPart (cfg3 78) 0 = true := by decide +kernel
theorem sem3p_78_1 : semOKPart (cfg3 78) 1 = true := by decide +kernel
theorem sem3p_78_2 : semOKPart (cfg3 78) 2 = true := by decide +kernel
theorem sem3p_78_3 : semOKPart (cfg3 78) 3 = true := by decide +kernel

theorem sem3c_78 : semOK (cfg3 78) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_78_0 sem3p_78_1 sem3p_78_2 sem3p_78_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
