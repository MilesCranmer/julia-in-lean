import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 87 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_87_0 : semOKPart (cfg3 87) 0 = true := by decide +kernel
theorem sem3p_87_1 : semOKPart (cfg3 87) 1 = true := by decide +kernel
theorem sem3p_87_2 : semOKPart (cfg3 87) 2 = true := by decide +kernel
theorem sem3p_87_3 : semOKPart (cfg3 87) 3 = true := by decide +kernel

theorem sem3c_87 : semOK (cfg3 87) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_87_0 sem3p_87_1 sem3p_87_2 sem3p_87_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
