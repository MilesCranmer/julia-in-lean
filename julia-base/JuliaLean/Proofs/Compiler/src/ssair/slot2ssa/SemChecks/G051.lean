import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 51 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_51_0 : semOKPart (cfg3 51) 0 = true := by decide +kernel
theorem sem3p_51_1 : semOKPart (cfg3 51) 1 = true := by decide +kernel
theorem sem3p_51_2 : semOKPart (cfg3 51) 2 = true := by decide +kernel
theorem sem3p_51_3 : semOKPart (cfg3 51) 3 = true := by decide +kernel

theorem sem3c_51 : semOK (cfg3 51) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_51_0 sem3p_51_1 sem3p_51_2 sem3p_51_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
