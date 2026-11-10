import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 38 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_38_0 : semOKPart (cfg3 38) 0 = true := by decide +kernel
theorem sem3p_38_1 : semOKPart (cfg3 38) 1 = true := by decide +kernel
theorem sem3p_38_2 : semOKPart (cfg3 38) 2 = true := by decide +kernel
theorem sem3p_38_3 : semOKPart (cfg3 38) 3 = true := by decide +kernel

theorem sem3c_38 : semOK (cfg3 38) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_38_0 sem3p_38_1 sem3p_38_2 sem3p_38_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
