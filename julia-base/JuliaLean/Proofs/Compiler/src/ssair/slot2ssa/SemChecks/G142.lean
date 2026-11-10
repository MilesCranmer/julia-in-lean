import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 142 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_142_0 : semOKPart (cfg3 142) 0 = true := by decide +kernel
theorem sem3p_142_1 : semOKPart (cfg3 142) 1 = true := by decide +kernel
theorem sem3p_142_2 : semOKPart (cfg3 142) 2 = true := by decide +kernel
theorem sem3p_142_3 : semOKPart (cfg3 142) 3 = true := by decide +kernel

theorem sem3c_142 : semOK (cfg3 142) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_142_0 sem3p_142_1 sem3p_142_2 sem3p_142_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
