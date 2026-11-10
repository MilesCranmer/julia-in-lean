import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 20 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_20_0 : semOKPart (cfg3 20) 0 = true := by decide +kernel
theorem sem3p_20_1 : semOKPart (cfg3 20) 1 = true := by decide +kernel
theorem sem3p_20_2 : semOKPart (cfg3 20) 2 = true := by decide +kernel
theorem sem3p_20_3 : semOKPart (cfg3 20) 3 = true := by decide +kernel

theorem sem3c_20 : semOK (cfg3 20) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_20_0 sem3p_20_1 sem3p_20_2 sem3p_20_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
