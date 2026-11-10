import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 98 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_98_0 : semOKPart (cfg3 98) 0 = true := by decide +kernel
theorem sem3p_98_1 : semOKPart (cfg3 98) 1 = true := by decide +kernel
theorem sem3p_98_2 : semOKPart (cfg3 98) 2 = true := by decide +kernel
theorem sem3p_98_3 : semOKPart (cfg3 98) 3 = true := by decide +kernel

theorem sem3c_98 : semOK (cfg3 98) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_98_0 sem3p_98_1 sem3p_98_2 sem3p_98_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
