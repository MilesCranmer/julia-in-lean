import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 71 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_71_0 : semOKPart (cfg3 71) 0 = true := by decide +kernel
theorem sem3p_71_1 : semOKPart (cfg3 71) 1 = true := by decide +kernel
theorem sem3p_71_2 : semOKPart (cfg3 71) 2 = true := by decide +kernel
theorem sem3p_71_3 : semOKPart (cfg3 71) 3 = true := by decide +kernel

theorem sem3c_71 : semOK (cfg3 71) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_71_0 sem3p_71_1 sem3p_71_2 sem3p_71_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
