import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 79 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_79_0 : semOKPart (cfg3 79) 0 = true := by decide +kernel
theorem sem3p_79_1 : semOKPart (cfg3 79) 1 = true := by decide +kernel
theorem sem3p_79_2 : semOKPart (cfg3 79) 2 = true := by decide +kernel
theorem sem3p_79_3 : semOKPart (cfg3 79) 3 = true := by decide +kernel

theorem sem3c_79 : semOK (cfg3 79) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_79_0 sem3p_79_1 sem3p_79_2 sem3p_79_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
