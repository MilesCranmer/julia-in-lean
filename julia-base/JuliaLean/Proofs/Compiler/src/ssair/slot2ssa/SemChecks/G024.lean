import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 24 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_24_0 : semOKPart (cfg3 24) 0 = true := by decide +kernel
theorem sem3p_24_1 : semOKPart (cfg3 24) 1 = true := by decide +kernel
theorem sem3p_24_2 : semOKPart (cfg3 24) 2 = true := by decide +kernel
theorem sem3p_24_3 : semOKPart (cfg3 24) 3 = true := by decide +kernel

theorem sem3c_24 : semOK (cfg3 24) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_24_0 sem3p_24_1 sem3p_24_2 sem3p_24_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
