import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 88 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_88_0 : semOKPart (cfg3 88) 0 = true := by decide +kernel
theorem sem3p_88_1 : semOKPart (cfg3 88) 1 = true := by decide +kernel
theorem sem3p_88_2 : semOKPart (cfg3 88) 2 = true := by decide +kernel
theorem sem3p_88_3 : semOKPart (cfg3 88) 3 = true := by decide +kernel

theorem sem3c_88 : semOK (cfg3 88) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_88_0 sem3p_88_1 sem3p_88_2 sem3p_88_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
