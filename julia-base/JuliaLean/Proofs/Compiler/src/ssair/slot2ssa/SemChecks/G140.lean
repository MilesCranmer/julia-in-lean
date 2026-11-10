import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 140 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_140_0 : semOKPart (cfg3 140) 0 = true := by decide +kernel
theorem sem3p_140_1 : semOKPart (cfg3 140) 1 = true := by decide +kernel
theorem sem3p_140_2 : semOKPart (cfg3 140) 2 = true := by decide +kernel
theorem sem3p_140_3 : semOKPart (cfg3 140) 3 = true := by decide +kernel

theorem sem3c_140 : semOK (cfg3 140) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_140_0 sem3p_140_1 sem3p_140_2 sem3p_140_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
