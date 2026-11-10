import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 137 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_137_0 : semOKPart (cfg3 137) 0 = true := by decide +kernel
theorem sem3p_137_1 : semOKPart (cfg3 137) 1 = true := by decide +kernel
theorem sem3p_137_2 : semOKPart (cfg3 137) 2 = true := by decide +kernel
theorem sem3p_137_3 : semOKPart (cfg3 137) 3 = true := by decide +kernel

theorem sem3c_137 : semOK (cfg3 137) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_137_0 sem3p_137_1 sem3p_137_2 sem3p_137_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
