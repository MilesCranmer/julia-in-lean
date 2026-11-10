import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 126 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_126_0 : semOKPart (cfg3 126) 0 = true := by decide +kernel
theorem sem3p_126_1 : semOKPart (cfg3 126) 1 = true := by decide +kernel
theorem sem3p_126_2 : semOKPart (cfg3 126) 2 = true := by decide +kernel
theorem sem3p_126_3 : semOKPart (cfg3 126) 3 = true := by decide +kernel

theorem sem3c_126 : semOK (cfg3 126) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_126_0 sem3p_126_1 sem3p_126_2 sem3p_126_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
