import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 74 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_74_0 : semOKPart (cfg3 74) 0 = true := by decide +kernel
theorem sem3p_74_1 : semOKPart (cfg3 74) 1 = true := by decide +kernel
theorem sem3p_74_2 : semOKPart (cfg3 74) 2 = true := by decide +kernel
theorem sem3p_74_3 : semOKPart (cfg3 74) 3 = true := by decide +kernel

theorem sem3c_74 : semOK (cfg3 74) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_74_0 sem3p_74_1 sem3p_74_2 sem3p_74_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
