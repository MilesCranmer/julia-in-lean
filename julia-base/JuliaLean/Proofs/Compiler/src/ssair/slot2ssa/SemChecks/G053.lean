import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 53 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_53_0 : semOKPart (cfg3 53) 0 = true := by decide +kernel
theorem sem3p_53_1 : semOKPart (cfg3 53) 1 = true := by decide +kernel
theorem sem3p_53_2 : semOKPart (cfg3 53) 2 = true := by decide +kernel
theorem sem3p_53_3 : semOKPart (cfg3 53) 3 = true := by decide +kernel

theorem sem3c_53 : semOK (cfg3 53) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_53_0 sem3p_53_1 sem3p_53_2 sem3p_53_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
