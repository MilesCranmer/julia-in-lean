import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 112 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_112_0 : semOKPart (cfg3 112) 0 = true := by decide +kernel
theorem sem3p_112_1 : semOKPart (cfg3 112) 1 = true := by decide +kernel
theorem sem3p_112_2 : semOKPart (cfg3 112) 2 = true := by decide +kernel
theorem sem3p_112_3 : semOKPart (cfg3 112) 3 = true := by decide +kernel

theorem sem3c_112 : semOK (cfg3 112) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_112_0 sem3p_112_1 sem3p_112_2 sem3p_112_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
