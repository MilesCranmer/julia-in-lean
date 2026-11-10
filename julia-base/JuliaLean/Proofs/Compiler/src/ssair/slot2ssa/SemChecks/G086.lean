import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 86 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_86_0 : semOKPart (cfg3 86) 0 = true := by decide +kernel
theorem sem3p_86_1 : semOKPart (cfg3 86) 1 = true := by decide +kernel
theorem sem3p_86_2 : semOKPart (cfg3 86) 2 = true := by decide +kernel
theorem sem3p_86_3 : semOKPart (cfg3 86) 3 = true := by decide +kernel

theorem sem3c_86 : semOK (cfg3 86) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_86_0 sem3p_86_1 sem3p_86_2 sem3p_86_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
