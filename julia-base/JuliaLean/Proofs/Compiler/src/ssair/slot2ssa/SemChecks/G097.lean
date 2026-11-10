import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 97 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_97_0 : semOKPart (cfg3 97) 0 = true := by decide +kernel
theorem sem3p_97_1 : semOKPart (cfg3 97) 1 = true := by decide +kernel
theorem sem3p_97_2 : semOKPart (cfg3 97) 2 = true := by decide +kernel
theorem sem3p_97_3 : semOKPart (cfg3 97) 3 = true := by decide +kernel

theorem sem3c_97 : semOK (cfg3 97) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_97_0 sem3p_97_1 sem3p_97_2 sem3p_97_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
