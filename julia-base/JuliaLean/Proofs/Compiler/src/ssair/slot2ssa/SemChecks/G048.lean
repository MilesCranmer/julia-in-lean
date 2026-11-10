import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 48 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_48_0 : semOKPart (cfg3 48) 0 = true := by decide +kernel
theorem sem3p_48_1 : semOKPart (cfg3 48) 1 = true := by decide +kernel
theorem sem3p_48_2 : semOKPart (cfg3 48) 2 = true := by decide +kernel
theorem sem3p_48_3 : semOKPart (cfg3 48) 3 = true := by decide +kernel

theorem sem3c_48 : semOK (cfg3 48) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_48_0 sem3p_48_1 sem3p_48_2 sem3p_48_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
