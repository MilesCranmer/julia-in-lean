import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 62 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_62_0 : semOKPart (cfg3 62) 0 = true := by decide +kernel
theorem sem3p_62_1 : semOKPart (cfg3 62) 1 = true := by decide +kernel
theorem sem3p_62_2 : semOKPart (cfg3 62) 2 = true := by decide +kernel
theorem sem3p_62_3 : semOKPart (cfg3 62) 3 = true := by decide +kernel

theorem sem3c_62 : semOK (cfg3 62) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_62_0 sem3p_62_1 sem3p_62_2 sem3p_62_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
