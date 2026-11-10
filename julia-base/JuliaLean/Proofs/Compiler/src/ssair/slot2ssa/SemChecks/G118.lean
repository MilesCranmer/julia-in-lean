import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 118 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_118_0 : semOKPart (cfg3 118) 0 = true := by decide +kernel
theorem sem3p_118_1 : semOKPart (cfg3 118) 1 = true := by decide +kernel
theorem sem3p_118_2 : semOKPart (cfg3 118) 2 = true := by decide +kernel
theorem sem3p_118_3 : semOKPart (cfg3 118) 3 = true := by decide +kernel

theorem sem3c_118 : semOK (cfg3 118) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_118_0 sem3p_118_1 sem3p_118_2 sem3p_118_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
