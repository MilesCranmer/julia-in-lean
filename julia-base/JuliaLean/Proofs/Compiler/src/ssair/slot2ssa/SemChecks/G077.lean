import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 77 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_77_0 : semOKPart (cfg3 77) 0 = true := by decide +kernel
theorem sem3p_77_1 : semOKPart (cfg3 77) 1 = true := by decide +kernel
theorem sem3p_77_2 : semOKPart (cfg3 77) 2 = true := by decide +kernel
theorem sem3p_77_3 : semOKPart (cfg3 77) 3 = true := by decide +kernel

theorem sem3c_77 : semOK (cfg3 77) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_77_0 sem3p_77_1 sem3p_77_2 sem3p_77_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
