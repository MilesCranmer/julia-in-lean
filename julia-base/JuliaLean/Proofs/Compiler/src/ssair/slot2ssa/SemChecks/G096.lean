import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 96 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_96_0 : semOKPart (cfg3 96) 0 = true := by decide +kernel
theorem sem3p_96_1 : semOKPart (cfg3 96) 1 = true := by decide +kernel
theorem sem3p_96_2 : semOKPart (cfg3 96) 2 = true := by decide +kernel
theorem sem3p_96_3 : semOKPart (cfg3 96) 3 = true := by decide +kernel

theorem sem3c_96 : semOK (cfg3 96) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_96_0 sem3p_96_1 sem3p_96_2 sem3p_96_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
