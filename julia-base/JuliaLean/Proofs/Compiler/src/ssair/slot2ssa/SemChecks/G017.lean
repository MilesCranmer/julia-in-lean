import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 17 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_17_0 : semOKPart (cfg3 17) 0 = true := by decide +kernel
theorem sem3p_17_1 : semOKPart (cfg3 17) 1 = true := by decide +kernel
theorem sem3p_17_2 : semOKPart (cfg3 17) 2 = true := by decide +kernel
theorem sem3p_17_3 : semOKPart (cfg3 17) 3 = true := by decide +kernel

theorem sem3c_17 : semOK (cfg3 17) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_17_0 sem3p_17_1 sem3p_17_2 sem3p_17_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
