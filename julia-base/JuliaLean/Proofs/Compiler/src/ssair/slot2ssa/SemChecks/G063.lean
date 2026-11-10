import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 63 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_63_0 : semOKPart (cfg3 63) 0 = true := by decide +kernel
theorem sem3p_63_1 : semOKPart (cfg3 63) 1 = true := by decide +kernel
theorem sem3p_63_2 : semOKPart (cfg3 63) 2 = true := by decide +kernel
theorem sem3p_63_3 : semOKPart (cfg3 63) 3 = true := by decide +kernel

theorem sem3c_63 : semOK (cfg3 63) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_63_0 sem3p_63_1 sem3p_63_2 sem3p_63_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
