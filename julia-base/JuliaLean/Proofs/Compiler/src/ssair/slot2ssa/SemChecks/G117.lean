import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 117 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_117_0 : semOKPart (cfg3 117) 0 = true := by decide +kernel
theorem sem3p_117_1 : semOKPart (cfg3 117) 1 = true := by decide +kernel
theorem sem3p_117_2 : semOKPart (cfg3 117) 2 = true := by decide +kernel
theorem sem3p_117_3 : semOKPart (cfg3 117) 3 = true := by decide +kernel

theorem sem3c_117 : semOK (cfg3 117) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_117_0 sem3p_117_1 sem3p_117_2 sem3p_117_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
