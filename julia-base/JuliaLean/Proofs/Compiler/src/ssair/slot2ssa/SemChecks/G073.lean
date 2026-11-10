import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 73 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_73_0 : semOKPart (cfg3 73) 0 = true := by decide +kernel
theorem sem3p_73_1 : semOKPart (cfg3 73) 1 = true := by decide +kernel
theorem sem3p_73_2 : semOKPart (cfg3 73) 2 = true := by decide +kernel
theorem sem3p_73_3 : semOKPart (cfg3 73) 3 = true := by decide +kernel

theorem sem3c_73 : semOK (cfg3 73) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_73_0 sem3p_73_1 sem3p_73_2 sem3p_73_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
