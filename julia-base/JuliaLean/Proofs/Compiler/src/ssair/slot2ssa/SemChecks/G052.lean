import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 52 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_52_0 : semOKPart (cfg3 52) 0 = true := by decide +kernel
theorem sem3p_52_1 : semOKPart (cfg3 52) 1 = true := by decide +kernel
theorem sem3p_52_2 : semOKPart (cfg3 52) 2 = true := by decide +kernel
theorem sem3p_52_3 : semOKPart (cfg3 52) 3 = true := by decide +kernel

theorem sem3c_52 : semOK (cfg3 52) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_52_0 sem3p_52_1 sem3p_52_2 sem3p_52_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
