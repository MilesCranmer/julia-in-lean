import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 104 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_104_0 : semOKPart (cfg3 104) 0 = true := by decide +kernel
theorem sem3p_104_1 : semOKPart (cfg3 104) 1 = true := by decide +kernel
theorem sem3p_104_2 : semOKPart (cfg3 104) 2 = true := by decide +kernel
theorem sem3p_104_3 : semOKPart (cfg3 104) 3 = true := by decide +kernel

theorem sem3c_104 : semOK (cfg3 104) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_104_0 sem3p_104_1 sem3p_104_2 sem3p_104_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
