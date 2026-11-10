import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 67 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_67_0 : semOKPart (cfg3 67) 0 = true := by decide +kernel
theorem sem3p_67_1 : semOKPart (cfg3 67) 1 = true := by decide +kernel
theorem sem3p_67_2 : semOKPart (cfg3 67) 2 = true := by decide +kernel
theorem sem3p_67_3 : semOKPart (cfg3 67) 3 = true := by decide +kernel

theorem sem3c_67 : semOK (cfg3 67) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_67_0 sem3p_67_1 sem3p_67_2 sem3p_67_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
