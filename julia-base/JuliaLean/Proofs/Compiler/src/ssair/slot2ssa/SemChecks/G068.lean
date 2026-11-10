import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SemChecks.Common

/-! Kernel check of `semOK` on CFG 68 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem sem3p_68_0 : semOKPart (cfg3 68) 0 = true := by decide +kernel
theorem sem3p_68_1 : semOKPart (cfg3 68) 1 = true := by decide +kernel
theorem sem3p_68_2 : semOKPart (cfg3 68) 2 = true := by decide +kernel
theorem sem3p_68_3 : semOKPart (cfg3 68) 3 = true := by decide +kernel

theorem sem3c_68 : semOK (cfg3 68) = true :=
  semOK_of_parts _ (by decide +kernel) sem3p_68_0 sem3p_68_1 sem3p_68_2 sem3p_68_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
