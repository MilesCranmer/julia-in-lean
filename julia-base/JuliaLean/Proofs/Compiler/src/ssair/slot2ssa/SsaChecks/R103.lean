import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 103 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_103_0 : ssaOKPart (cfg3 103) 0 = true := by decide +kernel
theorem ssa3p_103_1 : ssaOKPart (cfg3 103) 1 = true := by decide +kernel
theorem ssa3p_103_2 : ssaOKPart (cfg3 103) 2 = true := by decide +kernel
theorem ssa3p_103_3 : ssaOKPart (cfg3 103) 3 = true := by decide +kernel

theorem ssa3c_103 : ssaOK (cfg3 103) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_103_0 ssa3p_103_1 ssa3p_103_2 ssa3p_103_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
