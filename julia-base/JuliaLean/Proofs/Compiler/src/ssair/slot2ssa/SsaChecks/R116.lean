import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 116 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_116_0 : ssaOKPart (cfg3 116) 0 = true := by decide +kernel
theorem ssa3p_116_1 : ssaOKPart (cfg3 116) 1 = true := by decide +kernel
theorem ssa3p_116_2 : ssaOKPart (cfg3 116) 2 = true := by decide +kernel
theorem ssa3p_116_3 : ssaOKPart (cfg3 116) 3 = true := by decide +kernel

theorem ssa3c_116 : ssaOK (cfg3 116) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_116_0 ssa3p_116_1 ssa3p_116_2 ssa3p_116_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
