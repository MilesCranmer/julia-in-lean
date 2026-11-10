import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 83 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_83_0 : ssaOKPart (cfg3 83) 0 = true := by decide +kernel
theorem ssa3p_83_1 : ssaOKPart (cfg3 83) 1 = true := by decide +kernel
theorem ssa3p_83_2 : ssaOKPart (cfg3 83) 2 = true := by decide +kernel
theorem ssa3p_83_3 : ssaOKPart (cfg3 83) 3 = true := by decide +kernel

theorem ssa3c_83 : ssaOK (cfg3 83) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_83_0 ssa3p_83_1 ssa3p_83_2 ssa3p_83_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
