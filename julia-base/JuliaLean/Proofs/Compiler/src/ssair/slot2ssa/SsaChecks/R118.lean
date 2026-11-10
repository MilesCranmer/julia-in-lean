import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 118 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_118_0 : ssaOKPart (cfg3 118) 0 = true := by decide +kernel
theorem ssa3p_118_1 : ssaOKPart (cfg3 118) 1 = true := by decide +kernel
theorem ssa3p_118_2 : ssaOKPart (cfg3 118) 2 = true := by decide +kernel
theorem ssa3p_118_3 : ssaOKPart (cfg3 118) 3 = true := by decide +kernel

theorem ssa3c_118 : ssaOK (cfg3 118) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_118_0 ssa3p_118_1 ssa3p_118_2 ssa3p_118_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
