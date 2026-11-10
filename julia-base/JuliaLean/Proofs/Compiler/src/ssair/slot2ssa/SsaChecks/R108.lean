import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 108 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_108_0 : ssaOKPart (cfg3 108) 0 = true := by decide +kernel
theorem ssa3p_108_1 : ssaOKPart (cfg3 108) 1 = true := by decide +kernel
theorem ssa3p_108_2 : ssaOKPart (cfg3 108) 2 = true := by decide +kernel
theorem ssa3p_108_3 : ssaOKPart (cfg3 108) 3 = true := by decide +kernel

theorem ssa3c_108 : ssaOK (cfg3 108) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_108_0 ssa3p_108_1 ssa3p_108_2 ssa3p_108_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
