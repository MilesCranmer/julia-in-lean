import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 80 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_80_0 : ssaOKPart (cfg3 80) 0 = true := by decide +kernel
theorem ssa3p_80_1 : ssaOKPart (cfg3 80) 1 = true := by decide +kernel
theorem ssa3p_80_2 : ssaOKPart (cfg3 80) 2 = true := by decide +kernel
theorem ssa3p_80_3 : ssaOKPart (cfg3 80) 3 = true := by decide +kernel

theorem ssa3c_80 : ssaOK (cfg3 80) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_80_0 ssa3p_80_1 ssa3p_80_2 ssa3p_80_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
