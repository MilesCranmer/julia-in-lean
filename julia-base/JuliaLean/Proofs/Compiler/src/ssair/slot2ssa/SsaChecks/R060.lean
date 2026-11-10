import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 60 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_60_0 : ssaOKPart (cfg3 60) 0 = true := by decide +kernel
theorem ssa3p_60_1 : ssaOKPart (cfg3 60) 1 = true := by decide +kernel
theorem ssa3p_60_2 : ssaOKPart (cfg3 60) 2 = true := by decide +kernel
theorem ssa3p_60_3 : ssaOKPart (cfg3 60) 3 = true := by decide +kernel

theorem ssa3c_60 : ssaOK (cfg3 60) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_60_0 ssa3p_60_1 ssa3p_60_2 ssa3p_60_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
