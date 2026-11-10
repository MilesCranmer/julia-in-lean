import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 136 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_136_0 : ssaOKPart (cfg3 136) 0 = true := by decide +kernel
theorem ssa3p_136_1 : ssaOKPart (cfg3 136) 1 = true := by decide +kernel
theorem ssa3p_136_2 : ssaOKPart (cfg3 136) 2 = true := by decide +kernel
theorem ssa3p_136_3 : ssaOKPart (cfg3 136) 3 = true := by decide +kernel

theorem ssa3c_136 : ssaOK (cfg3 136) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_136_0 ssa3p_136_1 ssa3p_136_2 ssa3p_136_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
