import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 76 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_76_0 : ssaOKPart (cfg3 76) 0 = true := by decide +kernel
theorem ssa3p_76_1 : ssaOKPart (cfg3 76) 1 = true := by decide +kernel
theorem ssa3p_76_2 : ssaOKPart (cfg3 76) 2 = true := by decide +kernel
theorem ssa3p_76_3 : ssaOKPart (cfg3 76) 3 = true := by decide +kernel

theorem ssa3c_76 : ssaOK (cfg3 76) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_76_0 ssa3p_76_1 ssa3p_76_2 ssa3p_76_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
