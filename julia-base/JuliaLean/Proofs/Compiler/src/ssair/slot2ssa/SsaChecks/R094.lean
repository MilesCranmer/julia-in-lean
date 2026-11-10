import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 94 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_94_0 : ssaOKPart (cfg3 94) 0 = true := by decide +kernel
theorem ssa3p_94_1 : ssaOKPart (cfg3 94) 1 = true := by decide +kernel
theorem ssa3p_94_2 : ssaOKPart (cfg3 94) 2 = true := by decide +kernel
theorem ssa3p_94_3 : ssaOKPart (cfg3 94) 3 = true := by decide +kernel

theorem ssa3c_94 : ssaOK (cfg3 94) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_94_0 ssa3p_94_1 ssa3p_94_2 ssa3p_94_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
