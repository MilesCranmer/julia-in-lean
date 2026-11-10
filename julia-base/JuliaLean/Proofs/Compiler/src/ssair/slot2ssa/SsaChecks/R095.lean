import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 95 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_95_0 : ssaOKPart (cfg3 95) 0 = true := by decide +kernel
theorem ssa3p_95_1 : ssaOKPart (cfg3 95) 1 = true := by decide +kernel
theorem ssa3p_95_2 : ssaOKPart (cfg3 95) 2 = true := by decide +kernel
theorem ssa3p_95_3 : ssaOKPart (cfg3 95) 3 = true := by decide +kernel

theorem ssa3c_95 : ssaOK (cfg3 95) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_95_0 ssa3p_95_1 ssa3p_95_2 ssa3p_95_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
