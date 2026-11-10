import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 100 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_100_0 : ssaOKPart (cfg3 100) 0 = true := by decide +kernel
theorem ssa3p_100_1 : ssaOKPart (cfg3 100) 1 = true := by decide +kernel
theorem ssa3p_100_2 : ssaOKPart (cfg3 100) 2 = true := by decide +kernel
theorem ssa3p_100_3 : ssaOKPart (cfg3 100) 3 = true := by decide +kernel

theorem ssa3c_100 : ssaOK (cfg3 100) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_100_0 ssa3p_100_1 ssa3p_100_2 ssa3p_100_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
