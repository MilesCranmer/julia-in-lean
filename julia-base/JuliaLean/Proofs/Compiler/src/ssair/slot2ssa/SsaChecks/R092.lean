import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 92 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_92_0 : ssaOKPart (cfg3 92) 0 = true := by decide +kernel
theorem ssa3p_92_1 : ssaOKPart (cfg3 92) 1 = true := by decide +kernel
theorem ssa3p_92_2 : ssaOKPart (cfg3 92) 2 = true := by decide +kernel
theorem ssa3p_92_3 : ssaOKPart (cfg3 92) 3 = true := by decide +kernel

theorem ssa3c_92 : ssaOK (cfg3 92) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_92_0 ssa3p_92_1 ssa3p_92_2 ssa3p_92_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
