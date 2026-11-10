import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 56 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_56_0 : ssaOKPart (cfg3 56) 0 = true := by decide +kernel
theorem ssa3p_56_1 : ssaOKPart (cfg3 56) 1 = true := by decide +kernel
theorem ssa3p_56_2 : ssaOKPart (cfg3 56) 2 = true := by decide +kernel
theorem ssa3p_56_3 : ssaOKPart (cfg3 56) 3 = true := by decide +kernel

theorem ssa3c_56 : ssaOK (cfg3 56) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_56_0 ssa3p_56_1 ssa3p_56_2 ssa3p_56_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
