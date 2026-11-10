import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 64 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_64_0 : ssaOKPart (cfg3 64) 0 = true := by decide +kernel
theorem ssa3p_64_1 : ssaOKPart (cfg3 64) 1 = true := by decide +kernel
theorem ssa3p_64_2 : ssaOKPart (cfg3 64) 2 = true := by decide +kernel
theorem ssa3p_64_3 : ssaOKPart (cfg3 64) 3 = true := by decide +kernel

theorem ssa3c_64 : ssaOK (cfg3 64) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_64_0 ssa3p_64_1 ssa3p_64_2 ssa3p_64_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
