import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 123 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_123_0 : ssaOKPart (cfg3 123) 0 = true := by decide +kernel
theorem ssa3p_123_1 : ssaOKPart (cfg3 123) 1 = true := by decide +kernel
theorem ssa3p_123_2 : ssaOKPart (cfg3 123) 2 = true := by decide +kernel
theorem ssa3p_123_3 : ssaOKPart (cfg3 123) 3 = true := by decide +kernel

theorem ssa3c_123 : ssaOK (cfg3 123) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_123_0 ssa3p_123_1 ssa3p_123_2 ssa3p_123_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
