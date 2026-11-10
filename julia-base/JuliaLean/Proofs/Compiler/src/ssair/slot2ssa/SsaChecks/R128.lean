import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 128 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_128_0 : ssaOKPart (cfg3 128) 0 = true := by decide +kernel
theorem ssa3p_128_1 : ssaOKPart (cfg3 128) 1 = true := by decide +kernel
theorem ssa3p_128_2 : ssaOKPart (cfg3 128) 2 = true := by decide +kernel
theorem ssa3p_128_3 : ssaOKPart (cfg3 128) 3 = true := by decide +kernel

theorem ssa3c_128 : ssaOK (cfg3 128) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_128_0 ssa3p_128_1 ssa3p_128_2 ssa3p_128_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
