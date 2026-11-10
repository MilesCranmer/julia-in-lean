import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 88 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_88_0 : ssaOKPart (cfg3 88) 0 = true := by decide +kernel
theorem ssa3p_88_1 : ssaOKPart (cfg3 88) 1 = true := by decide +kernel
theorem ssa3p_88_2 : ssaOKPart (cfg3 88) 2 = true := by decide +kernel
theorem ssa3p_88_3 : ssaOKPart (cfg3 88) 3 = true := by decide +kernel

theorem ssa3c_88 : ssaOK (cfg3 88) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_88_0 ssa3p_88_1 ssa3p_88_2 ssa3p_88_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
