import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 140 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_140_0 : ssaOKPart (cfg3 140) 0 = true := by decide +kernel
theorem ssa3p_140_1 : ssaOKPart (cfg3 140) 1 = true := by decide +kernel
theorem ssa3p_140_2 : ssaOKPart (cfg3 140) 2 = true := by decide +kernel
theorem ssa3p_140_3 : ssaOKPart (cfg3 140) 3 = true := by decide +kernel

theorem ssa3c_140 : ssaOK (cfg3 140) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_140_0 ssa3p_140_1 ssa3p_140_2 ssa3p_140_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
