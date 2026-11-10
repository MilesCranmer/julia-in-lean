import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 141 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_141_0 : ssaOKPart (cfg3 141) 0 = true := by decide +kernel
theorem ssa3p_141_1 : ssaOKPart (cfg3 141) 1 = true := by decide +kernel
theorem ssa3p_141_2 : ssaOKPart (cfg3 141) 2 = true := by decide +kernel
theorem ssa3p_141_3 : ssaOKPart (cfg3 141) 3 = true := by decide +kernel

theorem ssa3c_141 : ssaOK (cfg3 141) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_141_0 ssa3p_141_1 ssa3p_141_2 ssa3p_141_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
