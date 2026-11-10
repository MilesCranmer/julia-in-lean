import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 61 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_61_0 : ssaOKPart (cfg3 61) 0 = true := by decide +kernel
theorem ssa3p_61_1 : ssaOKPart (cfg3 61) 1 = true := by decide +kernel
theorem ssa3p_61_2 : ssaOKPart (cfg3 61) 2 = true := by decide +kernel
theorem ssa3p_61_3 : ssaOKPart (cfg3 61) 3 = true := by decide +kernel

theorem ssa3c_61 : ssaOK (cfg3 61) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_61_0 ssa3p_61_1 ssa3p_61_2 ssa3p_61_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
