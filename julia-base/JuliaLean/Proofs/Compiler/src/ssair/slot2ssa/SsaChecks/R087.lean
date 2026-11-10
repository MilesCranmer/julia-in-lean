import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 87 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_87_0 : ssaOKPart (cfg3 87) 0 = true := by decide +kernel
theorem ssa3p_87_1 : ssaOKPart (cfg3 87) 1 = true := by decide +kernel
theorem ssa3p_87_2 : ssaOKPart (cfg3 87) 2 = true := by decide +kernel
theorem ssa3p_87_3 : ssaOKPart (cfg3 87) 3 = true := by decide +kernel

theorem ssa3c_87 : ssaOK (cfg3 87) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_87_0 ssa3p_87_1 ssa3p_87_2 ssa3p_87_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
