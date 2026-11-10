import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 78 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_78_0 : ssaOKPart (cfg3 78) 0 = true := by decide +kernel
theorem ssa3p_78_1 : ssaOKPart (cfg3 78) 1 = true := by decide +kernel
theorem ssa3p_78_2 : ssaOKPart (cfg3 78) 2 = true := by decide +kernel
theorem ssa3p_78_3 : ssaOKPart (cfg3 78) 3 = true := by decide +kernel

theorem ssa3c_78 : ssaOK (cfg3 78) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_78_0 ssa3p_78_1 ssa3p_78_2 ssa3p_78_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
