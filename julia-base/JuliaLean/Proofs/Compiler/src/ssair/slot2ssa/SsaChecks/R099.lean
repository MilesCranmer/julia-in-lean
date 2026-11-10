import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 99 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_99_0 : ssaOKPart (cfg3 99) 0 = true := by decide +kernel
theorem ssa3p_99_1 : ssaOKPart (cfg3 99) 1 = true := by decide +kernel
theorem ssa3p_99_2 : ssaOKPart (cfg3 99) 2 = true := by decide +kernel
theorem ssa3p_99_3 : ssaOKPart (cfg3 99) 3 = true := by decide +kernel

theorem ssa3c_99 : ssaOK (cfg3 99) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_99_0 ssa3p_99_1 ssa3p_99_2 ssa3p_99_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
