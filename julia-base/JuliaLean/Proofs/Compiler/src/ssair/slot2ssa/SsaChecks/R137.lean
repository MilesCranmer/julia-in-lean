import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 137 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_137_0 : ssaOKPart (cfg3 137) 0 = true := by decide +kernel
theorem ssa3p_137_1 : ssaOKPart (cfg3 137) 1 = true := by decide +kernel
theorem ssa3p_137_2 : ssaOKPart (cfg3 137) 2 = true := by decide +kernel
theorem ssa3p_137_3 : ssaOKPart (cfg3 137) 3 = true := by decide +kernel

theorem ssa3c_137 : ssaOK (cfg3 137) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_137_0 ssa3p_137_1 ssa3p_137_2 ssa3p_137_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
