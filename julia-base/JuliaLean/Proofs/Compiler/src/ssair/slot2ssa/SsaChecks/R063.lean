import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 63 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_63_0 : ssaOKPart (cfg3 63) 0 = true := by decide +kernel
theorem ssa3p_63_1 : ssaOKPart (cfg3 63) 1 = true := by decide +kernel
theorem ssa3p_63_2 : ssaOKPart (cfg3 63) 2 = true := by decide +kernel
theorem ssa3p_63_3 : ssaOKPart (cfg3 63) 3 = true := by decide +kernel

theorem ssa3c_63 : ssaOK (cfg3 63) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_63_0 ssa3p_63_1 ssa3p_63_2 ssa3p_63_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
