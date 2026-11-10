import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 79 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_79_0 : ssaOKPart (cfg3 79) 0 = true := by decide +kernel
theorem ssa3p_79_1 : ssaOKPart (cfg3 79) 1 = true := by decide +kernel
theorem ssa3p_79_2 : ssaOKPart (cfg3 79) 2 = true := by decide +kernel
theorem ssa3p_79_3 : ssaOKPart (cfg3 79) 3 = true := by decide +kernel

theorem ssa3c_79 : ssaOK (cfg3 79) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_79_0 ssa3p_79_1 ssa3p_79_2 ssa3p_79_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
