import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 71 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_71_0 : ssaOKPart (cfg3 71) 0 = true := by decide +kernel
theorem ssa3p_71_1 : ssaOKPart (cfg3 71) 1 = true := by decide +kernel
theorem ssa3p_71_2 : ssaOKPart (cfg3 71) 2 = true := by decide +kernel
theorem ssa3p_71_3 : ssaOKPart (cfg3 71) 3 = true := by decide +kernel

theorem ssa3c_71 : ssaOK (cfg3 71) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_71_0 ssa3p_71_1 ssa3p_71_2 ssa3p_71_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
