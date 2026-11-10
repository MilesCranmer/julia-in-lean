import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 77 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_77_0 : ssaOKPart (cfg3 77) 0 = true := by decide +kernel
theorem ssa3p_77_1 : ssaOKPart (cfg3 77) 1 = true := by decide +kernel
theorem ssa3p_77_2 : ssaOKPart (cfg3 77) 2 = true := by decide +kernel
theorem ssa3p_77_3 : ssaOKPart (cfg3 77) 3 = true := by decide +kernel

theorem ssa3c_77 : ssaOK (cfg3 77) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_77_0 ssa3p_77_1 ssa3p_77_2 ssa3p_77_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
