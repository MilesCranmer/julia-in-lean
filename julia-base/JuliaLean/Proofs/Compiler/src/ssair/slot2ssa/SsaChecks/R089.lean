import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 89 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_89_0 : ssaOKPart (cfg3 89) 0 = true := by decide +kernel
theorem ssa3p_89_1 : ssaOKPart (cfg3 89) 1 = true := by decide +kernel
theorem ssa3p_89_2 : ssaOKPart (cfg3 89) 2 = true := by decide +kernel
theorem ssa3p_89_3 : ssaOKPart (cfg3 89) 3 = true := by decide +kernel

theorem ssa3c_89 : ssaOK (cfg3 89) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_89_0 ssa3p_89_1 ssa3p_89_2 ssa3p_89_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
