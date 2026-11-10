import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 96 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_96_0 : ssaOKPart (cfg3 96) 0 = true := by decide +kernel
theorem ssa3p_96_1 : ssaOKPart (cfg3 96) 1 = true := by decide +kernel
theorem ssa3p_96_2 : ssaOKPart (cfg3 96) 2 = true := by decide +kernel
theorem ssa3p_96_3 : ssaOKPart (cfg3 96) 3 = true := by decide +kernel

theorem ssa3c_96 : ssaOK (cfg3 96) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_96_0 ssa3p_96_1 ssa3p_96_2 ssa3p_96_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
