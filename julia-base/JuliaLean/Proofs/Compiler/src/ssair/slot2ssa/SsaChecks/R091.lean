import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 91 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_91_0 : ssaOKPart (cfg3 91) 0 = true := by decide +kernel
theorem ssa3p_91_1 : ssaOKPart (cfg3 91) 1 = true := by decide +kernel
theorem ssa3p_91_2 : ssaOKPart (cfg3 91) 2 = true := by decide +kernel
theorem ssa3p_91_3 : ssaOKPart (cfg3 91) 3 = true := by decide +kernel

theorem ssa3c_91 : ssaOK (cfg3 91) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_91_0 ssa3p_91_1 ssa3p_91_2 ssa3p_91_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
