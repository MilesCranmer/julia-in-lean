import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 93 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_93_0 : ssaOKPart (cfg3 93) 0 = true := by decide +kernel
theorem ssa3p_93_1 : ssaOKPart (cfg3 93) 1 = true := by decide +kernel
theorem ssa3p_93_2 : ssaOKPart (cfg3 93) 2 = true := by decide +kernel
theorem ssa3p_93_3 : ssaOKPart (cfg3 93) 3 = true := by decide +kernel

theorem ssa3c_93 : ssaOK (cfg3 93) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_93_0 ssa3p_93_1 ssa3p_93_2 ssa3p_93_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
