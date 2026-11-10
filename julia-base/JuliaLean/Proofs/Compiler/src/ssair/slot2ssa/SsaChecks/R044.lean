import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 44 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_44_0 : ssaOKPart (cfg3 44) 0 = true := by decide +kernel
theorem ssa3p_44_1 : ssaOKPart (cfg3 44) 1 = true := by decide +kernel
theorem ssa3p_44_2 : ssaOKPart (cfg3 44) 2 = true := by decide +kernel
theorem ssa3p_44_3 : ssaOKPart (cfg3 44) 3 = true := by decide +kernel

theorem ssa3c_44 : ssaOK (cfg3 44) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_44_0 ssa3p_44_1 ssa3p_44_2 ssa3p_44_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
