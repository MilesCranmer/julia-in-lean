import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 97 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_97_0 : ssaOKPart (cfg3 97) 0 = true := by decide +kernel
theorem ssa3p_97_1 : ssaOKPart (cfg3 97) 1 = true := by decide +kernel
theorem ssa3p_97_2 : ssaOKPart (cfg3 97) 2 = true := by decide +kernel
theorem ssa3p_97_3 : ssaOKPart (cfg3 97) 3 = true := by decide +kernel

theorem ssa3c_97 : ssaOK (cfg3 97) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_97_0 ssa3p_97_1 ssa3p_97_2 ssa3p_97_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
