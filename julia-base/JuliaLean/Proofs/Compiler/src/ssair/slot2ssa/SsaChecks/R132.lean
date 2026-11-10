import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 132 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_132_0 : ssaOKPart (cfg3 132) 0 = true := by decide +kernel
theorem ssa3p_132_1 : ssaOKPart (cfg3 132) 1 = true := by decide +kernel
theorem ssa3p_132_2 : ssaOKPart (cfg3 132) 2 = true := by decide +kernel
theorem ssa3p_132_3 : ssaOKPart (cfg3 132) 3 = true := by decide +kernel

theorem ssa3c_132 : ssaOK (cfg3 132) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_132_0 ssa3p_132_1 ssa3p_132_2 ssa3p_132_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
