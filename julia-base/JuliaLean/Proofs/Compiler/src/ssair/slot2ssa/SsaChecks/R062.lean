import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 62 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_62_0 : ssaOKPart (cfg3 62) 0 = true := by decide +kernel
theorem ssa3p_62_1 : ssaOKPart (cfg3 62) 1 = true := by decide +kernel
theorem ssa3p_62_2 : ssaOKPart (cfg3 62) 2 = true := by decide +kernel
theorem ssa3p_62_3 : ssaOKPart (cfg3 62) 3 = true := by decide +kernel

theorem ssa3c_62 : ssaOK (cfg3 62) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_62_0 ssa3p_62_1 ssa3p_62_2 ssa3p_62_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
