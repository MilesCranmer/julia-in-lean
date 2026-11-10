import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 127 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_127_0 : ssaOKPart (cfg3 127) 0 = true := by decide +kernel
theorem ssa3p_127_1 : ssaOKPart (cfg3 127) 1 = true := by decide +kernel
theorem ssa3p_127_2 : ssaOKPart (cfg3 127) 2 = true := by decide +kernel
theorem ssa3p_127_3 : ssaOKPart (cfg3 127) 3 = true := by decide +kernel

theorem ssa3c_127 : ssaOK (cfg3 127) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_127_0 ssa3p_127_1 ssa3p_127_2 ssa3p_127_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
