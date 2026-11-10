import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 73 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_73_0 : ssaOKPart (cfg3 73) 0 = true := by decide +kernel
theorem ssa3p_73_1 : ssaOKPart (cfg3 73) 1 = true := by decide +kernel
theorem ssa3p_73_2 : ssaOKPart (cfg3 73) 2 = true := by decide +kernel
theorem ssa3p_73_3 : ssaOKPart (cfg3 73) 3 = true := by decide +kernel

theorem ssa3c_73 : ssaOK (cfg3 73) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_73_0 ssa3p_73_1 ssa3p_73_2 ssa3p_73_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
