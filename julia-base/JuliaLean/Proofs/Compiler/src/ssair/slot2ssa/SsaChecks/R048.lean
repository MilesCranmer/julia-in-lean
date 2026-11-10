import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 48 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_48_0 : ssaOKPart (cfg3 48) 0 = true := by decide +kernel
theorem ssa3p_48_1 : ssaOKPart (cfg3 48) 1 = true := by decide +kernel
theorem ssa3p_48_2 : ssaOKPart (cfg3 48) 2 = true := by decide +kernel
theorem ssa3p_48_3 : ssaOKPart (cfg3 48) 3 = true := by decide +kernel

theorem ssa3c_48 : ssaOK (cfg3 48) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_48_0 ssa3p_48_1 ssa3p_48_2 ssa3p_48_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
