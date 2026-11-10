import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 117 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_117_0 : ssaOKPart (cfg3 117) 0 = true := by decide +kernel
theorem ssa3p_117_1 : ssaOKPart (cfg3 117) 1 = true := by decide +kernel
theorem ssa3p_117_2 : ssaOKPart (cfg3 117) 2 = true := by decide +kernel
theorem ssa3p_117_3 : ssaOKPart (cfg3 117) 3 = true := by decide +kernel

theorem ssa3c_117 : ssaOK (cfg3 117) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_117_0 ssa3p_117_1 ssa3p_117_2 ssa3p_117_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
