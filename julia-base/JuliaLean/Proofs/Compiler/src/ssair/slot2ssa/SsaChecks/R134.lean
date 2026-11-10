import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 134 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_134_0 : ssaOKPart (cfg3 134) 0 = true := by decide +kernel
theorem ssa3p_134_1 : ssaOKPart (cfg3 134) 1 = true := by decide +kernel
theorem ssa3p_134_2 : ssaOKPart (cfg3 134) 2 = true := by decide +kernel
theorem ssa3p_134_3 : ssaOKPart (cfg3 134) 3 = true := by decide +kernel

theorem ssa3c_134 : ssaOK (cfg3 134) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_134_0 ssa3p_134_1 ssa3p_134_2 ssa3p_134_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
