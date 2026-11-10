import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 86 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_86_0 : ssaOKPart (cfg3 86) 0 = true := by decide +kernel
theorem ssa3p_86_1 : ssaOKPart (cfg3 86) 1 = true := by decide +kernel
theorem ssa3p_86_2 : ssaOKPart (cfg3 86) 2 = true := by decide +kernel
theorem ssa3p_86_3 : ssaOKPart (cfg3 86) 3 = true := by decide +kernel

theorem ssa3c_86 : ssaOK (cfg3 86) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_86_0 ssa3p_86_1 ssa3p_86_2 ssa3p_86_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
