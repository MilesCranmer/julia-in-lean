import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 133 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_133_0 : ssaOKPart (cfg3 133) 0 = true := by decide +kernel
theorem ssa3p_133_1 : ssaOKPart (cfg3 133) 1 = true := by decide +kernel
theorem ssa3p_133_2 : ssaOKPart (cfg3 133) 2 = true := by decide +kernel
theorem ssa3p_133_3 : ssaOKPart (cfg3 133) 3 = true := by decide +kernel

theorem ssa3c_133 : ssaOK (cfg3 133) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_133_0 ssa3p_133_1 ssa3p_133_2 ssa3p_133_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
