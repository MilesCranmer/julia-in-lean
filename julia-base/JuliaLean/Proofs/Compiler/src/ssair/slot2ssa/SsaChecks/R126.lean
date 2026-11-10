import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 126 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_126_0 : ssaOKPart (cfg3 126) 0 = true := by decide +kernel
theorem ssa3p_126_1 : ssaOKPart (cfg3 126) 1 = true := by decide +kernel
theorem ssa3p_126_2 : ssaOKPart (cfg3 126) 2 = true := by decide +kernel
theorem ssa3p_126_3 : ssaOKPart (cfg3 126) 3 = true := by decide +kernel

theorem ssa3c_126 : ssaOK (cfg3 126) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_126_0 ssa3p_126_1 ssa3p_126_2 ssa3p_126_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
