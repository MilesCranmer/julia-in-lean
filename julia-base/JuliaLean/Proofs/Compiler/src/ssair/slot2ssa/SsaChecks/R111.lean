import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 111 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_111_0 : ssaOKPart (cfg3 111) 0 = true := by decide +kernel
theorem ssa3p_111_1 : ssaOKPart (cfg3 111) 1 = true := by decide +kernel
theorem ssa3p_111_2 : ssaOKPart (cfg3 111) 2 = true := by decide +kernel
theorem ssa3p_111_3 : ssaOKPart (cfg3 111) 3 = true := by decide +kernel

theorem ssa3c_111 : ssaOK (cfg3 111) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_111_0 ssa3p_111_1 ssa3p_111_2 ssa3p_111_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
