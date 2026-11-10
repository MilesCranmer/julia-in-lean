import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 67 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_67_0 : ssaOKPart (cfg3 67) 0 = true := by decide +kernel
theorem ssa3p_67_1 : ssaOKPart (cfg3 67) 1 = true := by decide +kernel
theorem ssa3p_67_2 : ssaOKPart (cfg3 67) 2 = true := by decide +kernel
theorem ssa3p_67_3 : ssaOKPart (cfg3 67) 3 = true := by decide +kernel

theorem ssa3c_67 : ssaOK (cfg3 67) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_67_0 ssa3p_67_1 ssa3p_67_2 ssa3p_67_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
