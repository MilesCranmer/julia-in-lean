import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 112 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_112_0 : ssaOKPart (cfg3 112) 0 = true := by decide +kernel
theorem ssa3p_112_1 : ssaOKPart (cfg3 112) 1 = true := by decide +kernel
theorem ssa3p_112_2 : ssaOKPart (cfg3 112) 2 = true := by decide +kernel
theorem ssa3p_112_3 : ssaOKPart (cfg3 112) 3 = true := by decide +kernel

theorem ssa3c_112 : ssaOK (cfg3 112) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_112_0 ssa3p_112_1 ssa3p_112_2 ssa3p_112_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
