import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 43 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_43_0 : ssaOKPart (cfg3 43) 0 = true := by decide +kernel
theorem ssa3p_43_1 : ssaOKPart (cfg3 43) 1 = true := by decide +kernel
theorem ssa3p_43_2 : ssaOKPart (cfg3 43) 2 = true := by decide +kernel
theorem ssa3p_43_3 : ssaOKPart (cfg3 43) 3 = true := by decide +kernel

theorem ssa3c_43 : ssaOK (cfg3 43) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_43_0 ssa3p_43_1 ssa3p_43_2 ssa3p_43_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
