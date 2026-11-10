import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 52 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_52_0 : ssaOKPart (cfg3 52) 0 = true := by decide +kernel
theorem ssa3p_52_1 : ssaOKPart (cfg3 52) 1 = true := by decide +kernel
theorem ssa3p_52_2 : ssaOKPart (cfg3 52) 2 = true := by decide +kernel
theorem ssa3p_52_3 : ssaOKPart (cfg3 52) 3 = true := by decide +kernel

theorem ssa3c_52 : ssaOK (cfg3 52) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_52_0 ssa3p_52_1 ssa3p_52_2 ssa3p_52_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
