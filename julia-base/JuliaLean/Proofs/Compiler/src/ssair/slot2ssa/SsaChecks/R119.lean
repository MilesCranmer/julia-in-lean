import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 119 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_119_0 : ssaOKPart (cfg3 119) 0 = true := by decide +kernel
theorem ssa3p_119_1 : ssaOKPart (cfg3 119) 1 = true := by decide +kernel
theorem ssa3p_119_2 : ssaOKPart (cfg3 119) 2 = true := by decide +kernel
theorem ssa3p_119_3 : ssaOKPart (cfg3 119) 3 = true := by decide +kernel

theorem ssa3c_119 : ssaOK (cfg3 119) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_119_0 ssa3p_119_1 ssa3p_119_2 ssa3p_119_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
