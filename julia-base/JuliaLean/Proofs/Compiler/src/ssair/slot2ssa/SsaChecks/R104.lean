import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 104 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_104_0 : ssaOKPart (cfg3 104) 0 = true := by decide +kernel
theorem ssa3p_104_1 : ssaOKPart (cfg3 104) 1 = true := by decide +kernel
theorem ssa3p_104_2 : ssaOKPart (cfg3 104) 2 = true := by decide +kernel
theorem ssa3p_104_3 : ssaOKPart (cfg3 104) 3 = true := by decide +kernel

theorem ssa3c_104 : ssaOK (cfg3 104) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_104_0 ssa3p_104_1 ssa3p_104_2 ssa3p_104_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
