import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 107 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_107_0 : ssaOKPart (cfg3 107) 0 = true := by decide +kernel
theorem ssa3p_107_1 : ssaOKPart (cfg3 107) 1 = true := by decide +kernel
theorem ssa3p_107_2 : ssaOKPart (cfg3 107) 2 = true := by decide +kernel
theorem ssa3p_107_3 : ssaOKPart (cfg3 107) 3 = true := by decide +kernel

theorem ssa3c_107 : ssaOK (cfg3 107) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_107_0 ssa3p_107_1 ssa3p_107_2 ssa3p_107_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
