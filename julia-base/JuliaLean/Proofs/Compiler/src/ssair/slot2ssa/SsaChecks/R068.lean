import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 68 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_68_0 : ssaOKPart (cfg3 68) 0 = true := by decide +kernel
theorem ssa3p_68_1 : ssaOKPart (cfg3 68) 1 = true := by decide +kernel
theorem ssa3p_68_2 : ssaOKPart (cfg3 68) 2 = true := by decide +kernel
theorem ssa3p_68_3 : ssaOKPart (cfg3 68) 3 = true := by decide +kernel

theorem ssa3c_68 : ssaOK (cfg3 68) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_68_0 ssa3p_68_1 ssa3p_68_2 ssa3p_68_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
