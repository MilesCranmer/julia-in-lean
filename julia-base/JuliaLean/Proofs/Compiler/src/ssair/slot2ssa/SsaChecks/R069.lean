import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Part

/-! Kernel check of `ssaOK` on CFG 69 (0-based) of `juliaCFGs 3`, in four parts. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

theorem ssa3p_69_0 : ssaOKPart (cfg3 69) 0 = true := by decide +kernel
theorem ssa3p_69_1 : ssaOKPart (cfg3 69) 1 = true := by decide +kernel
theorem ssa3p_69_2 : ssaOKPart (cfg3 69) 2 = true := by decide +kernel
theorem ssa3p_69_3 : ssaOKPart (cfg3 69) 3 = true := by decide +kernel

theorem ssa3c_69 : ssaOK (cfg3 69) = true :=
  ssaOK_of_parts _ (by decide +kernel) ssa3p_69_0 ssa3p_69_1 ssa3p_69_2 ssa3p_69_3

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
