import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.SsaChecks.Common

/-! Splitting `ssaOK` on one 3-block CFG by the pattern of block 1, so that each kernel check stays within memory. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

/-- CFG `j` (0-based) of `juliaCFGs 3`. -/
def cfg3 (j : Nat) : List (List Int) := (juliaCFGs 3).getD j []

/-- `ssaOK` on a 3-block CFG for the patterns whose block 1 has pattern `p0`. -/
def ssaOKPart (succs : List (List Int)) (p0 : Nat) : Bool :=
  ((allPats 2).map (p0 :: ·)).all fun pats => [false, true].all fun isArg =>
    !readsAssigned succs pats isArg ||
    let (I, ir) := ssaCase succs pats isArg
    jmIs (slot2regSsa I ir) ssaPropsOK

theorem ssaOK_of_parts (succs : List (List Int)) (h : succs.length = 3)
    (h0 : ssaOKPart succs 0 = true) (h1 : ssaOKPart succs 1 = true)
    (h2 : ssaOKPart succs 2 = true) (h3 : ssaOKPart succs 3 = true) : ssaOK succs = true := by
  unfold ssaOK
  rw [h, show allPats 3 = [0, 1, 2, 3].flatMap (fun p => (allPats 2).map (p :: ·)) from rfl]
  unfold ssaOKPart at h0 h1 h2 h3
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.all_append, h0, h1, h2,
    h3, Bool.and_self]

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
