import JuliaLean.Proofs.Compiler.src.ssair.domtree.Props

/-! Counterexamples, checked by kernel evaluation of the model. -/

namespace JuliaLean.Proofs.Compiler.src.ssair.domtree

open JuliaLean.Compiler.ssair

/-- 9 blocks in a shape `compute_basic_blocks` gives: fall-through from block 1, `GotoIfNot` or
`:enter` branches `[dest, next]`, a self loop on 8, and catch blocks 5 and 9 with the virtual
predecessor (blocks 2, 3 or 7 can be the `:enter` for 5, block 5 the one for 9). The DFS
preorder is the identity. Block 6 has predecessors 5 and 9, and its semidominator is 4, through
the path `4 -> 7 -> 8 -> 9 -> 6`. -/
def deleteCex : List (List Int) := [[2], [5, 3], [5, 4], [7, 5], [9, 6], [7], [5, 8], [8, 9], [6]]
def deleteCexZ : List Int := [1, 9, 5]

/-- Deleting `9 -> 6` leaves 5 as the only predecessor of 6, so a rebuild gives
`idom(6) = 5`; `domtree_delete_edge!` keeps `idom(6) = 2`, because `is_parent(9, 6)` and
`on_semidominator_path(9, 6)` are both false. -/
theorem deleteCex_stale :
    jmIs (constructDomtree (mkBlocks deleteCex deleteCexZ)) (fun dt =>
      jmIs (isParent dt.dfsTree 9 6) (· == false) &&
      jmIs (onSemidominatorPath dt 9 6) (· == false) &&
      jmIs (cfgDeleteEdge (mkBlocks deleteCex deleteCexZ) 9 6) fun b2 =>
        jmIs (domtreeDeleteEdge! dt b2 9 6) fun d2 =>
          jmIs (constructDomtree b2) fun d3 =>
            d2.idomsBB.toList == [0, 1, 2, 3, 2, 2, 2, 7, 2] &&
            d3.idomsBB.toList == [0, 1, 2, 3, 2, 5, 2, 7, 2]) = true := by
  decide +kernel

theorem deleteEdgeMatchesRebuild_refuted : ¬ DeleteEdgeMatchesRebuild := by
  intro h
  have hv : ValidSimpleCFG deleteCex deleteCexZ := by unfold ValidSimpleCFG ValidCFG; decide +kernel
  have := h deleteCex deleteCexZ 9 6 hv (by decide +kernel)
  have hf : deleteRebuildOK (mkBlocks deleteCex deleteCexZ) 9 6 = false := by decide +kernel
  rw [hf] at this
  exact Bool.false_ne_true this

/-- The first counterexample found (14 blocks, deleting `5 -> 3` keeps `idom(3) = 1` where a
rebuild gives 11). Its blocks 4, 11 and 14 have three successors, which `compute_basic_blocks`
never gives. -/
def deleteCex14 : List (List Int) :=
  [[12, 6], [], [], [14, 8, 7], [3, 4], [4], [12], [5, 11], [14], [], [8, 14, 3], [5, 11], [1],
   [13, 4, 11]]

theorem deleteCex14_stale :
    jmIs (constructDomtree (mkBlocks deleteCex14)) (fun dt =>
      jmIs (cfgDeleteEdge (mkBlocks deleteCex14) 5 3) fun b2 =>
        jmIs (domtreeDeleteEdge! dt b2 5 3) fun d2 =>
          jmIs (constructDomtree b2) fun d3 => idomAt d2 3 == 1 && idomAt d3 3 == 11) = true := by
  decide +kernel

/-- On `deleteCex` before the deletion: the model's semidominator of 6 is preorder 4, the same
as by definition; 9 is on the semidominator path `4 -> 7 -> 8 -> 9 -> 6` by definition; and
`on_semidominator_path(9, 6)` is false, because it follows the semidominators of 9 (preorder
9, then 5, then 2) and passes below 4 without meeting it. -/
theorem onSemiPath_miss :
    jmIs (constructDomtree (mkBlocks deleteCex deleteCexZ)) (fun dt =>
      let D := dt.dfsTree
      (dt.sncaState.toList.map (·.semi)).drop 1 == [1, 2, 3, 2, 4, 4, 7, 5] &&
      sdomDef (mkBlocks deleteCex deleteCexZ) D 6 == 4 &&
      onSdomPathDef (mkBlocks deleteCex deleteCexZ) D 4 9 6 &&
      jmIs (onSemidominatorPath dt 9 6) (· == false)) = true := by
  decide +kernel

theorem onSemiPathComplete_refuted : ¬ OnSemiPathComplete := by
  intro h
  have hv : ValidSimpleCFG deleteCex deleteCexZ := by unfold ValidSimpleCFG ValidCFG; decide +kernel
  have := h deleteCex deleteCexZ 9 6 hv (by decide +kernel)
  have hf : onSemiPathOK (mkBlocks deleteCex deleteCexZ) 9 6 = false := by decide +kernel
  rw [hf] at this
  exact Bool.false_ne_true this

/-- Two blocks; block 2 has only the virtual predecessor (a catch block whose `:enter` edge was
removed). -/
theorem naiveIdoms_typeError :
    (match naiveIdoms (mkBlocks [[], []] [1, 2]) false with
     | .error e => e == "julia:TypeError" | .ok _ => false) = true := by decide +kernel

theorem naiveIdomsReturns_refuted : ¬ NaiveIdomsReturns := by
  intro h
  have hv : ValidCFG [[], []] [1, 2] := by unfold ValidCFG; decide +kernel
  have := h [[], []] [1, 2] hv
  have hf : jmIs (naiveIdoms (mkBlocks [[], []] [1, 2]) false) (fun _ => true) = false := by
    decide +kernel
  rw [hf] at this
  exact Bool.false_ne_true this

/-- Two blocks, block 2 unreachable: `rename_nodes!` writes `from_pre[to_pre[2]] = from_pre[0]`. -/
theorem renameNodes_boundsError :
    (match constructDomtree (mkBlocks [[], []]) with
     | .ok dt => match renameNodes! dt #[1, 2] with
       | .error e => e == "julia:BoundsError" | .ok _ => false
     | .error _ => false) = true := by decide +kernel

theorem renameNodesIdentity_refuted : ¬ RenameNodesIdentity := by
  intro h
  have hv : ValidCFG [[], []] [1] := by unfold ValidCFG; decide +kernel
  have := h [[], []] [1] hv
  have hf : jmIs (constructDomtree (mkBlocks [[], []] [1])) (fun dt =>
      jmIs (renameNodes! dt (irange 1 ([[], []] : List (List Int)).length).toArray) fun d2 =>
        d2.idomsBB == dt.idomsBB) = false := by decide +kernel
  rw [hf] at this
  exact Bool.false_ne_true this

end JuliaLean.Proofs.Compiler.src.ssair.domtree
