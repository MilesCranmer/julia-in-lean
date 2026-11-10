import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.Spec

/-!
The Boolean checks of the bounded properties of `Compiler/src/ssair/slot2ssa.jl`. Each check runs
the model of the Julia function on one CFG of `cfgsUpTo3` in `Props.lean` (with the dominator
tree the model of `construct_domtree` builds for it) and compares the result with the reference
definitions of `Spec.lean`.
-/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

/-- The blocks reachable from the entry, increasing. -/
def reachableBlocks (I : DomInfo) (blocks : Blocks) : List Int :=
  (blockIds blocks).filter I.reachable

/-- For every subset of the reachable blocks, in every order, `iterated_dominance_frontier`
without liveness (`live_in_bbs === nothing`) returns, without a repeated block, exactly the
iterated dominance frontier of the subset by definition. -/
def idfOK (blocks : Blocks) : Bool :=
  jmIs (constructDomtree blocks) fun dt =>
    let I := domInfo blocks false
    (subsetsOf (reachableBlocks I blocks)).all fun s => (perms s).all fun d =>
      jmIs (iteratedDominanceFrontier (mkSCFG blocks) ⟨d.toArray, none⟩ dt) fun r =>
        nodupInt r.toList && sameSet r.toList (idfDef I blocks d)

/-- Every def/use pattern of `Spec.patLists` over the blocks (one pattern per block, with and
without the argument def `0`). -/
def allPats : Nat → List (List Nat)
  | 0 => [[]]
  | k + 1 => [0, 1, 2, 3].flatMap fun p => (allPats k).map (p :: ·)

/-- For every def/use pattern whose defs are all in reachable blocks: `compute_live_ins` returns
`def_bbs` = the blocks with a def, and `live_in_bbs` = the live-in blocks by definition without a
repeated block; and `iterated_dominance_frontier` with that liveness returns, without a repeated
block, exactly the pruned phi positions: the iterated dominance frontier of the def blocks
intersected with the live-in blocks. -/
def prunedOK (blocks : Blocks) : Bool :=
  jmIs (constructDomtree blocks) fun dt =>
    let I := domInfo blocks false
    let cfg := mkSCFG blocks
    (allPats blocks.size).all fun pats => [false, true].all fun isArg =>
      let (defs, uses) := patLists pats isArg
      let dblocks := (blockIds blocks).filter (hasDef defs)
      !(dblocks.all I.reachable) ||
      jmIs (computeLiveIns cfg defs.toArray uses.toArray) fun live =>
        let ld := liveDef blocks defs uses
        let L := (live.liveInBBs.getD #[-7]).toList
        nodupInt live.defBBs.toList && sameSet live.defBBs.toList dblocks &&
        live.liveInBBs.isSome && nodupInt L && sameSet L ld &&
        jmIs (iteratedDominanceFrontier cfg live dt) fun r =>
          nodupInt r.toList && sameSet r.toList ((idfDef I blocks dblocks).filter ld.contains)

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
