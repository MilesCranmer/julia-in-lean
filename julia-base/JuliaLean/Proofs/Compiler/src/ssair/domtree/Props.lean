import JuliaLean.Proofs.Compiler.src.ssair.domtree.Checks

/-!
The properties of `Compiler/src/ssair/domtree.jl` and of the CFG edits of
`Compiler/src/ssair/ir.jl` it relies on. Each property comes twice: over the small CFGs of
`smallCFGs` (proven by exhaustive kernel evaluation, see the `Bounded*` files) and over every
CFG (open). The checks they use are in `Checks.lean`, the definitions in `Spec.lean`.
-/

namespace JuliaLean.Proofs.Compiler.src.ssair.domtree

open JuliaLean.Compiler.ssair

/-- A CFG in the form `compute_basic_blocks` gives (Compiler/src/ssair/ir.jl:106-147), as
successor lists: at least one block, every successor a block, the virtual predecessor on block
1 and possibly on other blocks (catch blocks). Successor lists may repeat a block (an `:enter`
whose catch block is the next block). Predecessor lists are derived in the order of
`mkBlocks`; the dominator code takes a minimum or a set over them, so their order should not
matter, but the general statements below are only about this order. -/
def ValidCFG (succs : List (List Int)) (zp : List Int) : Prop :=
  succs ≠ [] ∧ (∀ l ∈ succs, ∀ x ∈ l, 1 ≤ x ∧ x ≤ succs.length) ∧ 1 ∈ zp ∧
    ∀ z ∈ zp, 1 ≤ z ∧ z ≤ succs.length

/-- As `ValidCFG`, and no successor list repeats a block, which `cfg_delete_edge!` and
`kill_edge!` assume ("Assumes that blocks appear at most once in preds and succs",
Compiler/src/ssair/ir.jl:24). -/
def ValidSimpleCFG (succs : List (List Int)) (zp : List Int) : Prop :=
  ValidCFG succs zp ∧ ∀ l ∈ succs, l.Nodup

/-! ### Over the small CFGs (bounded) -/

def ConstructDomtreeSmall : Prop := ∀ c ∈ smallCFGs, constructOK (mkBlocks c.1 c.2) false = true
def ConstructPostdomtreeSmall : Prop := ∀ c ∈ smallCFGs, constructOK (mkBlocks c.1 c.2) true = true
def InsertEdgeSmall : Prop := ∀ c ∈ smallCFGs, insertOK (mkBlocks c.1 c.2) = true
def DeleteEdgeSoundSmall : Prop := ∀ c ∈ smallCFGs, deleteSoundOK (mkBlocks c.1 c.2) = true
def CompressWorklistSmall : Prop := ∀ c ∈ smallCFGs, compressOK (mkBlocks c.1 c.2) = true
def NaiveIdomsSmall : Prop := ∀ c ∈ smallCFGs, naiveOK (mkBlocks c.1 c.2) = true
def RenameNodesSmall : Prop := ∀ c ∈ smallCFGs, renameOK (mkBlocks c.1 c.2) = true
def KillEdgeSmall : Prop := ∀ c ∈ smallCFGs, killOK (mkBlocks c.1 c.2) = true
def CfgEditSmall : Prop := ∀ c ∈ smallCFGs, cfgEditOK (mkBlocks c.1 c.2) = true

/-! ### Over every CFG (open) -/

def ConstructDomtreeAll : Prop :=
  ∀ succs zp, ValidCFG succs zp → constructOK (mkBlocks succs zp) false = true
def ConstructPostdomtreeAll : Prop :=
  ∀ succs zp, ValidCFG succs zp → constructOK (mkBlocks succs zp) true = true
def InsertEdgeAll : Prop :=
  ∀ succs zp, ValidSimpleCFG succs zp → insertOK (mkBlocks succs zp) = true
def DeleteEdgeSoundAll : Prop :=
  ∀ succs zp, ValidSimpleCFG succs zp → deleteSoundOK (mkBlocks succs zp) = true
def CompressWorklistAll : Prop :=
  ∀ succs zp, ValidCFG succs zp → compressOK (mkBlocks succs zp) = true
def NaiveIdomsAll : Prop :=
  ∀ succs zp, ValidCFG succs zp → naiveOK (mkBlocks succs zp) = true
def RenameNodesAll : Prop :=
  ∀ succs zp, ValidCFG succs zp → renameOK (mkBlocks succs zp) = true
def KillEdgeAll : Prop :=
  ∀ succs zp, ValidSimpleCFG succs zp → killOK (mkBlocks succs zp) = true
def CfgEditAll : Prop :=
  ∀ succs zp, ValidSimpleCFG succs zp → cfgEditOK (mkBlocks succs zp) = true

/-! ### Refuted -/

/-- After `cfg_delete_edge!(f, t)`, `domtree_delete_edge!` on the tree of the old CFG gives the
same `idoms_bb` as `construct_domtree` of the new CFG. -/
def deleteRebuildOK (blocks : Blocks) (f t : Int) : Bool :=
  jmIs (constructDomtree blocks) fun dt =>
    jmIs (cfgDeleteEdge blocks f t) fun b2 =>
      jmIs (domtreeDeleteEdge! dt b2 f t) fun d2 =>
        jmIs (constructDomtree b2) fun d3 => d2.idomsBB == d3.idomsBB

/-- The dynamic edge deletion gives the same tree as a rebuild from scratch, for every edge of
every CFG. -/
def DeleteEdgeMatchesRebuild : Prop :=
  ∀ succs zp f t, ValidSimpleCFG succs zp → t ∈ succs.getD (f - 1).toNat [] →
    deleteRebuildOK (mkBlocks succs zp) f t = true

/-- `on_semidominator_path(dt, f, t)` on the dominator tree of `blocks`, for an edge `f -> t` with
`f` reachable and `t` not block 1, is true whenever `f` lies on a semidominator path from the
semidominator of `t` (by definition, `sdomDef`) to `t` ending with that edge (`onSdomPathDef`). -/
def onSemiPathOK (blocks : Blocks) (f t : Int) : Bool :=
  jmIs (constructDomtree blocks) fun dt =>
    let D := dt.dfsTree
    D.toPre.getD (f - 1).toNat 0 == 0 || t == 1 ||
      !onSdomPathDef blocks D (sdomDef blocks D t) f t ||
      jmIs (onSemidominatorPath dt f t) id

/-- The docstring promise of `on_semidominator_path` (Compiler/src/ssair/domtree.jl:550-553:
"Check if x is on some semidominator path from the semidominator of y to y, assuming there is
an edge from x to y"), in the direction the deletion update needs: it never answers false when
`x` is on such a path. -/
def OnSemiPathComplete : Prop :=
  ∀ succs zp f t, ValidSimpleCFG succs zp → t ∈ succs.getD (f - 1).toNat [] →
    onSemiPathOK (mkBlocks succs zp) f t = true

/-- `naive_idoms(blocks)` returns (does not throw) for every CFG. -/
def NaiveIdomsReturns : Prop :=
  ∀ succs zp, ValidCFG succs zp → jmIs (naiveIdoms (mkBlocks succs zp) false) (fun _ => true) = true

/-- `rename_nodes!` with the identity renaming (every block kept, unreachable ones too) returns
and leaves `idoms_bb` unchanged, for every CFG. -/
def RenameNodesIdentity : Prop :=
  ∀ succs zp, ValidCFG succs zp →
    jmIs (constructDomtree (mkBlocks succs zp)) (fun dt =>
      jmIs (renameNodes! dt (irange 1 succs.length).toArray) fun d2 =>
        d2.idomsBB == dt.idomsBB) = true

end JuliaLean.Proofs.Compiler.src.ssair.domtree
