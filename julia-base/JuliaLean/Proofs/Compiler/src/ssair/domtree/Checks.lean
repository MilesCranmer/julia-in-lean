import JuliaLean.Proofs.Compiler.src.ssair.domtree.Spec

/-!
The Boolean checks of the bounded properties of `Compiler/src/ssair/domtree.jl`, and the family
of small CFGs they range over. Each check runs the model of the Julia function on one CFG and
compares the result with the definitions in `Spec.lean`.
-/

namespace JuliaLean.Proofs.Compiler.src.ssair.domtree

open JuliaLean.Compiler.ssair

/-- The subsets of `xs`, each in the order of `xs`. -/
def subsetsOf : List Int → List (List Int)
  | [] => [[]]
  | x :: xs => let r := subsetsOf xs; r ++ r.map (x :: ·)

/-- All orderings of a list. -/
def perms : List Int → List (List Int)
  | [] => [[]]
  | x :: xs => (perms xs).flatMap fun p =>
      (List.range (p.length + 1)).map fun i => p.take i ++ [x] ++ p.drop i

/-- Successor lists without repeated blocks, in every order. -/
def succChoices (n : Nat) : List (List Int) := (subsetsOf (irange 1 n)).flatMap perms

/-- Every list of `k` choices. -/
def cfgsOver (choices : List (List Int)) : Nat → List (List (List Int))
  | 0 => [[]]
  | k + 1 => choices.flatMap fun c => (cfgsOver choices k).map (c :: ·)

/-- Every CFG with exactly `n` blocks whose successor lists have no repeated block, with the
successors of each block in any order (`n = 3`: 16 choices per block, 4096 CFGs). -/
def cfgsOfSize (n : Nat) : List (List (List Int)) := cfgsOver (succChoices n) n

/-- The CFGs with 1 or 2 blocks of `smallCFGs`. -/
def smallCFGs12 : List (List (List Int) × List Int) :=
  ((cfgsOfSize 1).map fun s => (s, [1])) ++
  ((cfgsOfSize 2).flatMap fun s => [(s, [1]), (s, [1, 2])])

/-- The 3-block CFGs of `smallCFGs` whose block 1 has the successors `c`. -/
def slice3 (c : List Int) : List (List (List Int) × List Int) :=
  (cfgsOver (subsetsOf (irange 1 3)) 2).map fun s => (c :: s, [1])

/-- The successor lists `compute_basic_blocks` (Compiler/src/ssair/ir.jl:106-147) can give block
`i` of `n`: none (`return`), `[d]` (`goto`, or fall-through when `d = i + 1`), and, when `i < n`,
`[d, i + 1]` with `d ≠ i + 1` (`GotoIfNot`, or `:enter` with catch block `d`). -/
def lowerChoices (n i : Nat) : List (List Int) :=
  [] :: (irange 1 n).map (fun d => [d]) ++
    (if i < n then ((irange 1 n).filter (· != (i : Int) + 1)).map fun d => [d, (i : Int) + 1]
     else [])

/-- The 3-block CFGs `compute_basic_blocks` can give that are not already in `slice3`: block 1
branches with `[3, 2]` (the order a forward `GotoIfNot` gives, destination first), blocks 2 and 3
are any of `lowerChoices`; with the virtual predecessor on block 1, and also on block 3 (block
1 an `:enter` whose catch block is 3). 48 CFGs. -/
def lower3 : List (List (List Int) × List Int) :=
  (lowerChoices 3 2).flatMap fun b2 => (lowerChoices 3 3).flatMap fun b3 =>
    [([[3, 2], b2, b3], [1]), ([[3, 2], b2, b3], [1, 3])]

/-- Larger CFGs in the shapes `compute_basic_blocks` gives, chosen because they reach the
branches the 3-block CFGs cannot (found with a Julia copy of `SNCA!`'s semidominator loop,
difftest/compiler/domtree_branches.jl): forward and in post-dominance, the update branch of
`snca_compress!` (lines 454-459) and its recursive call, which is the push branch of
`snca_compress_worklist!` (lines 476-479); then two chains, where `kill_edge!` recurses five and
three levels deep; then the 9-block CFG of `compiler-domtree-delete-stale-idom` (with catch
blocks 5 and 9). -/
def branchFwdRec : List (List (List Int)) :=
  [[[2], [3], [4], [5], [2], []], [[2], [5, 3], [4], [5], [2], []],
   [[3, 2], [], [1, 4], [5], [2, 6], []], [[5, 2], [1], [1, 4], [2], [3], []],
   [[2], [4, 3], [1, 4], [5], [2, 6], []], [[4, 2], [6, 3], [4], [6, 5], [2, 6], []]]
def branchFwdUpd : List (List (List Int)) :=
  [[[2], [3], [4], [2], []], [[3, 2], [3], [4], [2], []], [[2], [3], [2, 4], [2], []],
   [[5, 2], [4], [2], [3, 5], []], [[2], [1, 3], [5, 4], [2, 5], []],
   [[4], [3], [1, 4], [4, 5], [3], []]]
def branchPostRec : List (List (List Int)) :=
  [[[2], [3], [4], [1, 5], []], [[5, 2], [3], [4], [1], []], [[4, 2], [3], [4], [1, 5], []],
   [[2], [3], [4], [], [1, 6], []], [[2], [4, 3], [2], [6], [3, 6], []],
   [[3, 2], [6, 3], [3, 4], [4, 5], [1, 6], []]]
def branchPostUpd : List (List (List Int)) :=
  [[[2], [3], [1, 4], []], [[4], [4, 3], [1], []], [[2], [4, 3], [1], [], []],
   [[3], [1, 3], [], [2, 5], []], [[5, 2], [3], [6, 4], [], [6], []],
   [[], [], [6, 4], [5], [], []]]
def branchChains : List (List (List Int)) :=
  [[[2], [3], [4], [5], [6], [7], []], [[2, 3], [4], [4], [5, 6], [7], [7], []]]
def branchCex : List (List (List Int) × List Int) :=
  [([[2], [5, 3], [5, 4], [7, 5], [9, 6], [7], [5, 8], [8, 9], [6]], [1, 9, 5])]

def branchCFGs : List (List (List Int) × List Int) :=
  (branchFwdRec ++ branchFwdUpd ++ branchPostRec ++ branchPostUpd ++ branchChains).map
    (fun s => (s, [1])) ++ branchCex

theorem branchCFGs_of_parts (P : List (List Int) × List Int → Bool)
    (h1 : (branchFwdRec.map fun s => (s, [1])).all P = true)
    (h2 : (branchFwdUpd.map fun s => (s, [1])).all P = true)
    (h3 : (branchPostRec.map fun s => (s, [1])).all P = true)
    (h4 : (branchPostUpd.map fun s => (s, [1])).all P = true)
    (h5 : (branchChains.map fun s => (s, [1])).all P = true)
    (h6 : branchCex.all P = true) : branchCFGs.all P = true := by
  simp only [branchCFGs, List.map_append, List.all_append, h1, h2, h3, h4, h5, h6, Bool.and_self]

/-- The CFGs the bounded properties range over, as successor lists and the blocks with a
virtual predecessor `0`:

* every CFG with 1 or 2 blocks, successor lists without a repeated block in any order, with the
  virtual predecessor on block 1, and also on block 2 (a catch block);
* every CFG with 3 blocks whose successor lists are increasing (no repeated block), with the
  virtual predecessor on block 1;
* `lower3`: the other 3-block CFGs `compute_basic_blocks` can give (block 1 `[3, 2]`);
* `branchCFGs`: 27 CFGs of 4 to 9 blocks that reach path compression, its recursion and deep
  `kill_edge!` recursion.

That is 2 + 50 + 512 + 48 + 27 CFGs. They include self loops, the irreducible loop `1 -> 2,
1 -> 3, 2 <-> 3`, back edges into block 1, unreachable blocks and unreachable cycles, catch
blocks, and blocks with no successors (exits). -/
def smallCFGs : List (List (List Int) × List Int) :=
  smallCFGs12 ++ (subsetsOf (irange 1 3)).flatMap slice3 ++ lower3 ++ branchCFGs

/-- `JM` result `r` succeeded with a value that satisfies `p`. -/
def jmIs {α : Type} (r : JM α) (p : α → Bool) : Bool :=
  match r with
  | .ok x => p x
  | .error _ => false

/-- `idoms_bb[b]` (or a sentinel that no check accepts when out of range). -/
def idomAt (dt : GenericDomTree) (b : Int) : Int := dt.idomsBB.getD (b - 1).toNat (-7)

def levelAt (dt : GenericDomTree) (b : Int) : Int :=
  (dt.nodes.getD (b - 1).toNat ⟨-7, #[]⟩).level

def childrenAt (dt : GenericDomTree) (b : Int) : List Int :=
  (dt.nodes.getD (b - 1).toNat ⟨-7, #[-7]⟩).children.toList

/-- `dt` is the (post-)dominator tree of `blocks` by definition:

* `idoms_bb` and `nodes` have one entry per block;
* `idoms_bb[b]` is the immediate (post-)dominator of every reachable `b` (`0` for the entry
  block, and for the virtual exit), and `0` for unreachable blocks;
* `nodes[d].children` are the blocks whose immediate dominator is `d`, in increasing order;
* `nodes[b].level` is 1 for the roots (and unreachable blocks), and one more than the level of
  the immediate dominator otherwise ("how deep we are in the DomTree");
* `dominates`/`postdominates(dt, a, b)` is true exactly when `a == b` or `a` (post-)dominates `b`
  by definition, for all blocks `a` and `b`, so it is false when `b` is unreachable;
* `nearest_common_dominator(dt, a, b)` is the nearest common (post-)dominator by definition for
  all reachable `a` and `b` (the virtual exit is `0`);
* forward only: `bb_unreachable(dt, b)` is true exactly for the unreachable blocks other than 1,
  and `dominated(dt, r)` yields exactly `r` and the blocks `r` dominates. -/
def treeOK (blocks : Blocks) (isPost : Bool) (dt : GenericDomTree) : Bool :=
  let I := domInfo blocks isPost
  let ids := blockIds blocks
  dt.idomsBB.size == blocks.size && dt.nodes.size == blocks.size &&
  ids.all (fun b => I.idomOK b (idomAt dt b)) &&
  ids.all (fun d => childrenAt dt d == ids.filter (fun b => idomAt dt b == d)) &&
  ids.all (fun b => levelAt dt b ==
    (if idomAt dt b == 0 then 1 else levelAt dt (idomAt dt b) + 1)) &&
  ids.all (fun a => ids.all fun b => jmIs (dominates dt a b) (· == (a == b || I.dom a b))) &&
  ids.all (fun a => ids.all fun b => !(I.reachable a && I.reachable b) ||
    jmIs (nearestCommonDominator dt a b) (I.isNCD a b ·)) &&
  (isPost ||
    (ids.all (fun b => jmIs (bbUnreachable dt b) (· == (b != 1 && !I.reachable b))) &&
     ids.all (fun r => jmIs (dominated dt r)
       (fun xs => isortInt xs.toList == ids.filter (fun b => b == r || I.dom r b)))))

/-- `construct_domtree` (`isPost = false`) or `construct_postdomtree` succeeds on `blocks` and
gives the tree of the definition. -/
def constructOK (blocks : Blocks) (isPost : Bool) : Bool :=
  jmIs (if isPost then constructPostdomtree blocks else constructDomtree blocks)
    (treeOK blocks isPost)

/-- For every new edge `f -> t` (`t` not yet a successor of `f`, as `cfg_insert_edge!`
assumes), `cfg_insert_edge!` followed by `domtree_insert_edge!` on the tree of `blocks` gives the
dominator tree of the new CFG by definition. -/
def insertOK (blocks : Blocks) : Bool :=
  jmIs (constructDomtree blocks) fun dt =>
    (blockIds blocks).all fun f => (blockIds blocks).all fun t =>
      ((blocks.getD (f - 1).toNat default).succs.contains t) ||
      jmIs (cfgInsertEdge blocks f t) fun b2 =>
        jmIs (domtreeInsertEdge! dt b2 f t) (treeOK b2 false)

/-- For every edge `f -> t`, after `cfg_delete_edge!` and `domtree_delete_edge!` on the tree of
`blocks`, on the new CFG:

* `idoms_bb` and `nodes` have one entry per block, `nodes[d].children` are the blocks whose
  `idoms_bb` is `d` in increasing order, and the levels are depths in that tree;
* `bb_unreachable` is exact;
* every reachable block other than 1 has a non-zero `idoms_bb`, and it is a strict dominator by
  definition (so the tree is a tree of real dominators, not merely empty);
* every `dominates(dt, a, b)` that is true holds by definition (the tree claims no dominance
  that is false).

It does not say that `idoms_bb` is the immediate dominator; that is refuted
(`compiler-domtree-delete-stale-idom`). -/
def deleteSoundOK (blocks : Blocks) : Bool :=
  jmIs (constructDomtree blocks) fun dt =>
    (blockIds blocks).all fun f =>
      (blocks.getD (f - 1).toNat default).succs.toList.all fun t =>
        jmIs (cfgDeleteEdge blocks f t) fun b2 =>
          jmIs (domtreeDeleteEdge! dt b2 f t) fun d2 =>
            let I := domInfo b2 false
            let ids := blockIds b2
            d2.idomsBB.size == b2.size && d2.nodes.size == b2.size &&
            ids.all (fun d => childrenAt d2 d == ids.filter (fun b => idomAt d2 b == d)) &&
            ids.all (fun b => levelAt d2 b ==
              (if idomAt d2 b == 0 then 1 else levelAt d2 (idomAt d2 b) + 1)) &&
            ids.all (fun b => jmIs (bbUnreachable d2 b) (· == (b != 1 && !I.reachable b))) &&
            ids.all (fun b => b == 1 || !I.reachable b ||
              (idomAt d2 b != 0 && idomAt d2 b != b && I.dom (idomAt d2 b) b)) &&
            ids.all fun a => ids.all fun b =>
              jmIs (dominates d2 a b) fun r => !r || a == b || I.dom a b

/-- The semidominator loop of `SNCA!` from scratch (`max_pre = length(D)`), with the choice
between `snca_compress!` (`small`) and `snca_compress_worklist!` made by the caller instead of by
`length(ancestors) <= 32`. The lines before the loop are those of `SNCA!` (its second
initialization loop is empty when `max_pre = n_nodes`). -/
def sncaSemisWith (blocks : Blocks) (isPost small : Bool) : JM (Array SNCAData × Array Int) := do
  let D ← DFS! (DFSTree.new 0) blocks isPost
  let nNodes := D.length
  let maxPre : Int := nNodes
  let fuel := 4 * (nNodes + 2)
  let state := JuliaLean.Compiler.ssair.resize (#[] : Array SNCAData) nNodes ⟨0, 0⟩
  let state ← (irange 1 maxPre).foldlM (fun st w => aset st w ⟨typemaxInt, w⟩) state
  let relevant := if isPost then irange 1 maxPre else irange 2 maxPre
  sncaSemiLoop fuel blocks isPost D small relevant.reverse state D.toParentPre

def sncaKey (r : Array SNCAData × Array Int) : List (Int × Int) × List Int :=
  (r.1.toList.map fun d => (d.semi, d.label), r.2.toList)

/-- `snca_compress_worklist!` and `snca_compress!` leave the same SNCA state (semidominators and
labels) and ancestors, in both directions. -/
def compressOK (blocks : Blocks) : Bool :=
  [false, true].all fun isPost =>
    jmIs (sncaSemisWith blocks isPost true) fun r1 =>
      jmIs (sncaSemisWith blocks isPost false) fun r2 => decide (sncaKey r1 = sncaKey r2)

/-- Some block other than block 1 has predecessors, all of them the virtual `0`. -/
def hasOnlyVirtualPred (blocks : Blocks) : Bool :=
  (blockIds blocks).any fun b => b != 1 &&
    let ps := (blocks.getD (b - 1).toNat default).preds
    !ps.isEmpty && ps.all (· == 0)

/-- `naive_idoms(blocks, is_post_dominator)` gives the immediate (post-)dominator of every block
(the same expectation as `idoms_bb`), in both directions; forward, CFGs where a block other
than 1 has only the virtual predecessor are left out (see `compiler-domtree-naive-only-virtual-pred`). -/
def naiveOK (blocks : Blocks) : Bool :=
  [false, true].all fun isPost =>
    (!isPost && hasOnlyVirtualPred blocks) ||
    jmIs (naiveIdoms blocks isPost) fun ids =>
      let I := domInfo blocks isPost
      ids.size == blocks.size && (blockIds blocks).all fun b => I.idomOK b (ids.getD (b - 1).toNat (-7))

/-- The renaming that drops the unreachable blocks and numbers the others in order, as
`CFGTransformState!` builds it (Compiler/src/ssair/ir.jl:786-795). -/
def dropUnreachable (blocks : Blocks) : Array Int :=
  let I := domInfo blocks false
  ((blockIds blocks).foldl (fun (acc : List Int × Int) b =>
    if b == 1 || I.reachable b then (acc.1 ++ [acc.2 + 1], acc.2 + 1) else (acc.1 ++ [-1], acc.2))
    ([], 0)).1.toArray

/-- The CFG with the blocks renamed by `r`: dropped blocks are removed, and so are edges out of
them; the virtual predecessor `0` stays. -/
def renameCFG (blocks : Blocks) (r : Array Int) : Blocks :=
  let rn (b : Int) : Int := r.getD (b - 1).toNat (-1)
  ((blockIds blocks).filterMap fun b =>
    if rn b == -1 then none else
      let bb := blocks.getD (b - 1).toNat default
      some (⟨(bb.preds.toList.filterMap fun p =>
          if p == 0 then some 0 else if rn p == -1 then none else some (rn p)).toArray,
        bb.succs.map rn⟩ : BasicBlock)).toArray

def treeKey (dt : GenericDomTree) : List Int × List Int × List Int × List Int × List Int ×
    List Int × List Int × List Int × List (List Int) :=
  (dt.dfsTree.toPre.toList, dt.dfsTree.fromPre.toList, dt.dfsTree.toPost.toList,
   dt.dfsTree.fromPost.toList, dt.dfsTree.toParentPre.toList,
   dt.sncaState.toList.map (·.semi), dt.idomsBB.toList,
   dt.nodes.toList.map (·.level), dt.nodes.toList.map (·.children.toList))

/-- `rename_nodes!(construct_domtree(blocks), r)`, with `r` the renaming that drops the
unreachable blocks, gives the same DFS numbering, semidominators, `idoms_bb` and `nodes` as
`construct_domtree` of the renamed CFG. -/
def renameOK (blocks : Blocks) : Bool :=
  let r := dropUnreachable blocks
  jmIs (constructDomtree blocks) fun dt =>
    jmIs (renameNodes! dt r) fun d1 =>
      jmIs (constructDomtree (renameCFG blocks r)) fun d2 => treeKey d1 == treeKey d2

def edgeList (blocks : Blocks) : List Int :=
  (blockIds blocks).flatMap fun a =>
    (blocks.getD (a - 1).toNat default).succs.toList.map fun b => 1000 * a + b

def predsAt (blocks : Blocks) (b : Int) : Array Int := (blocks.getD (b - 1).toNat default).preds
def succsAt (blocks : Blocks) (b : Int) : Array Int := (blocks.getD (b - 1).toNat default).succs

/-- For every edge `f -> t`, `kill_edge!(bbs, f, t, callback)` with a callback that records its
calls:

* leaves `preds` and `succs` consistent (each edge once in both, the virtual `0`s unchanged);
* removes exactly the recorded edges, the last recorded being `f -> t`;
* removes an edge other than `f -> t` only when its source has no predecessors left, and
  removes every edge out of a block whose last predecessor it removed. -/
def killOK (blocks : Blocks) : Bool :=
  let ids := blockIds blocks
  ids.all fun f => (succsAt blocks f).toList.all fun t =>
    jmIs (killEdge (fun _ a c (s : List (Int × Int)) => pure (s ++ [(a, c)]))
        (edgeCount blocks + 2) blocks f t []) fun (b2, rec) =>
      (ids.all fun a => ids.all fun b =>
        (succsAt b2 a).toList.count b == (predsAt b2 b).toList.count a) &&
      (ids.all fun b => (predsAt b2 b).toList.count 0 == (predsAt blocks b).toList.count 0) &&
      rec.getLast? == some (f, t) &&
      isortInt (edgeList blocks) == isortInt (edgeList b2 ++ rec.map fun e => 1000 * e.1 + e.2) &&
      (rec.all fun e => !(predsAt b2 e.2).isEmpty || (succsAt b2 e.2).isEmpty) &&
      (rec.all fun e => e == (f, t) || (predsAt b2 e.1).isEmpty)

/-- `cfg_insert_edge!(cfg, f, t)` for every pair of blocks appends `f` to the predecessors of
`t` and `t` to the successors of `f` and changes nothing else; `cfg_delete_edge!(cfg, f, t)` for
every edge removes the first `f` from the predecessors of `t` and the first `t` from the
successors of `f` and changes nothing else. -/
def cfgEditOK (blocks : Blocks) : Bool :=
  let ids := blockIds blocks
  (ids.all fun f => ids.all fun t =>
    jmIs (cfgInsertEdge blocks f t) fun b2 => b2.size == blocks.size && ids.all fun b =>
      (succsAt b2 b).toList == (succsAt blocks b).toList ++ (if b == f then [t] else []) &&
      (predsAt b2 b).toList == (predsAt blocks b).toList ++ (if b == t then [f] else [])) &&
  (ids.all fun f => (succsAt blocks f).toList.all fun t =>
    jmIs (cfgDeleteEdge blocks f t) fun b2 => b2.size == blocks.size && ids.all fun b =>
      (succsAt b2 b).toList ==
        (if b == f then (succsAt blocks b).toList.erase t else (succsAt blocks b).toList) &&
      (predsAt b2 b).toList ==
        (if b == t then (predsAt blocks b).toList.erase f else (predsAt blocks b).toList))

/-- Every bounded property holds on all of `smallCFGs` once it holds on `smallCFGs12`, on each
of the eight slices of 3-block CFGs, on `lower3` and on `branchCFGs`. -/
theorem smallCFGs_of_slices (P : List (List Int) × List Int → Bool)
    (h12 : smallCFGs12.all P = true)
    (h0 : (slice3 []).all P = true) (h1 : (slice3 [3]).all P = true)
    (h2 : (slice3 [2]).all P = true) (h3 : (slice3 [2, 3]).all P = true)
    (h4 : (slice3 [1]).all P = true) (h5 : (slice3 [1, 3]).all P = true)
    (h6 : (slice3 [1, 2]).all P = true) (h7 : (slice3 [1, 2, 3]).all P = true)
    (hl : lower3.all P = true) (hb : branchCFGs.all P = true) :
    ∀ c ∈ smallCFGs, P c = true := by
  have hs : subsetsOf (irange 1 3) = [[], [3], [2], [2, 3], [1], [1, 3], [1, 2], [1, 2, 3]] := by
    decide
  apply List.all_eq_true.mp
  simp only [smallCFGs, hs, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.all_append, h12, h0, h1, h2, h3, h4, h5, h6, h7, hl, hb, Bool.and_self]

/-- The semidominator of `y` by definition, as a preorder number of the DFS tree `D`: the least
`pre(v)` over the paths `v -> ... -> y` whose inner nodes all have preorder numbers above
`pre(y)` (the virtual predecessor 0 and unreachable blocks are no nodes). `S` is the set of
nodes from which `y` is reached through such nodes, `y` included. -/
def sdomDef (blocks : Blocks) (D : DFSTree) (y : Int) : Int :=
  let pre (b : Int) : Int := D.toPre.getD (b - 1).toNat 0
  let py := pre y
  let preds (u : Int) : List Int := (predsAt blocks u).toList.filter fun p => p != 0 && pre p != 0
  let S := layers (fun u => (preds u).filter (pre · > py)) (-1) (blocks.size + 1) [y]
  (S.flatMap preds).foldl (fun m p => min m (pre p)) typemaxInt

/-- `x` lies on a semidominator path from the block with preorder number `sPre` to `y` whose
last edge is `x -> y`: `x` is that block, or `pre(x) > pre(y)` and `x` is reached from it
through nodes whose preorder numbers are all above `pre(y)`. -/
def onSdomPathDef (blocks : Blocks) (D : DFSTree) (sPre x y : Int) : Bool :=
  let pre (b : Int) : Int := D.toPre.getD (b - 1).toNat 0
  let s := D.fromPre.getD (sPre - 1).toNat 0
  x == s || (pre x > pre y &&
    (layers (fun u => (succsAt blocks u).toList.filter (pre · > pre y)) (-1) (blocks.size + 1)
      [s]).contains x)

end JuliaLean.Proofs.Compiler.src.ssair.domtree
