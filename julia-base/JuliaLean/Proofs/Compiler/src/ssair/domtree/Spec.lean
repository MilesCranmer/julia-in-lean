import JuliaLean.Compiler.src.ssair.domtree

/-!
Reference definitions for the properties of `Compiler/src/ssair/domtree.jl`: reachability,
dominance and post-dominance by their definitions (every path passes through the block), and
the immediate (post-)dominator by its definition. These are written from the definitions, not
from the Julia code, and use none of the model's functions.

A CFG for the bounded checks is a list of successor lists over the blocks `1..n`. Predecessor
lists are derived from it the way `compute_basic_blocks` pushes them: in increasing order of the
source block, one entry per edge, with the virtual predecessor `0` first on block 1 when
asked for (as `compute_basic_blocks` gives the entry block and catch blocks).
-/

namespace JuliaLean.Proofs.Compiler.src.ssair.domtree

open JuliaLean.Compiler.ssair

/-- The blocks of the CFG whose successor lists are `succs`. The blocks in `zeroPreds` get the
virtual predecessor `0` first (`compute_basic_blocks` gives it to the entry block and to catch
blocks, Compiler/src/ssair/ir.jl:109 and 139). -/
def mkBlocks (succs : List (List Int)) (zeroPreds : List Int := [1]) : Blocks :=
  let n := succs.length
  ((List.range n).map fun (i : Nat) =>
    let b : Int := (i : Int) + 1
    let preds := (List.range n).flatMap fun (j : Nat) =>
      ((succs.getD j []).filter (· == b)).map fun _ => (j : Int) + 1
    (⟨((if zeroPreds.contains b then [0] else []) ++ preds).toArray,
      (succs.getD i []).toArray⟩ : BasicBlock)).toArray

/-- The real blocks `1..n`. -/
def blockIds (blocks : Blocks) : List Int := irange 1 blocks.size

/-- Edges of the search graph out of `x`. Forward: the successors of `x`. Reverse (for
post-dominance): out of the virtual exit `0`, the blocks with no successors; out of a real block,
its predecessors other than the virtual `0`. -/
def specEdges (blocks : Blocks) (isPost : Bool) (x : Int) : List Int :=
  if isPost then
    if x == 0 then (blockIds blocks).filter fun b =>
        match blocks[(b - 1).toNat]? with | some bb => bb.succs.isEmpty | none => false
    else match blocks[(x - 1).toNat]? with
      | some bb => bb.preds.toList.filter (· != 0) | none => []
  else match blocks[(x - 1).toNat]? with
    | some bb => bb.succs.toList | none => []

/-- One breadth-first layer: add every node one edge away from `s` that is not `avoid`. -/
def layer (edges : Int → List Int) (avoid : Int) (s : List Int) : List Int :=
  s.foldl (fun acc x => (edges x).foldl
    (fun acc y => if y == avoid || acc.contains y then acc else acc ++ [y]) acc) s

def layers (edges : Int → List Int) (avoid : Int) : Nat → List Int → List Int
  | 0, s => s
  | k + 1, s => layers edges avoid k (layer edges avoid s)

/-- The nodes reachable from the root without passing through `avoid` (`avoid = -1`: no node
avoided). The root is block 1 forward and the virtual exit `0` in reverse. `n + 1` layers reach
every node within distance `n + 1` of the root, which is every reachable node, since a shortest
path visits each of the `n + 1` nodes at most once. -/
def reachAvoid (blocks : Blocks) (isPost : Bool) (avoid : Int) : List Int :=
  let root : Int := if isPost then 0 else 1
  if root == avoid then [] else
    layers (specEdges blocks isPost) avoid (blocks.size + 1) [root]

/-- The candidate dominators: the real blocks, and the virtual exit `0` for post-dominance. -/
def candidates (blocks : Blocks) (isPost : Bool) : List Int :=
  (if isPost then [0] else []) ++ blockIds blocks

/-- The reachability facts of one CFG and direction: the nodes reachable from the root, and for
each candidate `a` the nodes reachable from the root while avoiding `a`. Computed once per CFG,
so that the checks below do not redo the searches for every pair of blocks. -/
structure DomInfo where
  isPost : Bool
  cands : List Int
  reach : List Int
  avoid : List (Int × List Int)

def domInfo (blocks : Blocks) (isPost : Bool) : DomInfo :=
  let cands := candidates blocks isPost
  ⟨isPost, cands, reachAvoid blocks isPost (-1),
    cands.map fun a => (a, reachAvoid blocks isPost a)⟩

/-- `b` is reachable from the root (block 1, or the virtual exit in reverse). -/
def DomInfo.reachable (I : DomInfo) (b : Int) : Bool := I.reach.contains b

/-- `a` (post-)dominates `b` by definition: `b` is reachable from the root, and every path from
the root to `b` passes through `a` (`b` is not reachable when `a` is removed). Node `0` is the
virtual exit in reverse. A non-candidate `a` (not a node) dominates only itself, which the
`getD` gives: it looks up the full reachable set. -/
def DomInfo.dom (I : DomInfo) (a b : Int) : Bool :=
  I.reach.contains b && (a == b ||
    !(((I.avoid.find? (·.1 == a)).map (·.2)).getD I.reach).contains b)

/-- `d` is the immediate (post-)dominator of `b` by definition: it is a node, strictly dominates
`b`, and every strict dominator of `b` dominates `d`. -/
def DomInfo.isIdom (I : DomInfo) (d b : Int) : Bool :=
  d != b && I.cands.contains d && I.dom d b &&
    I.cands.all fun c => c == b || !I.dom c b || I.dom c d

/-- The expected `idoms_bb[b]`: `0` for the entry block and for blocks not reachable from the
root; otherwise the immediate dominator, which is `0` in the post-dominator tree exactly when it
is the virtual exit. -/
def DomInfo.idomOK (I : DomInfo) (b d : Int) : Bool :=
  if (!I.isPost && b == 1) || !I.reachable b then d == 0 else I.isIdom d b

/-- `d` is the nearest common (post-)dominator of `a` and `b` by definition: it dominates both,
and every node that dominates both dominates `d`. -/
def DomInfo.isNCD (I : DomInfo) (a b d : Int) : Bool :=
  I.dom d a && I.dom d b &&
    I.cands.all fun c => !(I.dom c a && I.dom c b) || I.dom c d

/-- Insertion sort, to compare the blocks `dominated` yields as a set. -/
def isortInt : List Int → List Int
  | [] => []
  | x :: xs => let r := isortInt xs; r.filter (· < x) ++ [x] ++ r.filter (x ≤ ·)

end JuliaLean.Proofs.Compiler.src.ssair.domtree
