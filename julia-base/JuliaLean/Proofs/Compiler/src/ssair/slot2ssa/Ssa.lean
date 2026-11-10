import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.Props

/-!
The end-to-end check of `construct_ssa!` on small lowered-code shapes: the IR that
`convert_to_ircode!` gives for a function with one local (or argument) `x` whose reads and
assignments follow a def/use pattern, over every small CFG that `compute_basic_blocks` can make
from gotos, conditional gotos, fall-throughs and returns. The inference results are computed
here from the definitions (defined on every path, on some path). The checks on the result are
the SSA properties: every use is dominated by its definition, every phi node has one value per
predecessor edge, and the blocks are in dominator order with every statement use after its
definition (the docstring of `domsort_ssa!`, Compiler/src/ssair/slot2ssa.jl:328-334).
-/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

/-! ## The inputs -/

/-- The successor lists block `b` of `n` can have in lowered code: none (a `return`), the
fall-through `b + 1` (no terminator), any block by a `goto`, or a `goto ... if not` to any
block `t` with the fall-through, as `[t, b + 1]` (`compute_basic_blocks` pushes the jump target
first, Compiler/src/ssair/ir.jl:116-146). -/
def juliaSuccChoices (n : Nat) (b : Int) : List (List Int) :=
  let blocks := irange 1 n
  [[]] ++ (if b < n then [[b + 1]] else []) ++ (blocks.filter (· != b + 1)).map (fun t => [t]) ++
    (if b < n then (blocks.filter (· != b + 1)).map (fun t => [t, b + 1]) else [])

/-- Every lowered-code CFG with `n` blocks. -/
def juliaCFGs (n : Nat) : List (List (List Int)) :=
  (irange 1 n).foldr (fun b acc => (juliaSuccChoices n b).flatMap fun s => acc.map (s :: ·)) [[]]

/-- The terminator of block `b` (statement `3b`) for its successor list. -/
def termFor (b : Int) : List Int → IRV
  | [] => .ret (some (.lit "Int64:0"))
  | [t] => if t == b + 1 then .lit "Int64:0" else .goto (3 * t - 2)
  | [t, _] => .gotoifnot (.glob "Main.c") (3 * t - 2)
  | _ => .nothing

/-- The two pattern statements of one block, slot 2 being `x`: nothing; a read `f(x)`; an
assignment `x = 1` then a read; `x = x + 1` (a read and an assignment in one statement). -/
def patStmts : Nat → List IRV
  | 1 => [.expr "call" #[.glob "Main.f", .slot 2], .nothing]
  | 2 => [.expr "=" #[.slot 2, .lit "Int64:1"], .expr "call" #[.glob "Main.f", .slot 2]]
  | 3 => [.expr "=" #[.slot 2, .expr "call" #[.glob "Main.+", .slot 2, .lit "Int64:1"]], .nothing]
  | _ => [.nothing, .nothing]

/-- Inference's view of `x` at block entry, from the definitions: `allIn` (assigned on every
path from the entry), `someIn` (on some path); `isArg` makes it always assigned. Least and
greatest fixed points by iteration over `n + 1` rounds. -/
def defIn (blocks : Blocks) (pats : List Nat) (isArg : Bool) : List Int × List Int :=
  let ids := blockIds blocks
  let hasD (b : Int) : Bool := let p := pats.getD (b - 1).toNat 0; p == 2 || p == 3
  let preds (b : Int) := (predsOf blocks b).filter (· != 0)
  let entryIn (b : Int) : Bool := b == 1 && isArg
  let allIn := (List.range (blocks.size + 1)).foldl (fun s _ =>
      ids.filter fun b => entryIn b || (b != 1 && (preds b).all fun p => hasD p || s.contains p))
    ids
  let someIn := (List.range (blocks.size + 1)).foldl (fun s _ =>
      ids.filter fun b => entryIn b || (preds b).any fun p => hasD p || s.contains p) []
  (allIn, someIn)

/-- The `construct_ssa!` inputs for one CFG and pattern: three statements per block (two from
the pattern, then the terminator); the blocks that are not reachable have no inference state,
and their pattern statements are `nothing`, as inference leaves dead code. Slot 1 is `#self#`. -/
def ssaCase (succs : List (List Int)) (pats : List Nat) (isArg : Bool) : SSAInputs × SIR :=
  let blocks := mkBlocks succs
  let I := domInfo blocks false
  let n := succs.length
  let (allIn, someIn) := defIn blocks pats isArg
  let stmts : List IRV := (List.range n).flatMap fun (i : Nat) =>
    let b : Int := (i : Int) + 1
    (if I.reachable b then patStmts (pats.getD i 0) else [.nothing, .nothing]) ++
      [termFor b (succs.getD i [])]
  let self : VarIn := ⟨false, false, "Core.Const(Main.g)", false⟩
  let bbs : List (Option (Array VarIn)) := (List.range n).map fun (i : Nat) =>
    let b : Int := (i : Int) + 1
    if I.reachable b then
      some #[self, ⟨!someIn.contains b, !allIn.contains b,
        if someIn.contains b then "Int64" else "Union{}", false⟩]
    else none
  let cfg : SCFG := ⟨((List.range n).map fun (i : Nat) =>
      let bb := blocks.getD i default
      (⟨3 * (i : Int) + 1, 3 * (i : Int) + 3, bb.preds, bb.succs⟩ : SBlock)).toArray,
    ((List.range (n - 1)).map fun (i : Nat) => 3 * (i : Int) + 4).toArray⟩
  (⟨if isArg then 2 else 1, #["#self#", "x"], bbs.toArray,
     Array.replicate (3 * n) 0, #[]⟩,
   ⟨stmts.toArray, Array.replicate (3 * n) false, cfg, #[]⟩)

/-- The cases where inference would not stop at a read of `x` that is never assigned before it
(a `throw_undef_if_not` with a constant `false`, after which inference sees no more code): every
read in a reachable block has an assignment on some path before it. -/
def readsAssigned (succs : List (List Int)) (pats : List Nat) (isArg : Bool) : Bool :=
  let blocks := mkBlocks succs
  let I := domInfo blocks false
  let (_, someIn) := defIn blocks pats isArg
  (blockIds blocks).all fun b =>
    !I.reachable b || someIn.contains b || let p := pats.getD (b - 1).toNat 0; p == 0 || p == 2

/-! ## The checks on the result -/

mutual
/-- The `SSAValue` operands of a statement other than a phi node, at any depth. -/
def ssaOps : IRV → List Int
  | .ssa n => [n]
  | .expr _ ⟨args⟩ => ssaOpsList args
  | .gotoifnot c _ => ssaOps c
  | .ret (some v) => ssaOps v
  | .enter _ (some v) => ssaOps v
  | .phic ⟨vals⟩ => ssaOpsOpts vals
  | .upsilon (some v) => ssaOps v
  | .pinode v _ => ssaOps v
  | _ => []
def ssaOpsList : List IRV → List Int
  | [] => []
  | v :: vs => ssaOps v ++ ssaOpsList vs
def ssaOpsOpts : List (Option IRV) → List Int
  | [] => []
  | some v :: vs => ssaOps v ++ ssaOpsOpts vs
  | none :: vs => ssaOpsOpts vs
end

/-- Where an `SSAValue` is defined or a statement sits: its block and its place in the block's
order. A new node at `pos` comes before statement `pos` (after it with `attach_after`), and new
nodes at the same place come in insertion order. -/
structure Place where
  block : Int
  pos : Int
  slot : Nat
  idx : Nat

def Place.before (a b : Place) : Bool :=
  a.pos < b.pos || (a.pos == b.pos && (a.slot < b.slot || (a.slot == b.slot && a.idx < b.idx)))

def blockOf (out : SIR) (pos : Int) : Int :=
  match blockForInst out.cfg pos with
  | .ok b => b
  | .error _ => -1

def stmtPlace (out : SIR) (i : Int) : Place := ⟨blockOf out i, i, 1, 0⟩

def nodePlace (out : SIR) (k : Nat) : Place :=
  let nn := out.newNodes.getD k default
  ⟨blockOf out nn.pos, nn.pos, if nn.attachAfter then 2 else 0, k⟩

/-- The place where `SSAValue(v)` is defined, if `v` names a statement or a new node. -/
def defPlace (out : SIR) (v : Int) : Option Place :=
  if 1 ≤ v ∧ v ≤ out.stmts.size then some (stmtPlace out v)
  else if out.stmts.size < v ∧ v ≤ out.stmts.size + out.newNodes.size then
    some (nodePlace out (v - out.stmts.size - 1).toNat)
  else none

/-- A use at `u` of a value defined at `d` is dominated by the definition. -/
def domUse (D : DomInfo) (d u : Place) : Bool :=
  (d.block == u.block && d.before u) || (d.block != u.block && D.dom d.block u.block)

/-- The SSA properties of a result: on the CFG of the result,

* every phi node has exactly one edge per predecessor of its block (the same multiset, with the
  virtual `0` of the entry block) and one value slot per edge, and each value defined at a
  statement or new node dominates the end of its predecessor block;
* every other use of an `SSAValue` in a reachable block names a statement or a new node whose
  place dominates the use;
* the blocks are in dominator order: the immediate dominator of each reachable block other than
  1 has a smaller number, and every use of a statement `SSAValue` by a statement comes after it.
-/
def ssaPropsOK (out : SIR) : Bool :=
  let blocks := out.cfg.domBlocks
  let D := domInfo blocks false
  let n := out.stmts.size
  let reachableAt (p : Place) := D.reachable p.block
  let useOK (u : Place) (v : Int) : Bool :=
    match defPlace out v with
    | some d => domUse D d u
    | none => false
  let stmtsOK := (irange 1 n).all fun i =>
    let u := stmtPlace out i
    !reachableAt u || (ssaOps (out.stmts.getD (i - 1).toNat .nothing)).all fun v =>
      useOK u v && (v > n || v < i)
  let nodesOK := (List.range out.newNodes.size).all fun k =>
    let u := nodePlace out k
    !reachableAt u ||
    match (out.newNodes.getD k default).stmt with
    | .phi edges vals =>
      let preds := (blocks.getD (u.block - 1).toNat default).preds.toList
      isortInt edges.toList == isortInt preds && vals.size == edges.size &&
      (List.range edges.size).all fun j =>
        match vals.getD j none with
        | some v => (ssaOps v).all fun w =>
            match defPlace out w with
            | some d => D.dom d.block (edges.getD j 0)
            | none => false
        | none => true
    | s => (ssaOps s).all (useOK u)
  let orderOK := (blockIds blocks).all fun b =>
    b == 1 || !D.reachable b ||
      (blockIds blocks).all fun d => !D.isIdom d b || d < b
  stmtsOK && nodesOK && orderOK

/-- For every pattern of `x` (with and without `x` an argument) whose reads all have an
assignment before them on some path, `construct_ssa!` returns and its result has the SSA
properties of `ssaPropsOK`. -/
def ssaOK (succs : List (List Int)) : Bool :=
  (allPats succs.length).all fun pats => [false, true].all fun isArg =>
    !readsAssigned succs pats isArg ||
    let (I, ir) := ssaCase succs pats isArg
    jmIs (slot2regSsa I ir) ssaPropsOK

/-- `construct_ssa!` (as `slot2reg` calls it) returns and gives IR with the SSA properties of
`ssaPropsOK` for every def/use pattern of one slot (every block: nothing, a read, an assignment
then a read, or `x = x + 1`; `x` a local or an argument; every read has an assignment before it
on some path) over every lowered-code CFG with 1 to 3 blocks (gotos, conditional gotos,
fall-throughs, returns, self loops, irreducible loops and unreachable blocks). -/
def SsaSmall : Prop := ∀ n, 1 ≤ n → n ≤ 3 → ∀ succs ∈ juliaCFGs n, ssaOK succs = true

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
