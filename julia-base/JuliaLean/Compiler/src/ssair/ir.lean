/-!
The control-flow-graph pieces of `Compiler/src/ssair/ir.jl` (and the `BasicBlock` struct of
`Compiler/src/ssair/basicblock.jl`) that the dominator tree reads and the passes use to edit
the CFG before updating it.

Conventions shared with `JuliaLean/Compiler/src/ssair/domtree.lean`:

* Julia vectors are `Array`s indexed from 1 through `aget`/`aset`, which throw
  `julia:BoundsError` exactly where Julia's checked indexing does.
* Julia exceptions are `julia:<Exception>` strings in `JM`, like the lattice model's `CM`.
  Running out of fuel is `outOfBudget`, which is a model failure, never a Julia outcome.
* Mutable vectors are values. Every function returns the updated value of what Julia mutates.
  Where Julia shares one vector between two places, the docstring says so.
-/

namespace JuliaLean.Compiler.ssair

/-- Julia outcomes: a value, or a thrown `julia:<Exception>` (or a model `outOfBudget`). -/
abbrev JM := Except String

def outOfBudget {α : Type} : JM α := throw "outOfBudget"

/-- Checked 1-based `a[i]`. -/
def aget {α : Type} (a : Array α) (i : Int) : JM α :=
  if h : 1 ≤ i ∧ (i - 1).toNat < a.size then pure (a[(i - 1).toNat]'h.2)
  else throw "julia:BoundsError"

/-- Checked 1-based `a[i] = v`. -/
def aset {α : Type} (a : Array α) (i : Int) (v : α) : JM (Array α) :=
  if 1 ≤ i ∧ (i - 1).toNat < a.size then pure (a.set! (i - 1).toNat v)
  else throw "julia:BoundsError"

/-- `resize!(a, n)`. Julia leaves grown slots of a bits array undefined; the model fills them
with `undef`. No result the difftest compares reads such a slot (see the domtree docstrings). -/
def resize {α : Type} (a : Array α) (n : Nat) (undef : α) : Array α :=
  if n ≤ a.size then a.extract 0 n else a ++ Array.replicate (n - a.size) undef

/-- The Julia range `a:b` as a list (empty when `b < a`). -/
def irange (a b : Int) : List Int :=
  (List.range (b - a + 1).toNat).map fun (i : Nat) => a + (i : Int)

/-- `struct BasicBlock`

Julia source: Compiler/src/ssair/basicblock.jl:18-22 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct BasicBlock
    stmts::StmtRange
    preds::Vector{Int}
    succs::Vector{Int}
end
```
`stmts` is not read by any modelled function and is left out. -/
structure BasicBlock where
  preds : Array Int
  succs : Array Int
  deriving Repr, BEq, Inhabited

/-- `CFG.blocks`. The `index` field is not read by the modelled functions. -/
abbrev Blocks := Array BasicBlock

/-- `findfirst(x::Int->x==v, xs)::Int`, with the `TypeError` of the failed typeassert. -/
def findfirstInt (xs : Array Int) (v : Int) : JM Nat :=
  match xs.findIdx? (· == v) with
  | some i => pure i
  | none => throw "julia:TypeError"

/-- `cfg_insert_edge!(cfg, from, to)`

Julia source: Compiler/src/ssair/ir.jl:14-19 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function cfg_insert_edge!(cfg::CFG, from::Int, to::Int)
    # Assumes that this edge does not already exist
    push!(cfg.blocks[to].preds, from)
    push!(cfg.blocks[from].succs, to)
    nothing
end
```
-/
def cfgInsertEdge (blocks : Blocks) (frm to : Int) : JM Blocks := do
  let bt ← aget blocks to
  let blocks ← aset blocks to { bt with preds := bt.preds.push frm }
  let bf ← aget blocks frm
  aset blocks frm { bf with succs := bf.succs.push to }

/-- `cfg_delete_edge!(cfg, from, to)`

Julia source: Compiler/src/ssair/ir.jl:21-28 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function cfg_delete_edge!(cfg::CFG, from::Int, to::Int)
    preds = cfg.blocks[to].preds
    succs = cfg.blocks[from].succs
    # Assumes that blocks appear at most once in preds and succs
    deleteat!(preds, findfirst(x::Int->x==from, preds)::Int)
    deleteat!(succs, findfirst(x::Int->x==to, succs)::Int)
    nothing
end
```
-/
def cfgDeleteEdge (blocks : Blocks) (frm to : Int) : JM Blocks := do
  let preds := (← aget blocks to).preds
  let succs := (← aget blocks frm).succs
  let i ← findfirstInt preds frm
  let blocks ← aset blocks to { (← aget blocks to) with preds := preds.eraseIdxIfInBounds i }
  let j ← findfirstInt succs to
  aset blocks frm { (← aget blocks frm) with succs := succs.eraseIdxIfInBounds j }

/-- `kill_edge!(bbs, from, to, callback)`, with the callback a state transformer that sees the
blocks at the time Julia calls it. `callback === nothing` is `fun _ _ _ s => pure s`.

Julia source: Compiler/src/ssair/ir.jl:1452-1465 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Used in inlining before we start compacting - Only works at the CFG level
function kill_edge!(bbs::Vector{BasicBlock}, from::Int, to::Int, callback=nothing)
    preds, succs = bbs[to].preds, bbs[from].succs
    deleteat!(preds, findfirst(x::Int->x==from, preds)::Int)
    deleteat!(succs, findfirst(x::Int->x==to, succs)::Int)
    if length(preds) == 0
        for succ in copy(bbs[to].succs)
            kill_edge!(bbs, to, succ, callback)
        end
    end
    if callback !== nothing
        callback(from, to)
    end
end
```
Each call deletes one edge, so `fuel` one more than the number of edges is enough. -/
def killEdge {σ : Type} (callback : Blocks → Int → Int → σ → JM σ) :
    Nat → Blocks → Int → Int → σ → JM (Blocks × σ)
  | 0, _, _, _, _ => outOfBudget
  | fuel + 1, bbs, frm, to, s => do
    let preds := (← aget bbs to).preds
    let succs := (← aget bbs frm).succs
    let i ← findfirstInt preds frm
    let preds := preds.eraseIdxIfInBounds i
    let bbs ← aset bbs to { (← aget bbs to) with preds }
    let j ← findfirstInt succs to
    let bbs ← aset bbs frm { (← aget bbs frm) with succs := succs.eraseIdxIfInBounds j }
    let (bbs, s) ← if preds.size == 0 then
        (← aget bbs to).succs.toList.foldlM
          (fun (acc : Blocks × σ) succ => killEdge callback fuel acc.1 to succ acc.2) (bbs, s)
      else pure (bbs, s)
    let s ← callback bbs frm to s
    pure (bbs, s)

/-- The number of edge endpoints in the CFG, a fuel bound for the loops over it. -/
def edgeCount (blocks : Blocks) : Nat :=
  blocks.foldl (fun n b => n + b.preds.size + b.succs.size) 0

end JuliaLean.Compiler.ssair
