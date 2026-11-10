import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.Checks
import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.Inputs

/-!
The statements of the properties of `Compiler/src/ssair/slot2ssa.jl`.
-/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

/-! ## Bounded properties -/

/-- The CFGs the bounded properties range over: the 564 CFGs of 1 to 3 blocks that the domtree
area's `smallCFGs` held when these properties were written (`smallCFGs12` and the eight `slice3`
slices), plus that area's lowering-shaped 3-block CFGs `lower3`. Its `branchCFGs` (4 to 9
blocks) are left out, because the exhaustive checks here grow too fast with the block count. -/
def cfgsUpTo3 : List (List (List Int) × List Int) :=
  smallCFGs12 ++ (subsetsOf (irange 1 3)).flatMap slice3 ++ lower3

/-- Every bounded property holds on all of `cfgsUpTo3` once it holds on `smallCFGs12`, on each
of the eight slices of 3-block CFGs and on `lower3`. -/
theorem cfgsUpTo3_of_slices (P : List (List Int) × List Int → Bool)
    (h12 : smallCFGs12.all P = true)
    (h0 : (slice3 []).all P = true) (h1 : (slice3 [3]).all P = true)
    (h2 : (slice3 [2]).all P = true) (h3 : (slice3 [2, 3]).all P = true)
    (h4 : (slice3 [1]).all P = true) (h5 : (slice3 [1, 3]).all P = true)
    (h6 : (slice3 [1, 2]).all P = true) (h7 : (slice3 [1, 2, 3]).all P = true)
    (hl : lower3.all P = true) :
    ∀ c ∈ cfgsUpTo3, P c = true := by
  have hs : subsetsOf (irange 1 3) = [[], [3], [2], [2, 3], [1], [1, 3], [1, 2], [1, 2, 3]] := by
    decide
  apply List.all_eq_true.mp
  simp only [cfgsUpTo3, hs, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.all_append, h12, h0, h1, h2, h3, h4, h5, h6, h7, hl, Bool.and_self]

/-- `iterated_dominance_frontier(cfg, BlockLiveness(defs, nothing), construct_domtree(cfg))` is
the iterated dominance frontier of `defs` by definition, with no block twice, for every set of
reachable def blocks given in any order, on every CFG of `cfgsUpTo3`. -/
def IdfSmall : Prop := ∀ c ∈ cfgsUpTo3, idfOK (mkBlocks c.1 c.2) = true

/-- On every CFG of `cfgsUpTo3` and every def/use pattern of one slot (each block: nothing, a
use, a def then a use, or `x = x + 1`; with or without the argument def `0`) whose defs are in
reachable blocks: `compute_live_ins` gives the def blocks and the live-in blocks by definition,
and `iterated_dominance_frontier` with that liveness gives exactly the pruned SSA phi positions
(iterated dominance frontier of the def blocks ∩ live-in blocks), with no block twice. -/
def PrunedPhisSmall : Prop := ∀ c ∈ cfgsUpTo3, prunedOK (mkBlocks c.1 c.2) = true

/-! ## The renaming keeps every inserted phi -/

mutual
/-- `.ssa t` is an operand of `v`, at any depth. -/
def irvMentions (t : Int) : IRV → Bool
  | .ssa n => n == t
  | .expr _ ⟨args⟩ => mentionsList t args
  | .gotoifnot c _ => irvMentions t c
  | .ret (some v) => irvMentions t v
  | .enter _ (some v) => irvMentions t v
  | .phi _ ⟨vals⟩ => mentionsOpts t vals
  | .phic ⟨vals⟩ => mentionsOpts t vals
  | .upsilon (some v) => irvMentions t v
  | .pinode v _ => irvMentions t v
  | _ => false
def mentionsList (t : Int) : List IRV → Bool
  | [] => false
  | v :: vs => irvMentions t v || mentionsList t vs
def mentionsOpts (t : Int) : List (Option IRV) → Bool
  | [] => false
  | some v :: vs => irvMentions t v || mentionsOpts t vs
  | none :: vs => mentionsOpts t vs
end

mutual
/-- `v` contains an `Expr(:isdefined, ...)`. -/
def irvHasIsdefined : IRV → Bool
  | .expr h ⟨args⟩ => h == "isdefined" || isdefinedList args
  | _ => false
def isdefinedList : List IRV → Bool
  | [] => false
  | v :: vs => irvHasIsdefined v || isdefinedList vs
end

/-- The inputs the statement is about: every block has an inference state (no block is
unreachable for inference), every slot that inference sees at a block entry is either
`Union{}` or surely defined there (so `construct_ssa!` makes no undef-tracking nodes), no
statement contains `@isdefined` (whose renaming reads only the undef part of a slot), and the IR
has no new nodes yet (as `convert_to_ircode!` leaves it). -/
def phiInputsOK (I : SSAInputs) (ir : SIR) : Bool :=
  I.bbStates.all (fun s => match s with
    | some vt => vt.all fun v => v.bottom || !v.undef
    | none => false) &&
  ir.stmts.all (fun s => !irvHasIsdefined s) && ir.newNodes.isEmpty

/-- New node `k` (0-based) of `out` is an operand of some statement or new node. After
`new_to_regular` and `domsort_ssa!`, new node `k` is `SSAValue(length(out.stmts) + k + 1)`. -/
def newNodeUsed (out : SIR) (k : Nat) : Bool :=
  let t : Int := out.stmts.size + k + 1
  out.stmts.any (irvMentions t ·) || out.newNodes.any fun n => irvMentions t n.stmt

/-- Every phi node in the new nodes of `out` that has an incoming edge is used. -/
def phisUsed (out : SIR) : Bool :=
  (List.range out.newNodes.size).all fun k =>
    match (out.newNodes[k]?.map (·.stmt) : Option IRV) with
    | some (.phi e _) => e.isEmpty || newNodeUsed out k
    | _ => true

/-- A successful result satisfies `p` (a thrown error satisfies the statement vacuously). -/
def okThen {α : Type} (r : JM α) (p : α → Bool) : Bool :=
  match r with
  | .ok x => p x
  | .error _ => true

/-- Pruned SSA has no dead phi nodes (the comment of `compute_live_ins` at
Compiler/src/ssair/slot2ssa.jl:495-497 says pruning "prevents insertion of dead phi nodes"): on
every input of `phiInputsOK`, every phi node `construct_ssa!` (as `slot2reg` calls it, with
`construct_domtree` and `scan_slot_def_use`) inserts and gives an incoming edge is an operand of
some statement or new node of its result. A phi is placed only in a block where the slot is
live-in, so some path from that block reaches a read of the slot before any store to it, and a
correct renaming makes that read (or a phi, π or upsilon on the way) refer to the phi. -/
def PhisUsed : Prop :=
  ∀ (I : SSAInputs) (ir : SIR), phiInputsOK I ir = true → okThen (slot2regSsa I ir) phisUsed = true

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
