import JuliaLean.Compiler.src.ssair.slot2ssa
import JuliaLean.Proofs.Compiler.src.ssair.domtree.Checks

/-!
Reference definitions for the properties of `Compiler/src/ssair/slot2ssa.jl`, written from the
textbook definitions and not from the Julia code:

* the dominance frontier and the iterated dominance frontier of a set of blocks, from dominance
  by definition (`DomInfo.dom` of the domtree area: every path from the entry passes through
  the block);
* liveness of a slot at block entry, from its def/use statements: a block is live-in when some
  path from its entry reaches a use before any def (the standard backward equations, solved by
  iteration);
* the small CFGs with statement ranges the bounded checks range over, and the def/use patterns
  placed in them.
-/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

/-- The blocks of a small CFG as an `SCFG` with two statements per block: block `i` holds the
statements `2i - 1` and `2i`, and `cfg.index` holds the first statement of blocks `2..n`
(`compute_basic_blocks` stores it so; `block_for_inst` searches it). -/
def mkSCFG (blocks : Blocks) : SCFG :=
  let n := blocks.size
  ⟨((List.range n).map fun (i : Nat) =>
      let b := blocks.getD i default
      (⟨2 * (i : Int) + 1, 2 * (i : Int) + 2, b.preds, b.succs⟩ : SBlock)).toArray,
   ((List.range (n - 1)).map fun (i : Nat) => 2 * (i : Int) + 3).toArray⟩

def predsOf (blocks : Blocks) (y : Int) : List Int :=
  (blocks.getD (y - 1).toNat default).preds.toList

def succsOf (blocks : Blocks) (y : Int) : List Int :=
  (blocks.getD (y - 1).toNat default).succs.toList

/-- `y` is in the dominance frontier of `x`: `x` dominates a predecessor of `y` (other than the
virtual `0`) and does not strictly dominate `y`. -/
def inDF (I : DomInfo) (blocks : Blocks) (x y : Int) : Bool :=
  (predsOf blocks y).any (fun p => p != 0 && I.dom x p) && !(x != y && I.dom x y)

/-- The dominance frontier of a set of blocks, in increasing order. -/
def dfSet (I : DomInfo) (blocks : Blocks) (s : List Int) : List Int :=
  (blockIds blocks).filter fun y => s.any fun x => inDF I blocks x y

/-- The iterated dominance frontier `DF⁺(s)`: the least `t` with `t = DF(s ∪ t)`, in increasing
order. The iteration is monotone and adds at least one block per step until it stops, so
`n + 1` steps reach the fixed point. -/
def idfDef (I : DomInfo) (blocks : Blocks) (s : List Int) : List Int :=
  (List.range (blocks.size + 1)).foldl (fun t _ => dfSet I blocks (s ++ t)) []

/-- The same set, with no repeated element. -/
def sameSet (a b : List Int) : Bool := a.all b.contains && b.all a.contains

def nodupInt : List Int → Bool
  | [] => true
  | x :: xs => !xs.contains x && nodupInt xs

/-- A def/use pattern of one slot in one block of `mkSCFG`, statements `2i - 1` and `2i`:
0 nothing, 1 a use at `2i - 1`, 2 a def at `2i - 1` then a use at `2i` (the use is killed),
3 a use and a def at `2i - 1` (`x = x + 1`). -/
def patDefs (b : Int) : Nat → List Int
  | 2 => [2 * b - 1]
  | 3 => [2 * b - 1]
  | _ => []

def patUses (b : Int) : Nat → List Int
  | 1 => [2 * b - 1]
  | 2 => [2 * b]
  | 3 => [2 * b - 1]
  | _ => []

/-- The `defs` and `uses` statement lists of a slot with pattern `pats[i]` in block `i + 1`, in
statement order as `scan_slot_def_use` builds them, with the argument def `0` first when
`isArg`. -/
def patLists (pats : List Nat) (isArg : Bool) : List Int × List Int :=
  let bs := (List.range pats.length).map fun (i : Nat) => ((i : Int) + 1, pats.getD i 0)
  ((if isArg then [0] else []) ++ bs.flatMap (fun (b, p) => patDefs b p),
   bs.flatMap fun (b, p) => patUses b p)

/-- The block of statement `s` in `mkSCFG` (`0`, the argument def, is in block 1). -/
def blockOfStmt (s : Int) : Int := if s ≤ 0 then 1 else (s + 1) / 2

/-- Upward-exposed use in block `b`: some use comes before every def of the block (a use and a
def at the same statement count as the use first, since the right-hand side is evaluated
first). -/
def ueUse (defs uses : List Int) (b : Int) : Bool :=
  uses.any fun u => blockOfStmt u == b && defs.all fun d => blockOfStmt d != b || u ≤ d

def hasDef (defs : List Int) (b : Int) : Bool := defs.any fun d => blockOfStmt d == b

/-- Liveness at block entry by the backward equations
`livein(b) = ue(b) ∨ (¬def(b) ∧ ∃ s ∈ succs(b), livein(s))`, least solution, increasing. -/
def liveDef (blocks : Blocks) (defs uses : List Int) : List Int :=
  let ids := blockIds blocks
  (List.range (blocks.size + 1)).foldl (fun live _ =>
    ids.filter fun b => ueUse defs uses b ||
      (!hasDef defs b && (succsOf blocks b).any live.contains)) []

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
