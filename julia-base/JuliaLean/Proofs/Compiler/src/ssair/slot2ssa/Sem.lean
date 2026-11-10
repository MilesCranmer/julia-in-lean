import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.Ssa

/-!
What the IR does, for the end-to-end check of `construct_ssa!` and of `domsort_ssa!`.

`runIR` runs an IR on symbolic values: a call `f(a, b)` gives the term `f(a, b)` and is logged,
so two IRs that make the same calls on the same arguments in the same order log the same list.
The branch condition `Main.c` of the generated code reads the next Boolean of an oracle list, so
running every oracle runs every path. A run ends in a `return` (with its value), an
`UndefVarError` (a read of an unassigned local, or a `throw_undef_if_not` on `false`), the oracle
running out (`cut`), or `stuck`: any statement or value the semantics does not cover, an
`SSAValue` read before its definition ran, a phi node that is not at the start of its block or
that has no edge for the block control came from, and falling off the last block. A run that
uses up its block budget has no end.

The checks compare the lowered code `ssaCase` builds (slots, statement-number labels) with the
IR `construct_ssa!` hands to `domsort_ssa!` and with the result of `domsort_ssa!` (SSA values,
block-number labels, the new nodes placed as `ssaPropsOK` places them).
-/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

/-- Symbolic values: a literal or global name, an argument, or an application. -/
inductive Tm where
  | s (x : String)
  | a (n : Int)
  | app (f : Tm) (x : Tm)
  deriving BEq, Inhabited

/-- Why a run stopped early. -/
inductive Stop where
  | err (name : String)
  | cut
  | stuck
  deriving BEq, Inhabited

structure RunSt where
  ssa : List (Int × Tm)
  slots : List (Int × Tm)
  orc : List Bool
  ev : List Tm

abbrev SM := StateT RunSt (Except (Stop × List Tm))

def stop {α : Type} (k : Stop) : SM α := do
  let s ← get
  throw (k, s.ev)

def boolTm (b : Bool) : Tm := .s (if b then "Bool:true" else "Bool:false")

/-- The value of an operand. -/
def evalAtom (names : Array String) (v : IRV) : SM Tm := do
  match v with
  | .lit x => pure (.s x)
  | .sym x => pure (.s x)
  | .glob g =>
    if g == "Main.c" then
      let s ← get
      match s.orc with
      | [] => stop .cut
      | b :: bs => do set { s with orc := bs }; pure (boolTm b)
    else pure (.s g)
  | .arg n => pure (.a n)
  | .ssa n =>
    match (← get).ssa.lookup n with
    | some t => pure t
    | none => stop .stuck
  | .slot n =>
    match (← get).slots.lookup n with
    | some t => pure t
    | none => stop (.err (names.getD (n - 1).toNat ""))
  | _ => stop .stuck

/-- The value of an operand or of a call on operands. `Core.typeassert(v, Core.Bool)` (what
`construct_ssa!` makes of a `goto ... if not` to the next block) gives `v` and is not logged;
any other call is logged. -/
def evalRhs (names : Array String) (v : IRV) : SM Tm := do
  match v with
  | .expr "call" args =>
    let vs ← args.toList.mapM (evalAtom names)
    match vs with
    | [] => stop .stuck
    | f :: xs =>
      if f == .s "Core.typeassert" then
        match xs with
        | [x, .s "Core.Bool"] => pure x
        | _ => stop .stuck
      else
        let t := xs.foldl Tm.app f
        modify fun s => { s with ev := s.ev ++ [t] }
        pure t
  | v => evalAtom names v

def setSsa (id : Int) (t : Tm) : SM Unit :=
  modify fun s => { s with ssa := (id, t) :: s.ssa }

/-- Where control goes after a statement. -/
inductive Ctrl where
  | next
  | jump (b : Int)
  | ret (v : Tm)

/-- Run one statement other than a phi node. `labelBlock` turns a `goto` label into a block. -/
def execStmt (names : Array String) (labelBlock : Int → Int) (id : Int) (stmt : IRV) :
    SM Ctrl := do
  match stmt with
  | .nothing => pure .next
  | .expr "=" #[.slot x, rhs] => do
    let t ← evalRhs names rhs
    modify fun s => { s with slots := (x, t) :: s.slots }
    pure .next
  | .expr "throw_undef_if_not" #[.sym n, c] => do
    let t ← evalAtom names c
    if t == boolTm true then pure .next
    else if t == boolTm false then stop (.err n)
    else stop .stuck
  | .expr "call" _ => do setSsa id (← evalRhs names stmt); pure .next
  | .pinode v _ => do setSsa id (← evalAtom names v); pure .next
  | .lit _ | .ssa _ | .arg _ | .glob _ | .slot _ => do setSsa id (← evalAtom names stmt); pure .next
  | .goto l => pure (.jump (labelBlock l))
  | .gotoifnot c d => do
    let t ← evalAtom names c
    if t == boolTm true then pure .next
    else if t == boolTm false then pure (.jump (labelBlock d))
    else stop .stuck
  | .ret (some v) => pure (.ret (← evalAtom names v))
  | _ => stop .stuck

/-- The statements of each block in execution order, with their `SSAValue` ids: for each
statement, the new nodes placed before it (in insertion order), the statement, then the new
nodes attached after it. New node `k` (0-based) is `SSAValue(length(stmts) + k + 1)`. -/
def blockInsts (ir : SIR) : Array (List (Int × IRV)) :=
  let n := ir.stmts.size
  let nodesAt (p : Int) (after : Bool) : List (Int × IRV) :=
    (List.range ir.newNodes.size).filterMap fun k =>
      let nn := ir.newNodes.getD k default
      if nn.pos == p && nn.attachAfter == after then some (((n + k + 1 : Nat) : Int), nn.stmt)
      else none
  ir.cfg.blocks.map fun b => (irange b.first b.last).flatMap fun p =>
    nodesAt p false ++ [(p, ir.stmts.getD (p - 1).toNat .nothing)] ++ nodesAt p true

/-- The leading phi nodes of a block, and the statements after them. -/
def splitPhis : List (Int × IRV) → List (Int × Array Int × Array (Option IRV)) × List (Int × IRV)
  | (id, .phi e v) :: rest => let (ps, r) := splitPhis rest; ((id, e, v) :: ps, r)
  | l => ([], l)

/-- The values of the leading phi nodes for an entry from block `pred`, all read before any is
set. An edge whose value is unassigned gives `#undef`. -/
def evalPhis (names : Array String) (pred : Int) :
    List (Int × Array Int × Array (Option IRV)) → SM (List (Int × Tm))
  | [] => pure []
  | (id, e, v) :: rest => do
    let t ← match e.toList.idxOf? pred with
      | none => stop .stuck
      | some j => match v.getD j none with
        | some x => evalAtom names x
        | none => pure (.s "#undef")
    pure ((id, t) :: (← evalPhis names pred rest))

def execList (names : Array String) (labelBlock : Int → Int) :
    List (Int × IRV) → SM Ctrl
  | [] => pure .next
  | (id, st) :: rest => do
    match ← execStmt names labelBlock id st with
    | .next => execList names labelBlock rest
    | c => pure c

/-- Run from block `b`, entered from `pred`, for at most `fuel` block entries. `none` when the
budget runs out. -/
def runBlocks (names : Array String) (labelBlock : Int → Int) (prog : Array (List (Int × IRV))) :
    Nat → Int → Int → SM (Option Tm)
  | 0, _, _ => pure none
  | fuel + 1, b, pred => do
    let some insts := prog[(b - 1).toNat]? | stop .stuck
    if b < 1 then stop .stuck
    let (phis, rest) := splitPhis insts
    let vals ← evalPhis names pred phis
    modify fun s => { s with ssa := vals ++ s.ssa }
    match ← execList names labelBlock rest with
    | .ret v => pure (some v)
    | .jump t => runBlocks names labelBlock prog fuel t b
    | .next => runBlocks names labelBlock prog fuel (b + 1) b

/-- A run's log and its end: `some` of `ret(v)`, `err(name)`, `cut` or `stuck`, or `none` when
the block budget ran out. -/
abbrev Outcome := List Tm × Option Tm

def stuckTm : Tm := .s "!stuck"

/-- Run `ir` on the oracle `orc`. `stmtLabels` says that `goto` labels are statement numbers (the
lowered code) rather than block numbers. Slots `1:nargs` start as the arguments. -/
def runIR (names : Array String) (nargs : Int) (stmtLabels : Bool) (fuel : Nat) (ir : SIR)
    (orc : List Bool) : Outcome :=
  let labelBlock (l : Int) : Int :=
    if stmtLabels then (match blockForInst ir.cfg l with | .ok b => b | .error _ => -1) else l
  let init : RunSt := ⟨[], (irange 1 nargs).map (fun i => (i, Tm.a i)), orc, []⟩
  match (runBlocks names labelBlock (blockInsts ir) fuel 1 0).run init with
  | .ok (some v, s) => (s.ev, some (.app (.s "!ret") v))
  | .ok (none, s) => (s.ev, none)
  | .error (.err n, ev) => (ev, some (.app (.s "!err") (.s n)))
  | .error (.cut, ev) => (ev, some (.s "!cut"))
  | .error (.stuck, ev) => (ev, some stuckTm)

/-- Two runs agree: neither is stuck, and either both ended the same way with the same log, or
one ran out of budget and its log is a prefix of the other's. -/
def sameOutcome (a b : Outcome) : Bool :=
  match a.2, b.2 with
  | some x, some y => x != stuckTm && x == y && a.1 == b.1
  | none, some y => y != stuckTm && a.1.isPrefixOf b.1
  | some x, none => x != stuckTm && b.1.isPrefixOf a.1
  | none, none => a.1.isPrefixOf b.1 || b.1.isPrefixOf a.1

/-- Every oracle of three branch outcomes. -/
def oracles : List (List Bool) :=
  [false, true].flatMap fun a => [false, true].flatMap fun b => [false, true].map fun c => [a, b, c]

/-- The block budget of a run: enough for every path of three branches through three blocks
and the fixup blocks of `domsort_ssa!`. -/
def semFuel : Nat := 16

/-- `slot2reg`'s calls as in `slot2regSsa`, returning the IR `construct_ssa!` hands to
`domsort_ssa!` and the result of `domsort_ssa!`. -/
def slot2regParts (I : SSAInputs) (ir : SIR) : JM (SIR × SIR) := do
  let dt ← constructDomtree ir.cfg.domBlocks
  let defuses ← scanSlotDefUse I.nargs I.slotnames.size ir.stmts
  let pre ← constructSsaBody! I ir dt defuses
  let post ← domsortSsa! pre dt
  pure (pre, post)

theorem slot2regParts_snd (I : SSAInputs) (ir : SIR) :
    slot2regSsa I ir = Prod.snd <$> slot2regParts I ir := by
  simp [slot2regSsa, slot2regParts, constructSsa!, map_bind, bind_pure_comp, Functor.map_map]

/-- On one input, `construct_ssa!` returns, `domsort_ssa!` keeps the new nodes, and on every
oracle the IR `construct_ssa!` hands to `domsort_ssa!` and the result of `domsort_ssa!` agree. -/
def domsortSemOK (I : SSAInputs) (ir : SIR) : Bool :=
  jmIs (slot2regParts I ir) fun (pre, post) =>
    post.newNodes.size == pre.newNodes.size &&
    oracles.all fun o =>
      sameOutcome (runIR I.slotnames I.nargs false semFuel pre o)
        (runIR I.slotnames I.nargs false semFuel post o)

/-- On one input, `construct_ssa!` returns and on every oracle the lowered code and the IR
`construct_ssa!` hands to `domsort_ssa!` agree. -/
def constructSemOK (I : SSAInputs) (ir : SIR) : Bool :=
  jmIs (slot2regParts I ir) fun (pre, _) =>
    oracles.all fun o =>
      sameOutcome (runIR I.slotnames I.nargs true semFuel ir o)
        (runIR I.slotnames I.nargs false semFuel pre o)

/-- Lowering never jumps back to the first statement while an argument is assigned: an
argument that the body assigns is first copied into a new slot by statement 1 (as `x@_3 =
x@_2`), so the loop header is not block 1. In the generated inputs: `x` is a local, or no block
jumps to block 1. -/
def argEntryOK (succs : List (List Int)) (isArg : Bool) : Bool :=
  !isArg || !(succs.any (·.contains 1))

/-- The two checks on every input of `ssaOK` for one CFG: `domsortSemOK` on all of them,
`constructSemOK` on those of `argEntryOK`. -/
def semOK (succs : List (List Int)) : Bool :=
  (allPats succs.length).all fun pats => [false, true].all fun isArg =>
    !readsAssigned succs pats isArg ||
    let (I, ir) := ssaCase succs pats isArg
    domsortSemOK I ir && (!argEntryOK succs isArg || constructSemOK I ir)

/-- `semOK` on a 3-block CFG for the patterns whose block 1 has pattern `p0`. -/
def semOKPart (succs : List (List Int)) (p0 : Nat) : Bool :=
  ((allPats 2).map (p0 :: ·)).all fun pats => [false, true].all fun isArg =>
    !readsAssigned succs pats isArg ||
    let (I, ir) := ssaCase succs pats isArg
    domsortSemOK I ir && (!argEntryOK succs isArg || constructSemOK I ir)

theorem semOK_of_parts (succs : List (List Int)) (h : succs.length = 3)
    (h0 : semOKPart succs 0 = true) (h1 : semOKPart succs 1 = true)
    (h2 : semOKPart succs 2 = true) (h3 : semOKPart succs 3 = true) : semOK succs = true := by
  unfold semOK
  rw [h, show allPats 3 = [0, 1, 2, 3].flatMap (fun p => (allPats 2).map (p :: ·)) from rfl]
  unfold semOKPart at h0 h1 h2 h3
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.all_append, h0, h1, h2,
    h3, Bool.and_self]

/-- `domsort_ssa!` keeps what the code does, and so does `construct_ssa!` on lowered code: for
one local or argument `x` and every input of `SsaSmall` (every lowered-code CFG with 1 to 3
blocks, every def/use pattern of `x` whose reads have an assignment before them on some path), on
every oracle of three branch outcomes,

* the IR `construct_ssa!` hands to `domsort_ssa!` and the result of `domsort_ssa!` make the same
  calls with the same arguments in the same order and end the same way (the same return value,
  or the same `UndefVarError`), neither gets stuck, and `domsort_ssa!` keeps every new node;
* when `x` is a local or no block jumps back to block 1 (`argEntryOK`, which lowering keeps), the
  same holds for the lowered code and the IR `construct_ssa!` hands to `domsort_ssa!`. -/
def SemSmall : Prop := ∀ n, 1 ≤ n → n ≤ 3 → ∀ succs ∈ juliaCFGs n, semOK succs = true

/-- `construct_ssa!` keeps what the code does on every input of `SsaSmall`, without
`argEntryOK`. -/
def ConstructSemAll : Prop :=
  ∀ n, 1 ≤ n → n ≤ 3 → ∀ succs ∈ juliaCFGs n, ∀ pats ∈ allPats n, ∀ isArg : Bool,
    readsAssigned succs pats isArg = true →
    constructSemOK (ssaCase succs pats isArg).1 (ssaCase succs pats isArg).2 = true

/-- The counterexample of `ConstructSemAll`: block 1 runs `x = x + 1` and then jumps back to
itself through block 2 while `Main.c` holds; block 3 calls `f(x)`. `x` is the argument. -/
def argLoopSuccs : List (List Int) := [[3, 2], [1], []]
def argLoopPats : List Nat := [3, 0, 1]

theorem argLoop_in : argLoopSuccs ∈ juliaCFGs 3 := by decide +kernel
theorem argLoopPats_in : argLoopPats ∈ allPats 3 := by decide +kernel
theorem argLoop_reads : readsAssigned argLoopSuccs argLoopPats true = true := by decide +kernel

/-- On the counterexample, the IR `construct_ssa!` hands to `domsort_ssa!` reads `x + 1` with
`x` the argument on every iteration: block 1 gets no phi node for `x`. On the oracle
`[true, false, false]` the lowered code calls `Main.+` twice and then `f(arg + 1 + 1)`; the IR
calls `f(arg + 1)`. -/
theorem argLoop_wrong :
    constructSemOK (ssaCase argLoopSuccs argLoopPats true).1
      (ssaCase argLoopSuccs argLoopPats true).2 = false := by decide +kernel

theorem constructSemAll_refuted : ¬ ConstructSemAll := fun h => by
  have := h 3 (by decide) (by decide) argLoopSuccs argLoop_in argLoopPats argLoopPats_in true
    argLoop_reads
  rw [argLoop_wrong] at this
  exact Bool.false_ne_true this

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
