import JuliaLean.Compiler.src.ssair.domtree

/-!
Source-mirrored model of `Compiler/src/ssair/slot2ssa.jl` at
f755f49a9e41380d7da126b3c1db9fe7f83dd027: the slot def/use scan, `compute_live_ins`,
`iterated_dominance_frontier` (with the binary heap of `Compiler/src/ssair/heap.jl`),
`construct_ssa!` (phi and `PhiC` placement, the renaming walk, upsilon and `π` insertion, the
deletion of unreachable code and the conversion to `IRCode` form), the slot fixup helpers, and
`domsort_ssa!` with its edge renaming. The dominator tree is the domtree area's model
(`JuliaLean/Compiler/src/ssair/domtree.lean`).

Modelling choices (see also `JuliaLean/Compiler/src/ssair/ir.lean`):

* IR values and statements are one inductive `IRV`, mirroring the Julia node types the code
  distinguishes. Literals, `QuoteNode` payloads and the names in `GlobalRef`s are opaque strings
  the model never inspects. `Bool` literals are `lit "Bool:true"` and `lit "Bool:false"`, and a
  `Symbol` is `sym`.
* Only the `:stmt` column of instruction streams is modelled. Types (`ssavaluetypes`, the
  `:type` of new nodes), line numbers, call infos and flags other than `IR_FLAG_NOTHROW` are not.
  `typ_for_val` is modelled only for the `error("unexpected val type")` it can throw.
* What `construct_ssa!` reads from the `OptimizationState` and the lattice is an input
  (`SSAInputs`): for each block, `nothing` or, for each slot, whether `vt.typ === Union{}`,
  `vt.undef`, the printed `vt.typ`, and whether `⊑(𝕃ₒ, sv.slottypes[slot], vt.typ)` fails (the
  `π` test). The handler of every statement (`compute_trycatch` and `gethandler`, both in
  `Compiler/src/inferencestate.jl`) is an input too, as the `:enter` index of the innermost
  handler or 0. So are the `sptypes` entries the `:static_parameter` fixup reads.
* Julia mutates the `PhiNode`s and `PhiCNode`s after inserting them into `ir.new_nodes`. The
  model keeps their index in the new-node stream and updates the stream in place.
* `insert_node!` (Compiler/src/ssair/ir.jl:752-770) is only called with a position that is an
  original statement, so it appends `(pos, attach_after, stmt)` and returns the new node's
  index. The `NewSSAValue` it leads to is `newssa k` for the `k`th new node.
-/

namespace JuliaLean.Compiler.ssair

/-! ## IR values -/

/-- IR values and statements: the node types `slot2ssa.jl` and the `userefs` machinery of
`Compiler/src/ssair/ir.jl` tell apart. `Option` stands for an unassigned slot (`#undef`) of a
`PhiNode` or `PhiCNode` value vector, and for the missing `val` of `ReturnNode()`,
`UpsilonNode()` and the missing `scope` of an `EnterNode`. -/
inductive IRV where
  | nothing
  /-- `UNDEF_TOKEN` (Compiler/src/ssair/ir.jl:584). -/
  | undefTok
  | slot (n : Int)
  | ssa (n : Int)
  | newssa (n : Int)
  | arg (n : Int)
  | glob (name : String)
  | sym (s : String)
  | lit (s : String)
  | quot (s : String)
  | expr (head : String) (args : Array IRV)
  | goto (label : Int)
  | gotoifnot (cond : IRV) (dest : Int)
  | ret (val : Option IRV)
  | enter (catchDest : Int) (scope : Option IRV)
  | newvar (slot : Int)
  | phi (edges : Array Int) (vals : Array (Option IRV))
  | phic (vals : Array (Option IRV))
  | upsilon (val : Option IRV)
  | pinode (val : IRV) (typ : String)

instance : Inhabited IRV := ⟨.nothing⟩

def IRV.boolLit (b : Bool) : IRV := .lit (if b then "Bool:true" else "Bool:false")

/-- An `Int` literal, printed as `Int64:<value>`. -/
def IRV.litInt? : IRV → Option Int
  | .lit s => if s.startsWith "Int64:" then (s.drop 6).toInt? else none
  | _ => none

def IRV.isExpr (h : String) : IRV → Bool
  | .expr h' _ => h' == h
  | _ => false

/-- `is_relevant_expr(e)`

Julia source: Compiler/src/ssair/ir.jl:659-668 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function is_relevant_expr(e::Expr)
    return e.head in (:call, :invoke, :invoke_modify,
                      :new, :splatnew, :(=), :(&),
                      :gc_preserve_begin, :gc_preserve_end,
                      :foreigncall, :foreignglobal, :isdefined, :copyast,
                      :throw_undef_if_not,
                      :cfunction, :pop_exception,
                      :leave,
                      :new_opaque_closure)
end
```
-/
def isRelevantHead (h : String) : Bool :=
  ["call", "invoke", "invoke_modify", "new", "splatnew", "=", "&", "gc_preserve_begin",
   "gc_preserve_end", "foreigncall", "foreignglobal", "isdefined", "copyast",
   "throw_undef_if_not", "cfunction", "pop_exception", "leave", "new_opaque_closure"].contains h

/-- The result of `_useref_getindex`: an operand, `UNDEF_TOKEN` (an unassigned phi value) or
`OOB_TOKEN`. -/
inductive URef where
  | val (v : IRV)
  | undef
  | oob

/-- The `phi`/`phic` value lookup of `_useref_getindex` (Compiler/src/ssair/ir.jl:621-628). -/
def phiValAt (vals : Array (Option IRV)) (op : Nat) : URef :=
  if op > vals.size then .oob else
  match vals[op - 1]? with
  | some (some v) => .val v
  | _ => .undef

/-- `_useref_getindex(stmt, op)` with its two halves `_useref_getindex_op1` and
`_useref_getindex_opN`.

Julia source: Compiler/src/ssair/ir.jl:586-656 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _useref_getindex(@nospecialize(stmt), op::Int)
    if op == 1
        return _useref_getindex_op1(stmt)
    else
        return _useref_getindex_opN(stmt, op)
    end
end

@noinline function _useref_getindex_op1(@nospecialize(stmt))
    if isa(stmt, Expr) && stmt.head === :(=)
        rhs = stmt.args[2]
        if isa(rhs, Expr) && is_relevant_expr(rhs)
            length(rhs.args) < 1 && return OOB_TOKEN
            return rhs.args[1]
        end
        return rhs
    elseif isa(stmt, Expr) # @assert is_relevant_expr(stmt)
        length(stmt.args) < 1 && return OOB_TOKEN
        return stmt.args[1]
    elseif isa(stmt, GotoIfNot)
        return stmt.cond
    elseif isa(stmt, ReturnNode)
        isdefined(stmt, :val) || return OOB_TOKEN
        return stmt.val
    elseif isa(stmt, EnterNode)
        isdefined(stmt, :scope) || return OOB_TOKEN
        return stmt.scope
    elseif isa(stmt, PiNode)
        isdefined(stmt, :val) || return OOB_TOKEN
        return stmt.val
    elseif isa(stmt, Union{AnySSAValue, GlobalRef})
        return stmt
    elseif isa(stmt, UpsilonNode)
        isdefined(stmt, :val) || return OOB_TOKEN
        return stmt.val
    elseif isa(stmt, PhiNode)
        length(stmt.values) < 1 && return OOB_TOKEN
        isassigned(stmt.values, 1) || return UNDEF_TOKEN
        return stmt.values[1]
    elseif isa(stmt, PhiCNode)
        length(stmt.values) < 1 && return OOB_TOKEN
        isassigned(stmt.values, 1) || return UNDEF_TOKEN
        return stmt.values[1]
    else
        return OOB_TOKEN
    end
end

@noinline function _useref_getindex_opN(@nospecialize(stmt), op::Int)
    if isa(stmt, Expr) && stmt.head === :(=)
        rhs = stmt.args[2]
        if isa(rhs, Expr) && is_relevant_expr(rhs)
            op > length(rhs.args) && return OOB_TOKEN
            return rhs.args[op]
        end
        return OOB_TOKEN
    elseif isa(stmt, Expr) # @assert is_relevant_expr(stmt)
        op > length(stmt.args) && return OOB_TOKEN
        return stmt.args[op]
    elseif isa(stmt, PhiNode)
        op > length(stmt.values) && return OOB_TOKEN
        isassigned(stmt.values, op) || return UNDEF_TOKEN
        return stmt.values[op]
    elseif isa(stmt, PhiCNode)
        op > length(stmt.values) && return OOB_TOKEN
        isassigned(stmt.values, op) || return UNDEF_TOKEN
        return stmt.values[op]
    else
        return OOB_TOKEN
    end
end
```
A literal `UNDEF_TOKEN` operand reads as `URef.undef`, as `_advance`'s `===` test sees it. -/
def urefGet (stmt : IRV) (op : Nat) : JM URef :=
  let tok : IRV → URef := fun v => match v with
    | .undefTok => .undef
    | v => .val v
  if op == 1 then
    match stmt with
    | .expr "=" args => do
      let rhs ← aget args 2
      match rhs with
      | .expr h rargs =>
        if isRelevantHead h then
          if rargs.size < 1 then pure .oob else pure (tok rargs[0]!)
        else pure (tok rhs)
      | _ => pure (tok rhs)
    | .expr _ args => if args.size < 1 then pure .oob else pure (tok args[0]!)
    | .gotoifnot c _ => pure (tok c)
    | .ret v => pure (match v with | some v => tok v | none => .oob)
    | .enter _ s => pure (match s with | some v => tok v | none => .oob)
    | .pinode v _ => pure (tok v)
    | .ssa _ | .newssa _ | .glob _ => pure (tok stmt)
    | .upsilon v => pure (match v with | some v => tok v | none => .oob)
    | .phi _ vals => pure (match phiValAt vals 1 with | .val v => tok v | r => r)
    | .phic vals => pure (match phiValAt vals 1 with | .val v => tok v | r => r)
    | _ => pure .oob
  else
    match stmt with
    | .expr "=" args => do
      let rhs ← aget args 2
      match rhs with
      | .expr h rargs =>
        if isRelevantHead h then
          if op > rargs.size then pure .oob else pure (tok rargs[op - 1]!)
        else pure .oob
      | _ => pure .oob
    | .expr _ args => if op > args.size then pure .oob else pure (tok args[op - 1]!)
    | .phi _ vals => pure (match phiValAt vals op with | .val v => tok v | r => r)
    | .phic vals => pure (match phiValAt vals op with | .val v => tok v | r => r)
    | _ => pure .oob

/-- The value assignment of the phi branches of `_useref_setindex!`
(Compiler/src/ssair/ir.jl:703-710): only an assigned slot may be overwritten. -/
def phiValSet (vals : Array (Option IRV)) (op : Nat) (v : IRV) : JM (Array (Option IRV)) :=
  if op > vals.size then throw "julia:BoundsError" else
  match vals[op - 1]? with
  | some (some _) => pure (vals.set! (op - 1) (some v))
  | _ => throw "julia:BoundsError"

/-- `_useref_setindex!(stmt, op, v)`: the new statement (Julia mutates `Expr`s and phi value
vectors in place and returns the same object; it rebuilds the immutable nodes).

Julia source: Compiler/src/ssair/ir.jl:670-715 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function _useref_setindex!(@nospecialize(stmt), op::Int, @nospecialize(v))
    if isa(stmt, Expr) && stmt.head === :(=)
        rhs = stmt.args[2]
        if isa(rhs, Expr)
            if is_relevant_expr(rhs)
                op > length(rhs.args) && throw(BoundsError())
                rhs.args[op] = v
                return stmt
            end
        end
        op == 1 || throw(BoundsError())
        stmt.args[2] = v
    elseif isa(stmt, Expr) # @assert is_relevant_expr(stmt)
        op > length(stmt.args) && throw(BoundsError())
        stmt.args[op] = v
    elseif isa(stmt, GotoIfNot)
        op == 1 || throw(BoundsError())
        stmt = GotoIfNot(v, stmt.dest)
    elseif isa(stmt, ReturnNode)
        op == 1 || throw(BoundsError())
        stmt = ReturnNode(v)
    elseif isa(stmt, EnterNode)
        op == 1 || throw(BoundsError())
        stmt = EnterNode(stmt.catch_dest, v)
    elseif isa(stmt, Union{AnySSAValue, Argument, GlobalRef})
        op == 1 || throw(BoundsError())
        stmt = v
    elseif isa(stmt, UpsilonNode)
        op == 1 || throw(BoundsError())
        stmt = UpsilonNode(v)
    elseif isa(stmt, PiNode)
        op == 1 || throw(BoundsError())
        stmt = PiNode(v, stmt.typ)
    elseif isa(stmt, PhiNode)
        op > length(stmt.values) && throw(BoundsError())
        isassigned(stmt.values, op) || throw(BoundsError())
        stmt.values[op] = v
    elseif isa(stmt, PhiCNode)
        op > length(stmt.values) && throw(BoundsError())
        isassigned(stmt.values, op) || throw(BoundsError())
        stmt.values[op] = v
    else
        throw(BoundsError())
    end
    return stmt
end
```
-/
def urefSet (stmt : IRV) (op : Nat) (v : IRV) : JM IRV :=
  match stmt with
  | .expr "=" args => do
    let rhs ← aget args 2
    match rhs with
    | .expr h rargs =>
      if isRelevantHead h then do
        if op > rargs.size then throw "julia:BoundsError"
        pure (.expr "=" (args.set! 1 (.expr h (rargs.set! (op - 1) v))))
      else if op == 1 then pure (.expr "=" (args.set! 1 v)) else throw "julia:BoundsError"
    | _ => if op == 1 then pure (.expr "=" (args.set! 1 v)) else throw "julia:BoundsError"
  | .expr h args =>
    if op > args.size then throw "julia:BoundsError" else pure (.expr h (args.set! (op - 1) v))
  | .gotoifnot _ d => if op == 1 then pure (.gotoifnot v d) else throw "julia:BoundsError"
  | .ret _ => if op == 1 then pure (.ret (some v)) else throw "julia:BoundsError"
  | .enter cd _ => if op == 1 then pure (.enter cd (some v)) else throw "julia:BoundsError"
  | .ssa _ | .newssa _ | .arg _ | .glob _ =>
    if op == 1 then pure v else throw "julia:BoundsError"
  | .upsilon _ => if op == 1 then pure (.upsilon (some v)) else throw "julia:BoundsError"
  | .pinode _ t => if op == 1 then pure (.pinode v t) else throw "julia:BoundsError"
  | .phi e vals => do pure (.phi e (← phiValSet vals op v))
  | .phic vals => do pure (.phic (← phiValSet vals op v))
  | _ => throw "julia:BoundsError"

/-- `userefs(x).relevant`

Julia source: Compiler/src/ssair/ir.jl:722-727 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function userefs(@nospecialize(x))
    relevant = (isa(x, Expr) && is_relevant_expr(x)) ||
        isa(x, GotoIfNot) || isa(x, ReturnNode) || isa(x, SSAValue) || isa(x, OldSSAValue) || isa(x, NewSSAValue) ||
        isa(x, PiNode) || isa(x, PhiNode) || isa(x, PhiCNode) || isa(x, UpsilonNode) || isa(x, EnterNode) || isa(x, Argument)
    return UseRefIterator(x, relevant)
end
```
-/
def userefsRelevant : IRV → Bool
  | .expr h _ => isRelevantHead h
  | .gotoifnot .. | .ret _ | .ssa _ | .newssa _ | .pinode .. | .phi .. | .phic _ | .upsilon _
  | .enter .. | .arg _ => true
  | _ => false

/-- `_advance(stmt, op)`: the next operand index after `op` that is not `UNDEF_TOKEN`, or
`nothing` at `OOB_TOKEN`.

Julia source: Compiler/src/ssair/ir.jl:729-736 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function _advance(@nospecialize(stmt), op)
    while true
        op += 1
        y = _useref_getindex(stmt, op)
        y === OOB_TOKEN && return nothing
        y === UNDEF_TOKEN || return op
    end
end
```
Every statement has fewer than `fuel` operands for the fuel the callers pass. -/
def urefAdvance (stmt : IRV) : Nat → Nat → JM (Option (Nat × IRV))
  | 0, _ => outOfBudget
  | fuel + 1, op => do
    match ← urefGet stmt (op + 1) with
    | .oob => pure none
    | .undef => urefAdvance stmt fuel (op + 1)
    | .val v => pure (some (op + 1, v))

/-- A bound on the operand count of a statement, the fuel of the `userefs` loops. -/
def IRV.opBound : IRV → Nat
  | .expr _ args => args.size + 1 +
      (args.foldl (fun n a => match a with | .expr _ b => n + b.size | _ => n) 0) + 2
  | .phi _ vals => vals.size + 2
  | .phic vals => vals.size + 2
  | _ => 3

/-- `for op in userefs(stmt) ... end; return urs[]` with the loop body `f`, which sees the
current statement, the operand index and its value and returns the new statement and state,
or `.inr` to leave the function early with that result (the body's `return`). The iteration
re-reads the statement after each body, like `iterate(::UseRefIterator)`. -/
def userefsFold {σ : Type} (f : IRV → Nat → IRV → σ → JM (Sum (IRV × σ) (IRV × σ)))
    (stmt : IRV) (s : σ) : JM (Sum (IRV × σ) (IRV × σ)) := do
  if !userefsRelevant stmt then return .inl (stmt, s)
  let fuel := stmt.opBound + 1
  let rec go : Nat → IRV → Nat → σ → JM (Sum (IRV × σ) (IRV × σ))
    | 0, _, _, _ => outOfBudget
    | k + 1, stmt, op, s => do
      match ← urefAdvance stmt (fuel + 1) op with
      | none => pure (.inl (stmt, s))
      | some (op', v) =>
        match ← f stmt op' v s with
        | .inl (stmt, s) => go k stmt op' s
        | .inr r => pure (.inr r)
  go (fuel + 1) stmt 0 s

/-! ## Instruction streams and the CFG -/

/-- A basic block with its statement range `first:last` (Compiler/src/ssair/basicblock.jl:18-22). -/
structure SBlock where
  first : Int
  last : Int
  preds : Array Int
  succs : Array Int
  deriving Inhabited

/-- `struct CFG` (Compiler/src/ssair/ir.jl:6-10). -/
structure SCFG where
  blocks : Array SBlock
  index : Array Int
  deriving Inhabited

def SCFG.domBlocks (cfg : SCFG) : Blocks :=
  cfg.blocks.map fun b => { preds := b.preds, succs := b.succs }

/-- `searchsortedfirst(v, x, lt=(<=))` (base/sort.jl:184-199), the binary search. -/
def searchsortedfirstLe (v : Array Int) (x : Int) : JM Int :=
  let rec go : Nat → Int → Int → JM Int
    | 0, _, _ => outOfBudget
    | fuel + 1, lo, len =>
      if len == 0 then pure lo else do
        let half := len / 2
        let m := lo + half
        if (← aget v m) <= x then go fuel (m + 1) (len - (half + 1))
        else go fuel lo half
  go (v.size + 2) 1 v.size

/-- `block_for_inst(cfg, inst)`

Julia source: Compiler/src/ssair/ir.jl:36-38, 44 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function block_for_inst(index::Vector{Int}, inst::Int)
    return searchsortedfirst(index, inst, lt=(<=))
end
block_for_inst(cfg::CFG, inst::Int) = block_for_inst(cfg.index, inst)
```
-/
def blockForInst (cfg : SCFG) (inst : Int) : JM Int := searchsortedfirstLe cfg.index inst

/-- A pending node: `NewNodeInfo(pos, attach_after)` and its `:stmt`
(Compiler/src/ssair/ir.jl:403-421). -/
structure NewNode where
  pos : Int
  attachAfter : Bool
  stmt : IRV
  deriving Inhabited

/-- The `IRCode` fields the modelled code reads or writes: the `:stmt` and `IR_FLAG_NOTHROW`
columns of `ir.stmts`, the CFG and the new-node stream. -/
structure SIR where
  stmts : Array IRV
  nothrow : Array Bool
  cfg : SCFG
  newNodes : Array NewNode
  deriving Inhabited

/-- `insert_node!(ir, pos::Int, inst, attach_after)` for an original statement `pos`
(Compiler/src/ssair/ir.jl:752-770): returns the new node's index in `ir.new_nodes`; the
`SSAValue` Julia returns is that index plus `length(ir.stmts)`. -/
def SIR.insert (ir : SIR) (pos : Int) (stmt : IRV) (attachAfter : Bool := false) : SIR × Int :=
  ({ ir with newNodes := ir.newNodes.push ⟨pos, attachAfter, stmt⟩ }, ir.newNodes.size + 1)

/-- `ir[SSAValue(id)][:stmt]` (Compiler/src/ssair/ir.jl:542-554): `InvalidIRError` for an
id outside the statements and new nodes. -/
def SIR.stmtAt (ir : SIR) (id : Int) : JM IRV := do
  unless id ≥ 1 do throw "julia:InvalidIRError"
  if id > ir.stmts.size then
    unless id - ir.stmts.size ≤ ir.newNodes.size do throw "julia:InvalidIRError"
    return (← aget ir.newNodes (id - ir.stmts.size)).stmt
  aget ir.stmts id

def SIR.setNewStmt (ir : SIR) (k : Int) (f : IRV → JM IRV) : JM SIR := do
  let n ← aget ir.newNodes k
  pure { ir with newNodes := ← aset ir.newNodes k { n with stmt := ← f n.stmt } }

/-- `is_valid_phiblock_stmt(stmt)`

Julia source: Compiler/src/ssair/ir.jl:153-158 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function is_valid_phiblock_stmt(@nospecialize(stmt))
    isa(stmt, PhiNode) && return true
    isa(stmt, Union{UpsilonNode, PhiCNode, SSAValue}) && return false
    isa(stmt, Expr) && return false
    return true
end
```
-/
def isValidPhiblockStmt : IRV → Bool
  | .phi .. => true
  | .upsilon _ | .phic _ | .ssa _ => false
  | .expr .. => false
  | _ => true

/-- `first_insert_for_bb(code, cfg, block)`

Julia source: Compiler/src/ssair/ir.jl:160-177 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function first_insert_for_bb(code::Vector{Any}, cfg::CFG, block::Int)
    stmts = cfg.blocks[block].stmts
    lastnonphiidx = first(stmts)
    for idx in stmts
        stmt = code[idx]
        if !isa(stmt, PhiNode)
            if !is_valid_phiblock_stmt(stmt)
                return lastnonphiidx
            end
        else
            lastnonphiidx = idx + 1
        end
    end
    if lastnonphiidx > last(stmts)
        error("any insert position isn't found")
    end
    return lastnonphiidx
end
```
-/
def firstInsertForBB (code : Array IRV) (cfg : SCFG) (block : Int) : JM Int := do
  let b ← aget cfg.blocks block
  let rec go : List Int → Int → JM Int
    | [], lastnonphi =>
      if lastnonphi > b.last then throw "julia:ErrorException" else pure lastnonphi
    | idx :: rest, lastnonphi => do
      match ← aget code idx with
      | .phi .. => go rest (idx + 1)
      | stmt => if !isValidPhiblockStmt stmt then pure lastnonphi else go rest lastnonphi
  go (irange b.first b.last) b.first

/-- `isterminator(stmt)` (Compiler/src/ssair/ir.jl:3-4). -/
def isTerminator : IRV → Bool
  | .goto _ | .gotoifnot .. | .ret _ | .enter .. => true
  | s => s.isExpr "leave"

/-! ## Slot def/use scan -/

/-- `mutable struct SlotInfo` (Compiler/src/ssair/slot2ssa.jl:3-7). -/
structure SlotInfo where
  defs : Array Int
  uses : Array Int
  deriving Inhabited, BEq, Repr

def pushDef (r : Array SlotInfo) (s : Int) (idx : Int) : JM (Array SlotInfo) := do
  let si ← aget r s
  aset r s { si with defs := si.defs.push idx }

def pushUse (r : Array SlotInfo) (s : Int) (idx : Int) : JM (Array SlotInfo) := do
  let si ← aget r s
  aset r s { si with uses := si.uses.push idx }

/-- `scan_entry!(result, idx, stmt)`

Julia source: Compiler/src/ssair/slot2ssa.jl:9-32 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function scan_entry!(result::Vector{SlotInfo}, idx::Int, @nospecialize(stmt))
    # NewvarNodes count as defs for the purpose
    # of liveness analysis (i.e. they kill use chains)
    if isa(stmt, NewvarNode)
        push!(result[slot_id(stmt.slot)].defs, idx)
        return
    elseif isexpr(stmt, :(=))
        arg1 = stmt.args[1]
        if isa(arg1, SlotNumber)
            push!(result[slot_id(arg1)].defs, idx)
        end
        stmt = stmt.args[2]
    end
    if isa(stmt, SlotNumber)
        push!(result[slot_id(stmt)].uses, idx)
        return
    end
    for op in userefs(stmt)
        val = op[]
        if isa(val, SlotNumber)
            push!(result[slot_id(val)].uses, idx)
        end
    end
end
```
-/
def scanEntry (result : Array SlotInfo) (idx : Int) (stmt : IRV) : JM (Array SlotInfo) := do
  if let .newvar s := stmt then return ← pushDef result s idx
  let (result, stmt) ← match stmt with
    | .expr "=" args => do
      let a1 ← aget args 1
      let result ← match a1 with
        | .slot s => pushDef result s idx
        | _ => pure result
      pure (result, ← aget args 2)
    | _ => pure (result, stmt)
  if let .slot s := stmt then return ← pushUse result s idx
  let r ← userefsFold (fun st _ v result => do
      match v with
      | .slot s => pure (.inl (st, ← pushUse result s idx))
      | _ => pure (.inl (st, result))) stmt result
  match r with
  | .inl (_, result) | .inr (_, result) => pure result

/-- `scan_slot_def_use(nargs, ci, code)` with `nslots = length(ci.slotflags)`.

Julia source: Compiler/src/ssair/slot2ssa.jl:34-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function scan_slot_def_use(nargs::Int, ci::CodeInfo, code::Vector{Any})
    nslots = length(ci.slotflags)
    result = SlotInfo[SlotInfo() for i = 1:nslots]
    # Set defs for arguments
    for var in result[1:nargs]
        push!(var.defs, 0)
    end
    for idx in 1:length(code)
        stmt = code[idx]
        scan_entry!(result, idx, stmt)
    end
    result
end
```
`result[1:nargs]` throws a `BoundsError` when `nargs > nslots`; a negative `nargs` gives an
empty range. -/
def scanSlotDefUse (nargs : Int) (nslots : Nat) (code : Array IRV) : JM (Array SlotInfo) := do
  let result : Array SlotInfo := Array.replicate nslots ⟨#[], #[]⟩
  if nargs > nslots then throw "julia:BoundsError"
  let result ← (irange 1 nargs).foldlM (fun r i => pushDef r i 0) result
  (irange 1 code.size).foldlM (fun r idx => do scanEntry r idx (← aget code idx)) result

/-! ## SSA renumbering -/

/-- `renumber_ssa(stmt::SSAValue, ssanums, new_ssa)` on the id.

Julia source: Compiler/src/ssair/slot2ssa.jl:48-56 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function renumber_ssa(stmt::SSAValue, ssanums::Vector{SSAValue}, new_ssa::Bool=false)
    id = stmt.id
    if id > length(ssanums)
        return stmt
    end
    val = ssanums[id]
    @assert val.id > 0
    return val
end
```
-/
def renumberSsa (id : Int) (ssanums : Array Int) : JM IRV := do
  if id > ssanums.size then return .ssa id
  let v ← aget ssanums id
  unless v > 0 do throw "julia:AssertionError"
  pure (.ssa v)

/-- `ssamap(f, stmt)` (Compiler/src/utilities.jl:242-251): `f` on every `SSAValue` operand. -/
def ssamap (f : Int → JM IRV) (stmt : IRV) : JM IRV := do
  let r ← userefsFold (fun st op v (_ : Unit) => do
      match v with
      | .ssa id => pure (.inl (← urefSet st op (← f id), ()))
      | _ => pure (.inl (st, ()))) stmt ()
  match r with
  | .inl (s, _) | .inr (s, _) => pure s

/-- `renumber_ssa!(stmt, ssanums, new_ssa)`

Julia source: Compiler/src/ssair/slot2ssa.jl:58-61 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function renumber_ssa!(@nospecialize(stmt), ssanums::Vector{SSAValue}, new_ssa::Bool=false)
    isa(stmt, SSAValue) && return renumber_ssa(stmt, ssanums, new_ssa)
    return ssamap(val->renumber_ssa(val, ssanums, new_ssa), stmt)
end
```
-/
def renumberSsa! (stmt : IRV) (ssanums : Array Int) : JM IRV :=
  match stmt with
  | .ssa id => renumberSsa id ssanums
  | _ => ssamap (fun id => renumberSsa id ssanums) stmt

/-- `new_to_regular(stmt, new_offset)`

Julia source: Compiler/src/ssair/slot2ssa.jl:71-80 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function new_to_regular(@nospecialize(stmt), new_offset::Int)
    urs = userefs(stmt)
    for op in urs
        val = op[]
        if isa(val, NewSSAValue)
            op[] = SSAValue(val.id + new_offset)
        end
    end
    return urs[]
end
```
-/
def newToRegular (stmt : IRV) (off : Int) : JM IRV := do
  let r ← userefsFold (fun st op v (_ : Unit) => do
      match v with
      | .newssa id => pure (.inl (← urefSet st op (.ssa (id + off)), ()))
      | _ => pure (.inl (st, ()))) stmt ()
  match r with
  | .inl (s, _) | .inr (s, _) => pure s

/-- `make_ssa!(ci, code, idx, typ)` without the type: the assignment at `idx` becomes its
right-hand side and the slot's value is `SSAValue(idx)`.

Julia source: Compiler/src/ssair/slot2ssa.jl:63-69 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function make_ssa!(ci::CodeInfo, code::Vector{Any}, idx::Int, @nospecialize(typ))
    stmt = code[idx]
    @assert isexpr(stmt, :(=))
    code[idx] = stmt.args[2]
    (ci.ssavaluetypes::Vector{Any})[idx] = typ
    return SSAValue(idx)
end
```
-/
def makeSsa! (code : Array IRV) (idx : Int) : JM (Array IRV × IRV) := do
  match ← aget code idx with
  | .expr "=" args => pure (← aset code idx (← aget args 2), .ssa idx)
  | _ => throw "julia:AssertionError"

/-- `typ_for_val(x, ci, ir, idx, slottypes)`, for the errors it can throw only (the types it
returns are not modelled).

Julia source: Compiler/src/ssair/slot2ssa.jl:162-180 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function typ_for_val(@nospecialize(x), ci::CodeInfo, ir::IRCode, idx::Int, slottypes::Vector{Any})
    if isa(x, Expr)
        if x.head === :static_parameter
            return ir.sptypes[x.args[1]::Int].typ
        elseif x.head === :boundscheck
            return Bool
        elseif x.head === :copyast
            return typ_for_val(x.args[1], ci, ir, idx, slottypes)
        end
        return (ci.ssavaluetypes::Vector{Any})[idx]
    end
    isa(x, GlobalRef) && return globalref_rt(x, ci)
    isa(x, SSAValue) && return (ci.ssavaluetypes::Vector{Any})[x.id]
    isa(x, Argument) && return slottypes[x.n]
    isa(x, NewSSAValue) && return types(ir)[new_to_regular(x, length(ir.stmts))]
    isa(x, QuoteNode) && return Const(x.value)
    isa(x, Union{Symbol, PiNode, PhiNode, SlotNumber}) && error("unexpected val type")
    return Const(x)
end
```
The indexing into `ssavaluetypes`, `slottypes` and `sptypes` is in bounds on the inputs
`construct_ssa!` sees (every operand names an existing statement, argument or static
parameter) and is not modelled. -/
def typForValCheck : Nat → IRV → JM Unit
  | 0, _ => outOfBudget
  | fuel + 1, x =>
    match x with
    | .expr "copyast" args => do typForValCheck fuel (← aget args 1)
    | .expr .. => pure ()
    | .sym _ | .pinode .. | .phi .. | .slot _ => throw "julia:ErrorException"
    | _ => pure ()

/-! ## Slot fixups -/

/-- The undef-ness value paired with a slot's current value: `true`, `false` or the
`NewSSAValue` of an undef-tracking phi. -/
inductive DefV where
  | bool (b : Bool)
  | nss (k : Int)
  deriving Inhabited, BEq

def DefV.toIRV : DefV → IRV
  | .bool b => IRV.boolLit b
  | .nss k => .newssa k

/-- The `sptypes` entry the `:static_parameter` fixup reads: `some q` when the type is a
`Const`, with `q` the statement `quoted(ty.val)`; `none` otherwise. -/
abbrev SpInfo := Array (Option IRV)

/-- The static inputs of the fixups. -/
structure FixCtx where
  slotnames : Array String
  sp : SpInfo

/-- `fixup_slot!(ir, ci, idx, slot, ssa, def_ssa)`

Julia source: Compiler/src/ssair/slot2ssa.jl:82-97 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function fixup_slot!(ir::IRCode, ci::CodeInfo, idx::Int, slot::Int, @nospecialize(ssa), @nospecialize(def_ssa))
    # We don't really have the information here to get rid of these.
    # We'll do so later
    if ssa === UNDEF_TOKEN
        insert_node!(ir, idx, NewInstruction(
            Expr(:throw_undef_if_not, ci.slotnames[slot], false), Any))
        return UNDEF_TOKEN
    elseif has_flag(ir.stmts[idx], IR_FLAG_NOTHROW)
        # if the `isdefined`-ness of this slot is guaranteed by abstract interpretation,
        # there is no need to form a `:throw_undef_if_not`
    elseif def_ssa !== true
        insert_node!(ir, idx, NewInstruction(
            Expr(:throw_undef_if_not, ci.slotnames[slot], def_ssa), Any))
    end
    return ssa
end
```
-/
def fixupSlot! (C : FixCtx) (ir : SIR) (idx slot : Int) (ssa : IRV) (defSsa : DefV) :
    JM (SIR × IRV) := do
  if let .undefTok := ssa then
    let name ← aget C.slotnames slot
    let (ir, _) := ir.insert idx (.expr "throw_undef_if_not" #[.sym name, IRV.boolLit false])
    return (ir, .undefTok)
  if ← aget ir.nothrow idx then return (ir, ssa)
  if defSsa != .bool true then
    let name ← aget C.slotnames slot
    let (ir, _) := ir.insert idx (.expr "throw_undef_if_not" #[.sym name, defSsa.toIRV])
    return (ir, ssa)
  return (ir, ssa)

/-- The slot renaming `fixemup!` is called with: `rename_slot(x)` for a slot `x` that passes
`slot_filter`. -/
abbrev Renames := Array (IRV × DefV)

/-- `fixemup!(slot_filter, rename_slot, ir, ci, idx, stmt)`. A slot `x` passes `slot_filter` when
`flt (slot_id(x))`, and `rename_slot(x)` is `ren (slot_id(x))`. `rename_uses!` passes a filter that
accepts every slot and `renames[slot_id(x)]`, `fixup_uses!` the filter `slot_id(x) == slot` and
`ssa => true`. `fuel` bounds the nesting of `(=)`.

Julia source: Compiler/src/ssair/slot2ssa.jl:99-149 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function fixemup!(@specialize(slot_filter), @specialize(rename_slot), ir::IRCode, ci::CodeInfo, idx::Int, @nospecialize(stmt))
    if isa(stmt, SlotNumber) && slot_filter(stmt)
        return fixup_slot!(ir, ci, idx, slot_id(stmt), rename_slot(stmt)...)
    end
    if isexpr(stmt, :(=))
        stmt.args[2] = fixemup!(slot_filter, rename_slot, ir, ci, idx, stmt.args[2])
        return stmt
    end
    if isa(stmt, PhiNode)
        for i = 1:length(stmt.edges)
            isassigned(stmt.values, i) || continue
            val = stmt.values[i]
            isa(val, SlotNumber) || continue
            slot_filter(val) || continue
            bb_idx = block_for_inst(ir.cfg, Int(stmt.edges[i]))
            from_bb_terminator = last(ir.cfg.blocks[bb_idx].stmts)
            stmt.values[i] = fixup_slot!(ir, ci, from_bb_terminator, slot_id(val), rename_slot(val)...)
        end
        return stmt
    end
    if isexpr(stmt, :isdefined)
        val = stmt.args[1]
        if isa(val, SlotNumber)
            ssa, undef_ssa = rename_slot(val)
            return undef_ssa
        end
        return stmt
    end
    urs = userefs(stmt)
    for op in urs
        val = op[]
        if isa(val, SlotNumber) && slot_filter(val)
            x = fixup_slot!(ir, ci, idx, slot_id(val), rename_slot(val)...)
            # We inserted an undef error node. Delete subsequent statement
            # to avoid confusing the optimizer
            if x === UNDEF_TOKEN
                return nothing
            end
            op[] = x
        elseif isexpr(val, :static_parameter)
            ty = typ_for_val(val, ci, ir, idx, Any[])
            if isa(ty, Const)
                inst = NewInstruction(quoted(ty.val), ty)
            else
                inst = NewInstruction(val, ty)
            end
            op[] = NewSSAValue(insert_node!(ir, idx, inst).id - length(ir.stmts))
        end
    end
    return urs[]
end
```
-/
def fixemup! (C : FixCtx) (flt : Int → Bool) (ren : Int → JM (IRV × DefV)) :
    Nat → SIR → Int → IRV → JM (SIR × IRV)
  | 0, _, _, _ => outOfBudget
  | fuel + 1, ir, idx, stmt => do
    if let .slot s := stmt then
      if flt s then
        let (v, d) ← ren s
        return ← fixupSlot! C ir idx s v d
    if let .expr "=" args := stmt then
      let (ir, rhs) ← fixemup! C flt ren fuel ir idx (← aget args 2)
      return (ir, .expr "=" (← aset args 2 rhs))
    if let .phi edges vals := stmt then
      let mut ir := ir
      let mut vals := vals
      for i in irange 1 edges.size do
        match vals[(i - 1).toNat]? with
        | some (some (.slot s)) =>
          if !flt s then continue
          let bbIdx ← blockForInst ir.cfg (← aget edges i)
          let term := (← aget ir.cfg.blocks bbIdx).last
          let (v, d) ← ren s
          let (ir', x) ← fixupSlot! C ir term s v d
          ir := ir'
          vals ← aset vals i (some x)
        | _ => pure ()
      return (ir, .phi edges vals)
    if let .expr "isdefined" args := stmt then
      if let .slot s := (← aget args 1) then
        let (_, d) ← ren s
        return (ir, d.toIRV)
      return (ir, stmt)
    let r ← userefsFold (fun st op v (ir : SIR) => do
        match v with
        | .slot s => do
          if !flt s then return .inl (st, ir)
          let (rv, rd) ← ren s
          let (ir, x) ← fixupSlot! C ir idx s rv rd
          if let .undefTok := x then return .inr (.nothing, ir)
          pure (.inl (← urefSet st op x, ir))
        | .expr "static_parameter" spargs => do
          let i ← match (← aget spargs 1).litInt? with
            | some i => pure i
            | none => throw "julia:TypeError"
          let inst ← match ← aget C.sp i with
            | some q => pure q
            | none => pure v
          let (ir, k) := ir.insert idx inst
          pure (.inl (← urefSet st op (.newssa k), ir))
        | _ => pure (.inl (st, ir))) stmt ir
    match r with
    | .inl (s, ir) => pure (ir, s)
    | .inr (s, ir) => pure (ir, s)

/-- `rename_uses!(ir, ci, idx, stmt, renames)`

Julia source: Compiler/src/ssair/slot2ssa.jl:157-159 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rename_uses!(ir::IRCode, ci::CodeInfo, idx::Int, @nospecialize(stmt), renames::Vector{Pair{Any, Any}})
    return fixemup!(::SlotNumber->true, x::SlotNumber->renames[slot_id(x)], ir, ci, idx, stmt)
end
```
-/
def renameUses! (C : FixCtx) (ir : SIR) (idx : Int) (stmt : IRV) (renames : Renames) :
    JM (SIR × IRV) :=
  fixemup! C (fun _ => true) (fun s => aget renames s) 4 ir idx stmt

/-- `fixup_uses!(ir, ci, code, uses, slot, ssa)`: returns the IR (with any new nodes) and
`code`. Its only caller is the disabled `if false` branch of `construct_ssa!`
(Compiler/src/ssair/slot2ssa.jl:578-599).

Julia source: Compiler/src/ssair/slot2ssa.jl:151-155 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function fixup_uses!(ir::IRCode, ci::CodeInfo, code::Vector{Any}, uses::Vector{Int}, slot::Int, @nospecialize(ssa))
    for use in uses
        code[use] = fixemup!(x::SlotNumber->slot_id(x)==slot, ::SlotNumber->Pair{Any,Any}(ssa, true), ir, ci, use, code[use])
    end
end
```
-/
def fixupUses! (C : FixCtx) (ir : SIR) (code : Array IRV) (uses : Array Int) (slot : Int)
    (ssa : IRV) : JM (SIR × Array IRV) :=
  uses.foldlM (fun (ir, code) use => do
      let (ir, s) ← fixemup! C (· == slot) (fun _ => pure (ssa, .bool true)) 4 ir use
        (← aget code use)
      pure (ir, ← aset code use s))
    (ir, code)

/-! ## Liveness and the iterated dominance frontier -/

/-- `struct BlockLiveness` (Compiler/src/ssair/slot2ssa.jl:182-185). -/
structure BlockLiveness where
  defBBs : Array Int
  liveInBBs : Option (Array Int)
  deriving Inhabited, BEq, Repr

/-- The merge loop of `compute_live_ins` (Compiler/src/ssair/slot2ssa.jl:503-515). Returns
`bb_defs` and `bb_uses`. -/
def liveMerge (cfg : SCFG) (defs uses : Array Int) :
    Nat → Int → Bool → Nat → Nat → Array Int → Array Int → JM (Array Int × Array Int)
  | 0, _, _, _, _, _, _ => outOfBudget
  | fuel + 1, lastBlock, blockHasDef, di, ui, bbDefs, bbUses =>
    if !(di < defs.size || ui < uses.size) then pure (bbDefs, bbUses) else do
      let isDef := ui ≥ uses.size || (di < defs.size && defs[di]! < uses[ui]!)
      let block ← blockForInst cfg (if isDef then defs[di]! else uses[ui]!)
      let di := di + (if isDef then 1 else 0)
      let ui := ui + (if isDef then 0 else 1)
      let (bbDefs, bbUses, blockHasDef) :=
        if lastBlock != block || (isDef && !blockHasDef) then
          (if isDef then (bbDefs.push block, bbUses, isDef) else (bbDefs, bbUses.push block, isDef))
        else (bbDefs, bbUses, blockHasDef)
      liveMerge cfg defs uses fuel block blockHasDef di ui bbDefs bbUses

/-- The predecessors `Iterators.filter(p->p != 0 && !(p in bb_defs), cfg.blocks[bb].preds)`. -/
def livePreds (cfg : SCFG) (bbDefs : Array Int) (bb : Int) : JM (Array Int) := do
  pure ((← aget cfg.blocks bb).preds.filter fun p => p != 0 && !bbDefs.contains p)

/-- The `while !isempty(worklist)` loop of `compute_live_ins`
(Compiler/src/ssair/slot2ssa.jl:522-527). `extra` is the `BitSet` as a sorted list. -/
def liveWorklist (cfg : SCFG) (bbDefs bbUses : Array Int) :
    Nat → Array Int → List Int → JM (List Int)
  | 0, _, _ => outOfBudget
  | fuel + 1, wl, extra =>
    match wl.back? with
    | none => pure extra
    | some elem =>
      let wl := wl.pop
      if bbUses.contains elem || extra.contains elem then liveWorklist cfg bbDefs bbUses fuel wl extra
      else do
        let ps ← livePreds cfg bbDefs elem
        liveWorklist cfg bbDefs bbUses fuel (wl ++ ps) (bsInsert elem extra)

/-- `compute_live_ins(cfg, defs, uses)`

Julia source: Compiler/src/ssair/slot2ssa.jl:494-530 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function compute_live_ins(cfg::CFG, defs::Vector{Int}, uses::Vector{Int})
    # We remove from `uses` any block where all uses are dominated
    # by a def. This prevents insertion of dead phi nodes at the top
    # of such a block if that block happens to be in a loop
    bb_defs = Int[] # blocks with a def
    bb_uses = Int[] # blocks with a use that is not dominated by a def

    # We do a sorted joint iteration over the instructions listed
    # in defs and uses following a pattern similar to mergesort
    last_block, block_has_def = 0, false
    defs_i = uses_i = 1
    while defs_i <= lastindex(defs) || uses_i <= lastindex(uses)
        is_def = uses_i > lastindex(uses) || defs_i <= lastindex(defs) && defs[defs_i] < uses[uses_i]
        block = block_for_inst(cfg, is_def ? defs[defs_i] : uses[uses_i])
        defs_i += is_def
        uses_i += !is_def
        if last_block != block || is_def && !block_has_def
            push!(is_def ? bb_defs : bb_uses, block)
            block_has_def = is_def
        end
        last_block = block
    end
    # To obtain live ins from bb_uses, recursively add predecessors
    extra_liveins = BitSet()
    worklist = Int[]
    for bb in bb_uses
        append!(worklist, Iterators.filter(p->p != 0 && !(p in bb_defs), cfg.blocks[bb].preds))
    end
    while !isempty(worklist)
        elem = pop!(worklist)
        (elem in bb_uses || elem in extra_liveins) && continue
        push!(extra_liveins, elem)
        append!(worklist, Iterators.filter(p->p != 0 && !(p in bb_defs), cfg.blocks[elem].preds))
    end
    append!(bb_uses, extra_liveins)
    BlockLiveness(bb_defs, bb_uses)
end
```
`compute_live_ins(cfg, slot::SlotInfo)` (line 492) passes `slot.defs` and `slot.uses`. Every
worklist entry is a predecessor edge, and a block's predecessors are appended at most once
after it enters `extra_liveins`, so the edge count plus the block count bounds the loop. -/
def computeLiveIns (cfg : SCFG) (defs uses : Array Int) : JM BlockLiveness := do
  let (bbDefs, bbUses) ← liveMerge cfg defs uses (defs.size + uses.size + 1) 0 false 0 0 #[] #[]
  let wl ← bbUses.foldlM (fun wl bb => do pure (wl ++ (← livePreds cfg bbDefs bb))) #[]
  let fuel := cfg.blocks.foldl (fun n b => n + b.preds.size) 0 + wl.size + cfg.blocks.size + 1
  let extra ← liveWorklist cfg bbDefs bbUses fuel wl []
  pure ⟨bbDefs, some (bbUses ++ extra.toArray)⟩

/-! ### The binary heap of `Compiler/src/ssair/heap.jl` under `By(x -> -x[2])` -/

/-- `lt(By(x -> -x[2]), a, b)`: `isless(-a[2], -b[2])`. -/
def heapLt (a b : Int × Int) : Bool := -a.2 < -b.2

/-- `percolate_down!(xs, i, x, o, len)`

Julia source: Compiler/src/ssair/heap.jl:12-21 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function percolate_down!(xs::Vector, i::Integer, x, o::Ordering, len::Integer=length(xs))
    @inbounds while (l = heapleft(i)) <= len
        r = heapright(i)
        j = r > len || lt(o, xs[l], xs[r]) ? l : r
        lt(o, xs[j], x) || break
        xs[i] = xs[j]
        i = j
    end
    xs[i] = x
end
```
`i` at least doubles each step, so `len + 1` steps are enough. -/
def percolateDown (xs : Array (Int × Int)) (i : Int) (x : Int × Int) (len : Int) :
    JM (Array (Int × Int)) :=
  let rec go : Nat → Array (Int × Int) → Int → JM (Array (Int × Int))
    | 0, _, _ => outOfBudget
    | fuel + 1, xs, i => do
      let l := 2 * i
      if l <= len then
        let r := 2 * i + 1
        let j ← if r > len then pure l else do
          if heapLt (← aget xs l) (← aget xs r) then pure l else pure r
        if heapLt (← aget xs j) x then go fuel (← aset xs i (← aget xs j)) j
        else aset xs i x
      else aset xs i x
  go (xs.size + 2) xs i

/-- `percolate_up!(xs, i, x, o)` (Compiler/src/ssair/heap.jl:24-31). -/
def percolateUp (xs : Array (Int × Int)) (i : Int) (x : Int × Int) : JM (Array (Int × Int)) :=
  let rec go : Nat → Array (Int × Int) → Int → JM (Array (Int × Int))
    | 0, _, _ => outOfBudget
    | fuel + 1, xs, i => do
      let j := i / 2
      if j >= 1 then
        if heapLt x (← aget xs j) then go fuel (← aset xs i (← aget xs j)) j
        else aset xs i x
      else aset xs i x
  go (xs.size + 2) xs i

/-- `heappop!(xs, o)` (Compiler/src/ssair/heap.jl:39-46). -/
def heappop (xs : Array (Int × Int)) : JM ((Int × Int) × Array (Int × Int)) := do
  let x ← aget xs 1
  let y := xs.back!
  let xs := xs.pop
  if xs.isEmpty then return (x, xs)
  return (x, ← percolateDown xs 1 y xs.size)

/-- `heappush!(xs, x, o)` (Compiler/src/ssair/heap.jl:54-59). -/
def heappush (xs : Array (Int × Int)) (x : Int × Int) : JM (Array (Int × Int)) :=
  let xs := xs.push x
  percolateUp xs xs.size x

/-- `heapify!(xs, o)` (Compiler/src/ssair/heap.jl:66-71). -/
def heapify (xs : Array (Int × Int)) : JM (Array (Int × Int)) :=
  ((irange 1 (xs.size / 2)).reverse).foldlM
    (fun xs i => do percolateDown xs i (← aget xs i) xs.size) xs

/-- The `for succ in succs` loop of `iterated_dominance_frontier`
(Compiler/src/ssair/slot2ssa.jl:248-275). The state is `(heap, phiblocks, processed)`, with
`processed` a sorted list. -/
def idfSuccLoop (cfg : SCFG) (live : BlockLiveness) (dt : GenericDomTree) (level : Int) :
    List Int → Array (Int × Int) × Array Int × List Int →
    JM (Array (Int × Int) × Array Int × List Int)
  | [], st => pure st
  | succ :: rest, (heap, phiblocks, processed) => do
    let succLevel := (← aget dt.nodes succ).level
    if succLevel > level then return ← idfSuccLoop cfg live dt level rest (heap, phiblocks, processed)
    if processed.contains succ then
      return ← idfSuccLoop cfg live dt level rest (heap, phiblocks, processed)
    let processed := bsInsert succ processed
    if let some li := live.liveInBBs then
      if !li.contains succ then
        return ← idfSuccLoop cfg live dt level rest (heap, phiblocks, processed)
    let phiblocks := phiblocks.push succ
    let heap ← if !live.defBBs.contains succ then heappush heap (succ, succLevel) else pure heap
    idfSuccLoop cfg live dt level rest (heap, phiblocks, processed)

/-- The `while !isempty(worklist)` loop of `iterated_dominance_frontier`
(Compiler/src/ssair/slot2ssa.jl:245-283). `visited` is a sorted list. -/
def idfWorklist (cfg : SCFG) (live : BlockLiveness) (dt : GenericDomTree) (level : Int) :
    Nat → Array Int → Array (Int × Int) × Array Int × List Int × List Int →
    JM (Array (Int × Int) × Array Int × List Int × List Int)
  | 0, _, _ => outOfBudget
  | fuel + 1, wl, (heap, phiblocks, processed, visited) =>
    match wl.back? with
    | none => pure (heap, phiblocks, processed, visited)
    | some active => do
      let wl := wl.pop
      let succs := (← aget cfg.blocks active).succs
      let (heap, phiblocks, processed) ←
        idfSuccLoop cfg live dt level succs.toList (heap, phiblocks, processed)
      let (wl, visited) := (← aget dt.nodes active).children.foldl (fun (wl, visited) child =>
          if visited.contains child then (wl, visited)
          else (wl.push child, bsInsert child visited)) (wl, visited)
      idfWorklist cfg live dt level fuel wl (heap, phiblocks, processed, visited)

/-- The `while !isempty(heap)` loop of `iterated_dominance_frontier`
(Compiler/src/ssair/slot2ssa.jl:240-284). -/
def idfHeapLoop (cfg : SCFG) (live : BlockLiveness) (dt : GenericDomTree) (wfuel : Nat) :
    Nat → Array (Int × Int) × Array Int × List Int × List Int → JM (Array Int)
  | 0, _ => outOfBudget
  | fuel + 1, (heap, phiblocks, processed, visited) =>
    if heap.isEmpty then pure phiblocks else do
      let ((node, level), heap) ← heappop heap
      let st ← idfWorklist cfg live dt level wfuel #[node] (heap, phiblocks, processed, visited)
      idfHeapLoop cfg live dt wfuel fuel st

/-- `iterated_dominance_frontier(cfg, liveness, domtree)`

Julia source: Compiler/src/ssair/slot2ssa.jl:229-285 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterated_dominance_frontier(cfg::CFG, liveness::BlockLiveness, domtree::DomTree)
    defs = liveness.def_bbs
    heap = Tuple{Int, Int}[(defs[i], domtree.nodes[defs[i]].level) for i in 1:length(defs)]
    heap_order = By(x -> -x[2])
    heapify!(heap, heap_order)
    phiblocks = Int[]
    # This bitset makes sure we only add a phi node to a given block once.
    processed = BitSet()
    # This bitset implements the `key insight` mentioned above. In particular, it prevents
    # us from visiting a subtree that we have already visited before.
    visited = BitSet()
    while !isempty(heap)
        # We pop from the end of the array - i.e. the element with the highest level.
        node, level = heappop!(heap, heap_order)
        worklist = Int[]
        push!(worklist, node)
        while !isempty(worklist)
            active = pop!(worklist)
            succs = cfg.blocks[active].succs
            for succ in succs
                succ_level = domtree.nodes[succ].level
                succ_level > level && continue
                succ in processed && continue
                push!(processed, succ)
                if liveness.live_in_bbs !== nothing && !(succ in liveness.live_in_bbs)
                    continue
                end
                push!(phiblocks, succ)
                if !(succ in defs)
                    heappush!(heap, (succ, succ_level), heap_order)
                end
            end
            # Recurse down the current subtree
            for child in domtree.nodes[active].children
                child in visited && continue
                push!(visited, child)
                push!(worklist, child)
            end
        end
    end
    phiblocks
end
```
(The long comments inside the loop are left out.) Each block enters `phiblocks` and the heap at
most once after the initial defs, and each child enters a worklist at most once, so the
bounds below are enough. -/
def iteratedDominanceFrontier (cfg : SCFG) (live : BlockLiveness) (dt : GenericDomTree) :
    JM (Array Int) := do
  let defs := live.defBBs
  let heap ← defs.mapM fun d => do pure (d, (← aget dt.nodes d).level)
  let heap ← heapify heap
  let n := cfg.blocks.size + dt.nodes.size
  idfHeapLoop cfg live dt (defs.size + 2 * n + 2) (defs.size + n + 2) (heap, #[], [], [])

/-! ## Edge renaming for `domsort_ssa!` -/

/-- `rename_incoming_edge(old_edge, old_to, result_order, bb_rename)`

Julia source: Compiler/src/ssair/slot2ssa.jl:287-298 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rename_incoming_edge(old_edge::Int, old_to::Int, result_order::Vector{Int}, bb_rename::Vector{Int})
    old_edge == 0 && return 0
    new_edge_from = bb_rename[old_edge]
    new_edge_from < 0 && return new_edge_from
    if old_edge == old_to - 1
        # Could have been a crit edge break
        if new_edge_from < length(result_order) && result_order[new_edge_from + 1] == 0
            new_edge_from += 1
        end
    end
    new_edge_from
end
```
-/
def renameIncomingEdge (oldEdge oldTo : Int) (resultOrder bbRename : Array Int) : JM Int := do
  if oldEdge == 0 then return 0
  let n ← aget bbRename oldEdge
  if n < 0 then return n
  if oldEdge == oldTo - 1 then
    if n < resultOrder.size then
      if (← aget resultOrder (n + 1)) == 0 then return n + 1
  return n

/-- `rename_outgoing_edge(old_to, old_from, result_order, bb_rename)`

Julia source: Compiler/src/ssair/slot2ssa.jl:300-309 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rename_outgoing_edge(old_to::Int, old_from::Int, result_order::Vector{Int}, bb_rename::Vector{Int})
    new_edge_to = bb_rename[old_to]
    if old_from == old_to - 1
        # Could have been a crit edge break
        if bb_rename[old_from] < length(result_order) && result_order[bb_rename[old_from]+1] == 0
            new_edge_to = bb_rename[old_from] + 1
        end
    end
    new_edge_to
end
```
-/
def renameOutgoingEdge (oldTo oldFrom : Int) (resultOrder bbRename : Array Int) : JM Int := do
  let n ← aget bbRename oldTo
  if oldFrom == oldTo - 1 then
    let f ← aget bbRename oldFrom
    if f < resultOrder.size then
      if (← aget resultOrder (f + 1)) == 0 then return f + 1
  return n

/-- `rename_phinode_edges(node, bb, result_order, bb_rename)`

Julia source: Compiler/src/ssair/slot2ssa.jl:311-326 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rename_phinode_edges(node::PhiNode, bb::Int, result_order::Vector{Int}, bb_rename::Vector{Int})
    new_values = Any[]
    new_edges = Int32[]
    for (idx, edge) in pairs(node.edges)
        edge = Int(edge)
        (edge == 0 || bb_rename[edge] != -1) || continue
        new_edge_from = edge == 0 ? 0 : rename_incoming_edge(edge, bb, result_order, bb_rename)
        push!(new_edges, new_edge_from)
        if isassigned(node.values, idx)
            push!(new_values, node.values[idx])
        else
            resize!(new_values, length(new_values)+1)
        end
    end
    return PhiNode(new_edges, new_values)
end
```
An edge vector longer than the value vector reads an unassigned value past the end as a
`BoundsError` in `node.values[idx]`; `isassigned` is false there, so Julia grows
`new_values` instead. -/
def renamePhinodeEdges (edges : Array Int) (vals : Array (Option IRV)) (bb : Int)
    (resultOrder bbRename : Array Int) : JM IRV := do
  let mut ne : Array Int := #[]
  let mut nv : Array (Option IRV) := #[]
  for idx in irange 1 edges.size do
    let edge := edges[(idx - 1).toNat]!
    if edge != 0 then
      if (← aget bbRename edge) == -1 then continue
    let nf ← if edge == 0 then pure 0 else renameIncomingEdge edge bb resultOrder bbRename
    ne := ne.push nf
    nv := nv.push (match vals[(idx - 1).toNat]? with | some v => v | none => none)
  return .phi ne nv

/-! ## `domsort_ssa!` -/

/-- The scheduling loop of `domsort_ssa!` (Compiler/src/ssair/slot2ssa.jl:349-389). Returns
`result_order`, `bb_rename` and `nfixupstmts`. -/
def domsortSchedule (ir : SIR) (dt : GenericDomTree) :
    Nat → Int → Array Int → Array Int → Array Int → Nat → JM (Array Int × Array Int × Nat)
  | 0, _, _, _, _, _ => outOfBudget
  | fuel + 1, node, resultOrder, bbRename, worklist, nfix =>
    if node == -1 then pure (resultOrder, bbRename, nfix) else do
      let resultOrder := resultOrder.push node
      let bbRename ← aset bbRename node resultOrder.size
      let cs := (← aget dt.nodes node).children
      let terminator ← ir.stmtAt (← aget ir.cfg.blocks node).last
      let fallthrough := node + 1
      let (sched, worklist) := cs.reverse.foldl (fun (sched, wl) n =>
          if n == fallthrough then (n, wl) else (sched, wl.push n)) ((-1 : Int), worklist)
      let (sched, worklist) := if sched == -1 && !worklist.isEmpty then
          (worklist.back!, worklist.pop) else (sched, worklist)
      let (resultOrder, nfix) ← if sched != fallthrough &&
          !(match terminator with | .goto _ | .ret _ => true | _ => false) then do
          let resultOrder ← match terminator with
            | .gotoifnot .. => pure (resultOrder.push 0)
            | .enter .. => pure (resultOrder.push 0)
            | t => if t.isExpr "leave" then pure (resultOrder.push 0) else do
              if isTerminator t then throw "julia:AssertionError"
              pure resultOrder
          pure (resultOrder, nfix + 1)
        else pure (resultOrder, nfix)
      domsortSchedule ir dt fuel sched resultOrder bbRename worklist nfix

/-- The instruction stream being built by `domsort_ssa!`, with `none` for an unassigned
`:stmt`. -/
abbrev Stream := Array (Option IRV)

def streamGet (r : Stream) (i : Int) : JM IRV := do
  match ← aget r i with
  | some s => pure s
  | none => throw "julia:UndefRefError"

/-- The `for (new_bb, bb) in pairs(result_order)` loop of `domsort_ssa!`
(Compiler/src/ssair/slot2ssa.jl:406-469), one block. -/
def domsortBlock (ir : SIR) (resultOrder bbRename : Array Int)
    (st : Stream × Array Int × Array SBlock × Int) (newBB bb : Int) :
    JM (Stream × Array Int × Array SBlock × Int) := do
  let (result, instRename, newBBs, off) := st
  if bb == 0 then
    let nidx := off + 1
    let stmt ← streamGet result nidx
    let label ← match stmt with
      | .goto l => pure l
      | _ => throw "julia:AssertionError"
    let newBBs ← aset newBBs newBB ⟨nidx, nidx, #[newBB - 1], #[label]⟩
    return (result, instRename, newBBs, off + 1)
  let ob ← aget ir.cfg.blocks bb
  let len := ob.last - ob.first + 1
  let rfirst := off + 1
  let mut rlast := off + len
  let mut result := result
  let mut instRename := instRename
  for (nidx, idx) in (irange rfirst rlast).zip (irange ob.first ob.last) do
    instRename ← aset instRename idx nidx
    if (← aget result nidx).isSome then throw "julia:AssertionError"
    let stmt ← aget ir.stmts idx
    let stmt ← match stmt with
      | .phi e v => renamePhinodeEdges e v bb resultOrder bbRename
      | s => pure s
    result ← aset result nidx (some stmt)
  let terminator ← streamGet result rlast
  match terminator with
  | .goto l =>
    if (← aget bbRename l) == newBB + 1 then result ← aset result rlast (some .nothing)
    else result ← aset result rlast (some (.goto (← aget bbRename l)))
  | .gotoifnot .. | .enter .. | .expr "leave" _ =>
    if (← aget bbRename (bb + 1)) != newBB + 1 then
      unless (← aget resultOrder (newBB + 1)) == 0 do throw "julia:AssertionError"
      result ← aset result (rlast + 1) (some (.goto (← aget bbRename (bb + 1))))
    match terminator with
    | .gotoifnot c d => result ← aset result rlast (some (.gotoifnot c (← aget bbRename d)))
    | .enter cd s =>
      let ncd ← if cd == 0 then pure 0 else aget bbRename cd
      result ← aset result rlast (some (.enter ncd s))
    | _ => pure ()
  | .ret _ => pure ()
  | _ =>
    if (← aget bbRename (bb + 1)) != newBB + 1 then
      result ← aset result (rlast + 1) (some (.goto (← aget bbRename (bb + 1))))
      rlast := rlast + 1
  let off := off + (rlast - rfirst + 1)
  let mut newPreds : Array Int := #[]
  for i in ob.preds do
    let e ← renameIncomingEdge i bb resultOrder bbRename
    if e != -1 then newPreds := newPreds.push e
  let newSuccs ← ob.succs.mapM fun i => renameOutgoingEdge i bb resultOrder bbRename
  let newBBs ← aset newBBs newBB ⟨rfirst, rlast, newPreds, newSuccs⟩
  return (result, instRename, newBBs, off)

/-- `domsort_ssa!(ir, domtree)`

Julia source: Compiler/src/ssair/slot2ssa.jl:335-490 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function domsort_ssa!(ir::IRCode, domtree::DomTree)
    # Mapping from new → old BB index
    # An "old" index of 0 means that this was a BB inserted as part of a fixup (see below)
    result_order = Int[]

    # Mapping from old → new BB index
    bb_rename = fill(-1, length(ir.cfg.blocks))

    # The number of GotoNodes we need to insert to preserve control-flow after sorting
    nfixupstmts = 0

    # node queued up for scheduling (-1 === nothing)
    node_to_schedule = 1
    worklist = Int[]
    while node_to_schedule !== -1
        # First assign a new BB index to `node_to_schedule`
        push!(result_order, node_to_schedule)
        bb_rename[node_to_schedule] = length(result_order)
        cs = domtree.nodes[node_to_schedule].children
        terminator = ir[SSAValue(last(ir.cfg.blocks[node_to_schedule].stmts))][:stmt]
        fallthrough = node_to_schedule + 1
        node_to_schedule = -1

        # Adding the nodes in reverse sorted order attempts to retain
        # the original source order of the nodes as much as possible.
        # This is not required for correctness, but is easier on the humans
        for node in Iterators.Reverse(cs)
            if node == fallthrough
                # Schedule the fall through node first,
                # so we can retain the fall through
                node_to_schedule = node
            else
                push!(worklist, node)
            end
        end
        if node_to_schedule == -1 && !isempty(worklist)
            node_to_schedule = pop!(worklist)
        end
        # If a fallthrough successor is no longer the fallthrough after sorting, we need to
        # add a GotoNode (and either extend or split the basic block as necessary)
        if node_to_schedule != fallthrough && !isa(terminator, Union{GotoNode, ReturnNode})
            if isa(terminator, GotoIfNot)
                # Need to break the critical edge
                push!(result_order, 0)
            elseif isa(terminator, EnterNode) || isexpr(terminator, :leave)
                # Cannot extend the BasicBlock with a goto, have to split it
                push!(result_order, 0)
            else
                # No need for a new block, just extend
                @assert !isterminator(terminator)
            end
            # Reserve space for the fixup goto
            nfixupstmts += 1
        end
    end
    new_bbs = Vector{BasicBlock}(undef, length(result_order))
    nstmts = 0
    for i in result_order
        if i !== 0
            nstmts += length(ir.cfg.blocks[i].stmts)
        end
    end
    result = InstructionStream(nstmts + nfixupstmts)
    inst_rename = Vector{SSAValue}(undef, length(ir.stmts) + length(ir.new_nodes))
    @inbounds for i = 1:length(ir.stmts)
        inst_rename[i] = SSAValue(-1)
    end
    @inbounds for i = 1:length(ir.new_nodes)
        inst_rename[i + length(ir.stmts)] = SSAValue(i + length(result))
    end
    bb_start_off = 0
    for (new_bb, bb) in pairs(result_order)
        if bb == 0
            nidx = bb_start_off + 1
            stmt = result[nidx][:stmt]
            @assert isa(stmt, GotoNode)
            # N.B.: The .label has already been renamed when it was created.
            new_bbs[new_bb] = BasicBlock(nidx:nidx, [new_bb - 1], [stmt.label])
            bb_start_off += 1
            continue
        end
        old_inst_range = ir.cfg.blocks[bb].stmts
        inst_range = (bb_start_off+1):(bb_start_off+length(old_inst_range))
        for (nidx, idx) in zip(inst_range, old_inst_range)
            inst_rename[idx] = SSAValue(nidx)
            @assert !isassigned(result.stmt, nidx)
            node = result[nidx]
            node[] = ir.stmts[idx]
            stmt = node[:stmt]
            if isa(stmt, PhiNode)
                node[:stmt] = rename_phinode_edges(stmt, bb, result_order, bb_rename)
            end
        end
        # Now fix up the terminator
        terminator = result[inst_range[end]][:stmt]
        if isa(terminator, GotoNode)
            # Convert to implicit fall through
            if bb_rename[terminator.label] == new_bb + 1
                result[inst_range[end]][:stmt] = nothing
            else
                result[inst_range[end]][:stmt] = GotoNode(bb_rename[terminator.label])
            end
        elseif isa(terminator, GotoIfNot) || isa(terminator, EnterNode) || isexpr(terminator, :leave)
            # Check if we need to break the critical edge or split the block
            if bb_rename[bb + 1] != new_bb + 1
                @assert result_order[new_bb + 1] == 0
                # Add an explicit goto node in the next basic block (we accounted for this above)
                nidx = inst_range[end] + 1
                node = result[nidx]
                node[:stmt], node[:type], node[:line] = GotoNode(bb_rename[bb + 1]), Any, NoLineUpdate
            end
            if isa(terminator, GotoIfNot)
                result[inst_range[end]][:stmt] = GotoIfNot(terminator.cond, bb_rename[terminator.dest])
            elseif isa(terminator, EnterNode)
                result[inst_range[end]][:stmt] = EnterNode(terminator, terminator.catch_dest == 0 ? 0 : bb_rename[terminator.catch_dest])
            else
                @assert isexpr(terminator, :leave)
            end
        elseif !isa(terminator, ReturnNode)
            if bb_rename[bb + 1] != new_bb + 1
                # Add an explicit goto node
                nidx = inst_range[end] + 1
                node = result[nidx]
                node[:stmt], node[:type], node[:line] = GotoNode(bb_rename[bb + 1]), Any, NoLineUpdate
                inst_range = first(inst_range):(last(inst_range) + 1)
            end
        end
        bb_start_off += length(inst_range)
        local new_preds, new_succs
        let bb = bb, bb_rename = bb_rename, result_order = result_order
            new_preds = Int[bb for bb in (rename_incoming_edge(i, bb, result_order, bb_rename) for i in ir.cfg.blocks[bb].preds) if bb != -1]
            new_succs = Int[              rename_outgoing_edge(i, bb, result_order, bb_rename) for i in ir.cfg.blocks[bb].succs]
        end
        new_bbs[new_bb] = BasicBlock(inst_range, new_preds, new_succs)
    end
    for i in 1:length(result)
        result[i][:stmt] = renumber_ssa!(result[i][:stmt], inst_rename, true)
    end
    cfg = CFG(new_bbs, Int[first(bb.stmts) for bb in new_bbs[2:end]])
    new_new_nodes = NewNodeStream(length(ir.new_nodes))
    for i = 1:length(ir.new_nodes)
        new_info = ir.new_nodes.info[i]
        new_new_info = NewNodeInfo(inst_rename[new_info.pos].id, new_info.attach_after)
        new_new_nodes.info[i] = new_new_info
        new_node = new_new_nodes.stmts[i]
        new_node[] = ir.new_nodes.stmts[i]
        new_node_inst = new_node[:stmt]
        if isa(new_node_inst, PhiNode)
            new_node_inst = rename_phinode_edges(new_node_inst, block_for_inst(ir.cfg, new_info.pos), result_order, bb_rename)
        end
        new_node[:stmt] = renumber_ssa!(new_node_inst, inst_rename, true)
    end
    ir.debuginfo.codelocs = result.line
    new_ir = IRCode(ir, result, cfg, new_new_nodes)
    return new_ir
end
```
The scheduling loop schedules each block at most once (the domtree's children lists form a
tree), so `length(blocks) + 2` iterations are enough. The `@inbounds` loops write in bounds.
A block range `first:last` with `last < first` (an empty block, which `compute_basic_blocks`
never makes) is not modelled: `inst_range[end]` reads `last` anyway. -/
def domsortSsa! (ir : SIR) (dt : GenericDomTree) : JM SIR := do
  let nb := ir.cfg.blocks.size
  let (resultOrder, bbRename, nfix) ←
    domsortSchedule ir dt (nb + 2) 1 #[] (Array.replicate nb (-1)) #[] 0
  let nstmts ← resultOrder.foldlM (fun n i => do
    if i != 0 then let b ← aget ir.cfg.blocks i; pure (n + (b.last - b.first + 1)) else pure n)
    (0 : Int)
  let rlen := (nstmts + nfix).toNat
  let result : Stream := Array.replicate rlen none
  let instRename : Array Int := Array.replicate ir.stmts.size (-1) ++
    (Array.range ir.newNodes.size).map fun (i : Nat) => (i : Int) + 1 + rlen
  let newBBs : Array SBlock := Array.replicate resultOrder.size default
  let (result, instRename, newBBs, _) ← (irange 1 resultOrder.size).foldlM
    (fun st newBB => do domsortBlock ir resultOrder bbRename st newBB (← aget resultOrder newBB))
    (result, instRename, newBBs, (0 : Int))
  let mut out : Array IRV := #[]
  for i in irange 1 result.size do
    out := out.push (← renumberSsa! (← streamGet result i) instRename)
  let cfg : SCFG := ⟨newBBs, (newBBs.extract 1 newBBs.size).map (·.first)⟩
  let newNodes ← ir.newNodes.mapM fun nn => do
    let pos ← aget instRename nn.pos
    let inst ← match nn.stmt with
      | .phi e v => do renamePhinodeEdges e v (← blockForInst ir.cfg nn.pos) resultOrder bbRename
      | s => pure s
    pure ({ pos, attachAfter := nn.attachAfter, stmt := ← renumberSsa! inst instRename } : NewNode)
  pure { stmts := out, nothrow := Array.replicate out.size false, cfg, newNodes }

/-! ## `construct_ssa!` -/

/-- What `construct_ssa!` reads about one slot at the entry of one block from
`sv.bb_states[block].vartable[slot]` and the lattice. -/
structure VarIn where
  /-- `vt.typ === Union{}` -/
  bottom : Bool
  /-- `vt.undef` -/
  undef : Bool
  /-- `vt.typ`, printed: the `typ` of the `PiNode` -/
  typ : String
  /-- `!⊑(𝕃ₒ, sv.slottypes[slot], vt.typ)` -/
  needPi : Bool
  deriving Inhabited

/-- The inputs of `construct_ssa!` beyond `ir`: `sv.bb_states` (`none` for `nothing`), the
slot names, the statement handlers (`compute_trycatch` and `gethandler`: the `:enter` index of
the innermost handler of each statement, or 0), and the `sptypes` the static-parameter fixup
reads. -/
structure SSAInputs where
  nargs : Int
  slotnames : Array String
  bbStates : Array (Option (Array VarIn))
  handler : Array Int
  sp : SpInfo
  deriving Inhabited

/-- `struct TryCatchRegion` (Compiler/src/ssair/slot2ssa.jl:532-535). -/
structure TryCatchRegion where
  enterBlock : Int
  leaveBlock : Int
  deriving Inhabited

/-- `struct NewSlotPhi{Phi}` (Compiler/src/ssair/slot2ssa.jl:536-541), with the phi nodes
given by their new-node index (the `NewSSAValue` id): `ssaval` is the node, `undefNode` the
undef-tracking node if there is one. -/
structure NewSlotPhi where
  ssaval : Int
  undefSsaval : DefV
  undefNode : Option Int
  deriving Inhabited

/-- `struct NewPhiCNode2` (Compiler/src/ssair/slot2ssa.jl:545-548). -/
structure NewPhiCNode2 where
  slot : Int
  insert : NewSlotPhi
  deriving Inhabited

/-- The state of `construct_ssa!` that its loops thread. -/
structure SSAState where
  ir : SIR
  code : Array IRV
  phiSlots : Array (Array Int)
  liveSlots : Array (Array Int)
  newPhiNodes : Array (Array NewSlotPhi)
  /-- `new_phic_nodes`, an `IdDict` keyed by block, as an association list in key order of
  first insertion -/
  newPhicNodes : List (Int × Array NewPhiCNode2)
  deriving Inhabited

def phicGet (m : List (Int × Array NewPhiCNode2)) (k : Int) : JM (Array NewPhiCNode2) :=
  match m.lookup k with
  | some v => pure v
  | none => throw "julia:KeyError"

def phicSet (m : List (Int × Array NewPhiCNode2)) (k : Int) (v : Array NewPhiCNode2) :
    List (Int × Array NewPhiCNode2) :=
  if m.any (·.1 == k) then m.map fun (k', v') => if k' == k then (k', v) else (k', v')
  else m ++ [(k, v)]

/-- `bbstate.vartable[idx]` for a block whose state is not `nothing`. -/
def varIn (I : SSAInputs) (block slot : Int) : JM VarIn := do
  match ← aget I.bbStates block with
  | some vt => aget vt slot
  | none => throw "julia:AssertionError"

/-- The undef part of a new phi or `PhiC` (Compiler/src/ssair/slot2ssa.jl:619-628 and
646-655): `false` for a `Union{}` slot, `true` for a slot that is surely defined, otherwise a
second node of kind `mk` at `pos`. -/
def newUndefNode (ir : SIR) (vt : VarIn) (pos : Int) (mk : IRV) : SIR × DefV × Option Int :=
  if vt.bottom then (ir, .bool false, none)
  else if !vt.undef then (ir, .bool true, none)
  else
    let (ir, k) := ir.insert pos mk
    (ir, .nss k, some k)

/-- The `for li in live.live_in_bbs` loop of `construct_ssa!` for one slot
(Compiler/src/ssair/slot2ssa.jl:602-636). Returns the state and the updated `live.def_bbs`. -/
def phicLoop (I : SSAInputs) (cer : Array TryCatchRegion) (idx : Int) :
    List Int → SSAState → Array Int → JM (SSAState × Array Int)
  | [], st, defs => pure (st, defs)
  | li :: rest, st, defs => do
    let st := { st with liveSlots := ← aset st.liveSlots li ((← aget st.liveSlots li).push idx) }
    match cer.findIdx? (·.leaveBlock == li) with
    | none => phicLoop I cer idx rest st defs
    | some _ =>
      match ← aget I.bbStates li with
      | none => phicLoop I cer idx rest st defs
      | some _ => do
        let insertpoint ← firstInsertForBB st.code st.ir.cfg li
        let vt ← varIn I li idx
        let (ir, phicSsa) := st.ir.insert insertpoint (.phic #[])
        let (ir, undefSsaval, undefNode) := newUndefNode ir vt insertpoint (.phic #[])
        let lst ← phicGet st.newPhicNodes li
        let lst := lst.push ⟨idx, ⟨phicSsa, undefSsaval, undefNode⟩⟩
        let st := { st with ir := ir, newPhicNodes := phicSet st.newPhicNodes li lst }
        let defs := if defs.contains li then defs else defs.push li
        phicLoop I cer idx rest st defs

/-- The `for block in phiblocks` loop of `construct_ssa!` for one slot
(Compiler/src/ssair/slot2ssa.jl:638-657). -/
def phiInsertLoop (I : SSAInputs) (idx : Int) : List Int → SSAState → JM SSAState
  | [], st => pure st
  | block :: rest, st => do
    let st := { st with phiSlots := ← aset st.phiSlots block ((← aget st.phiSlots block).push idx) }
    let vt ← varIn I block idx
    let pos ← firstInsertForBB st.code st.ir.cfg block
    let (ir, ssaval) := st.ir.insert pos (.phi #[] #[])
    let pos ← firstInsertForBB st.code ir.cfg block
    let (ir, undefSsaval, undefNode) := newUndefNode ir vt pos (.phi #[] #[])
    let lst := (← aget st.newPhiNodes block).push ⟨ssaval, undefSsaval, undefNode⟩
    let st := { st with ir := ir, newPhiNodes := ← aset st.newPhiNodes block lst }
    phiInsertLoop I idx rest st

/-- The `@zone "CC: IDF"` loop of `construct_ssa!` (Compiler/src/ssair/slot2ssa.jl:575-658)
over the slots. The disabled `if false` branch (lines 578-599) is left out. -/
def idfSlotsLoop (I : SSAInputs) (dt : GenericDomTree) (defuses : Array SlotInfo)
    (cer : Array TryCatchRegion) : List Int → SSAState → JM SSAState
  | [], st => pure st
  | idx :: rest, st => do
    let slot ← aget defuses idx
    if slot.uses.isEmpty then return ← idfSlotsLoop I dt defuses cer rest st
    let live ← computeLiveIns st.ir.cfg slot.defs slot.uses
    let lis := live.liveInBBs.getD #[]
    let (st, defs) ← phicLoop I cer idx lis.toList st live.defBBs
    let live := { live with defBBs := defs }
    let phiblocks ← iteratedDominanceFrontier st.ir.cfg live dt
    let st ← phiInsertLoop I idx phiblocks.toList st
    idfSlotsLoop I dt defuses cer rest st

/-- The existing-phi renaming at the top of the walk (Compiler/src/ssair/slot2ssa.jl:677-690):
for the first edge from `pred`, rename its value if it is assigned. -/
def renameExistingPhi (C : FixCtx) (cfg : SCFG) (pred : Int) (incoming : Renames)
    (ir : SIR) (edges : Array Int) (vals : Array (Option IRV)) :
    JM (SIR × Array (Option IRV)) := do
  for ei in irange 1 edges.size do
    let edge := edges[(ei - 1).toNat]!
    let fromBB ← if edge == 0 then pure 0 else blockForInst cfg edge
    if fromBB != pred then continue
    match vals[(ei - 1).toNat]? with
    | some (some v) =>
      let (ir, v) ← renameUses! C ir edge v incoming
      return (ir, ← aset vals ei (some v))
    | _ => return (ir, vals)
  return (ir, vals)

/-- The upsilons for a store inside `try` regions (Compiler/src/ssair/slot2ssa.jl:788-805):
walk the handler chain from `idx` outwards and add an upsilon to each `PhiC` of slot `id`. -/
def storeUpsilons (I : SSAInputs) (idx id : Int) (thisval : IRV) (thisdef : Bool) :
    Nat → Int → SSAState → JM SSAState
  | 0, _, _ => outOfBudget
  | fuel + 1, enterIdx, st => do
    let h ← aget I.handler enterIdx
    if h == 0 then return st
    let enterIdx := h
    let catchDest ← match ← aget st.code enterIdx with
      | .enter cd _ => pure cd
      | _ => throw "julia:TypeError"
    let leaveBlock ← blockForInst st.ir.cfg catchDest
    let lst ← phicGet st.newPhicNodes leaveBlock
    match lst.findIdx? (·.slot == id) with
    | none => storeUpsilons I idx id thisval thisdef fuel enterIdx st
    | some ci =>
      let node : IRV := if thisdef then .upsilon (some thisval) else .upsilon none
      let ins := lst[ci]!.insert
      let (ir, k) := st.ir.insert idx node true
      let ir ← ir.setNewStmt ins.ssaval fun s => match s with
        | .phic vs => pure (.phic (vs.push (some (.newssa k))))
        | _ => throw "julia:TypeError"
      let ir ← match ins.undefNode with
        | none => pure ir
        | some u => do
          let (ir, k2) := ir.insert idx (.upsilon (some (IRV.boolLit thisdef))) true
          ir.setNewStmt u fun s => match s with
            | .phic vs => pure (.phic (vs.push (some (.newssa k2))))
            | _ => throw "julia:TypeError"
      storeUpsilons I idx id thisval thisdef fuel enterIdx { st with ir }

/-- The statement loop of the renaming walk for one block
(Compiler/src/ssair/slot2ssa.jl:754-809). Returns the state, `incoming_vals` and
`has_pinode`. -/
def renameStmts (C : FixCtx) (I : SSAInputs) (blockLast : Int) :
    List Int → SSAState × Renames × Array Bool → JM (SSAState × Renames × Array Bool)
  | [], acc => pure acc
  | idx :: rest, (st, incoming, hasPi) => do
    let stmt ← aget st.code idx
    let isPhi : Bool := match stmt with
      | .phi .. => true
      | .expr "=" args => match (args[1]? : Option IRV) with
        | some (.phi ..) => true
        | _ => false
      | _ => false
    if isPhi then return ← renameStmts C I blockLast rest (st, incoming, hasPi)
    if let .newvar s := stmt then
      let incoming ← aset incoming s (.undefTok, .bool false)
      let hasPi ← aset hasPi s false
      let code ← aset st.code idx .nothing
      return ← renameStmts C I blockLast rest ({ st with code }, incoming, hasPi)
    let (ir, stmt') ← renameUses! C st.ir idx stmt incoming
    let stmt' := match stmt', stmt with
      | .nothing, .ret _ | .nothing, .gotoifnot .. => if idx == blockLast then .ret none else .nothing
      | s, _ => s
    let code ← aset st.code idx stmt'
    let st := { st with ir, code }
    match stmt' with
    | .expr "=" args =>
      match ← aget args 1 with
      | .slot id => do
        let v ← aget args 2
        let (st, thisval, thisdef) ← match v with
          | .undefTok => do pure ({ st with code := ← aset st.code idx .nothing }, IRV.undefTok, false)
          | _ => do
            typForValCheck 8 v
            let (code, sv) ← makeSsa! st.code idx
            pure ({ st with code }, sv, true)
        let incoming ← aset incoming id (thisval, .bool thisdef)
        let hasPi ← aset hasPi id false
        let st ← storeUpsilons I idx id thisval thisdef (I.handler.size + 1) idx st
        renameStmts C I blockLast rest (st, incoming, hasPi)
      | _ => renameStmts C I blockLast rest (st, incoming, hasPi)
    | _ => renameStmts C I blockLast rest (st, incoming, hasPi)

/-- One visit of the renaming walk (Compiler/src/ssair/slot2ssa.jl:671-820): the block `item`
reached from `pred`. Returns the state, the visited set (sorted) and the successor entries
to push. -/
def renameVisit (C : FixCtx) (I : SSAInputs) (cer : Array TryCatchRegion)
    (st0 : SSAState) (visited : List Int) (item pred : Int) (incoming : Renames) :
    JM (SSAState × List Int × Array (Int × Int × Renames)) := do
  if (← aget I.bbStates item).isNone then return (st0, visited, #[])
  let cfg := st0.ir.cfg
  let blk ← aget cfg.blocks item
  -- Rename existing phi nodes first, because their uses occur on the edge
  let mut st := st0
  for idx in irange blk.first blk.last do
    let stmt ← aget st.code idx
    match stmt with
    | .phi e v =>
      let (ir, v) ← renameExistingPhi C cfg pred incoming st.ir e v
      st := { st with ir, code := ← aset st.code idx (.phi e v) }
    | .expr "=" args =>
      match ← aget args 2 with
      | .phi e v =>
        let (ir, v) ← renameExistingPhi C cfg pred incoming st.ir e v
        st := { st with ir, code := ← aset st.code idx (.expr "=" (args.set! 1 (.phi e v))) }
      | _ => pure ()
    | _ => pure ()
  -- Insert phi nodes if necessary
  let mut incoming := incoming
  let pslots ← aget st.phiSlots item
  let pnodes ← aget st.newPhiNodes item
  for i in irange 1 pslots.size do
    let slot := pslots[(i - 1).toNat]!
    let np ← aget pnodes i
    let (ival, idef) ← aget incoming slot
    let ir ← st.ir.setNewStmt np.ssaval fun s => match s with
      | .phi e v => pure (.phi (e.push pred) (v.push (match ival with
          | .undefTok => none
          | v => some v)))
      | _ => throw "julia:TypeError"
    let ir ← match np.undefNode with
      | none => pure ir
      | some u => ir.setNewStmt u fun s => match s with
        | .phi e v => pure (.phi (e.push pred) (v.push (some idef.toIRV)))
        | _ => throw "julia:TypeError"
    st := { st with ir }
    incoming ← aset incoming slot (.newssa np.ssaval, np.undefSsaval)
  if visited.contains item then return (st, visited, #[])
  -- Record phi_C nodes if necessary
  if let some lst := st.newPhicNodes.lookup item then
    for p in lst do
      incoming ← aset incoming p.slot (.newssa p.insert.ssaval, p.insert.undefSsaval)
  -- Record Pi nodes if necessary
  let mut hasPi : Array Bool := Array.replicate incoming.size false
  for slot in ← aget st.liveSlots item do
    let (ival, idef) ← aget incoming slot
    if let .undefTok := ival then continue
    let vt ← varIn I item slot
    if vt.needPi then
      let pos ← firstInsertForBB st.code cfg item
      let (ir, k) := st.ir.insert pos (.pinode ival vt.typ)
      st := { st with ir }
      incoming ← aset incoming slot (.newssa k, idef)
      hasPi ← aset hasPi slot true
  -- Record initial upsilon nodes if necessary
  if let some ei := cer.findIdx? (·.enterBlock == item) then
    for p in ← phicGet st.newPhicNodes cer[ei]!.leaveBlock do
      let (ival, idef) ← aget incoming p.slot
      let node : IRV := match ival with
        | .undefTok => .upsilon none
        | v => .upsilon (some v)
      match ival with
      | .undefTok => pure ()
      | v => typForValCheck 8 v
      let pos ← firstInsertForBB st.code cfg item
      let (ir, k) := st.ir.insert pos node
      let ir ← ir.setNewStmt p.insert.ssaval fun s => match s with
        | .phic vs => pure (.phic (vs.push (some (.newssa k))))
        | _ => throw "julia:TypeError"
      let ir ← match p.insert.undefNode with
        | none => pure ir
        | some u => do
          let (ir, k2) := ir.insert pos (.upsilon (some idef.toIRV))
          ir.setNewStmt u fun s => match s with
            | .phic vs => pure (.phic (vs.push (some (.newssa k2))))
            | _ => throw "julia:TypeError"
      st := { st with ir }
  let visited := bsInsert item visited
  let (st', incoming', hasPi') ←
    renameStmts C I blk.last (irange blk.first blk.last) (st, incoming, hasPi)
  st := st'
  incoming := incoming'
  hasPi := hasPi'
  -- Unwrap any PiNodes before continuing
  for i in irange 1 incoming.size do
    if ← aget hasPi i then
      let (ival, idef) ← aget incoming i
      let k ← match ival with
        | .newssa k => pure k
        | _ => throw "julia:TypeError"
      let v ← match ← st.ir.stmtAt (k + st.ir.stmts.size) with
        | .pinode v _ => pure v
        | _ => throw "julia:ErrorException"
      incoming ← aset incoming i (v, idef)
  let blk ← aget st.ir.cfg.blocks item
  return (st, visited, blk.succs.map fun s => (s, item, incoming))

/-- The `@zone "CC: SSA_RENAME"` worklist loop of `construct_ssa!`
(Compiler/src/ssair/slot2ssa.jl:670-821). A block is renamed once; afterwards each visit only
adds its phi operands, so the visits are bounded by one per CFG edge plus one. -/
def renameLoop (C : FixCtx) (I : SSAInputs) (cer : Array TryCatchRegion) :
    Nat → SSAState → List Int → Array (Int × Int × Renames) → JM (SSAState × List Int)
  | 0, _, _, _ => outOfBudget
  | fuel + 1, st, visited, wl =>
    match wl.back? with
    | none => pure (st, visited)
    | some (item, pred, incoming) => do
      let (st, visited, push) ← renameVisit C I cer st visited item pred incoming
      renameLoop C I cer fuel st visited (wl.pop ++ push)

/-- The conversion of one statement to `IRCode` form (Compiler/src/ssair/slot2ssa.jl:838-867).
Returns the new statement and the `ssavalmap` entry (`none` for `SSAValue(-1)`). -/
def convertStmt (cfg : SCFG) (bb idx : Int) (stmt : IRV) : JM (IRV × Option Int) := do
  match stmt with
  | .goto l => pure (.goto (← blockForInst cfg l), none)
  | .gotoifnot c d =>
    let nd ← blockForInst cfg d
    if nd == bb + 1 then
      pure (.expr "call" #[.glob "Core.typeassert", c, .glob "Core.Bool"], none)
    else pure (.gotoifnot c nd, none)
  | .enter cd s =>
    let ebb ← if cd == 0 then pure 0 else blockForInst cfg cd
    pure (.enter ebb s, some idx)
  | .ret _ | .newvar _ => pure (stmt, none)
  | .expr h _ =>
    if h == "leave" || h == "=" || h == "meta" then pure (stmt, none) else pure (stmt, some idx)
  | .phi edges vals =>
    let edges ← edges.mapM fun e => if e == 0 then pure 0 else blockForInst cfg e
    pure (.phi edges vals, some idx)
  | _ => pure (stmt, some idx)

/-- `iterate(::BBIdxIter)` (Compiler/src/ssair/ir.jl:2287-2295): the block of each statement
index in order. -/
def bbIdxIter (cfg : SCFG) (n : Nat) : JM (List (Int × Int)) := do
  let mut bb : Int := 1
  let mut out : Array (Int × Int) := #[]
  for idx in irange 1 n do
    let b ← aget cfg.blocks bb
    out := out.push (bb, idx)
    if idx == b.last then bb := bb + 1
  return out.toList

/-- `construct_ssa!(ci, ir, sv, domtree, defuses, 𝕃ₒ)` up to the `domsort_ssa!` call, with
`ci.code === ir.stmts.stmt`: the IR it hands to `domsort_ssa!`.

Julia source: Compiler/src/ssair/slot2ssa.jl:550-882 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
(the body is quoted in parts in the docstrings of the helpers above; the setup is)
```julia
    code = ir.stmts.stmt
    cfg = ir.cfg
    catch_entry_blocks = TryCatchRegion[]
    for idx in 1:length(code)
        stmt = code[idx]
        if isa(stmt, EnterNode)
            push!(catch_entry_blocks, TryCatchRegion(
                block_for_inst(cfg, idx),
                block_for_inst(cfg, stmt.catch_dest)))
        end
    end

    # Record the correct exception handler for all critical sections
    handler_info = compute_trycatch(code)

    phi_slots = Vector{Int}[Int[] for _ = 1:length(ir.cfg.blocks)]
    live_slots = Vector{Int}[Int[] for _ = 1:length(ir.cfg.blocks)]
    new_phi_nodes = Vector{NewPhiNode2}[NewPhiNode2[] for _ = 1:length(cfg.blocks)]
    new_phic_nodes = IdDict{Int, Vector{NewPhiCNode2}}()
    for (; leave_block) in catch_entry_blocks
        new_phic_nodes[leave_block] = NewPhiCNode2[]
    end
```
and after the IDF loop (lines 659-668)
```julia
    # Perform SSA renaming
    initial_incoming_vals = Pair{Any, Any}[
        if 0 in defuses[x].defs
            Pair{Any, Any}(Argument(x), true)
        else
            Pair{Any, Any}(UNDEF_TOKEN, false)
        end for x in 1:length(ci.slotflags)
    ]
    worklist = Tuple{Int, Int, Vector{Pair{Any, Any}}}[(1, 0, initial_incoming_vals)]
    visited = BitSet()
```
then the renaming walk (`renameLoop`), the deletion of unreachable code (lines 822-831)
```julia
    for bb in setdiff(BitSet(1:length(cfg.blocks)), visited)
        for idx in cfg.blocks[bb].stmts
            if isa(code[idx], Union{GotoNode, GotoIfNot, ReturnNode})
                code[idx] = ReturnNode()
            else
                code[idx] = nothing
            end
        end
    end
```
the conversion (lines 832-867, `convertStmt` per statement), the renumbering
```julia
    for i in 1:nstmts
        local node = ir.stmts[i]
        node[:stmt] = new_to_regular(renumber_ssa!(new_code[i], ssavalmap), nstmts)
        node[:type] = ssavaluetypes[i]
    end
    for i = 1:length(new_nodes)
        local node = new_nodes.stmts[i]
        node[:stmt] = new_to_regular(renumber_ssa!(node[:stmt], ssavalmap), nstmts)
    end
    @zone "CC: DOMSORT" ir = domsort_ssa!(ir, domtree)
    return ir
```
with `ssavalmap = fill(SSAValue(-1), length(ssavaluetypes) + 1)` and
`length(ssavaluetypes) == length(code)`. The `@assert isempty(ir.stmts.type)` holds for the
`ir` that `convert_to_ircode!` makes. `defuses` is `scan_slot_def_use(nargs, ci, code)`, as
`slot2reg` (Compiler/src/optimize.jl:1773-1782) passes it, and `domtree` is
`construct_domtree(ir)`. -/
def constructSsaBody! (I : SSAInputs) (ir0 : SIR) (dt : GenericDomTree) (defuses : Array SlotInfo) :
    JM SIR := do
  let code := ir0.stmts
  let cfg := ir0.cfg
  let C : FixCtx := ⟨I.slotnames, I.sp⟩
  let nslots := I.slotnames.size
  let mut cer : Array TryCatchRegion := #[]
  for idx in irange 1 code.size do
    if let .enter cd _ := (← aget code idx) then
      cer := cer.push ⟨← blockForInst cfg idx, ← blockForInst cfg cd⟩
  let nb := cfg.blocks.size
  let mut phic : List (Int × Array NewPhiCNode2) := []
  for r in cer do
    phic := phicSet phic r.leaveBlock #[]
  let st : SSAState := ⟨ir0, code, Array.replicate nb #[], Array.replicate nb #[],
    Array.replicate nb #[], phic⟩
  let st ← idfSlotsLoop I dt defuses cer (irange 1 defuses.size) st
  let init : Renames := (Array.range nslots).map fun (i : Nat) =>
    if ((defuses[i]? : Option SlotInfo).map (·.defs.contains 0)).getD false then
      (.arg ((i : Int) + 1), .bool true)
    else (.undefTok, .bool false)
  let fuel := cfg.blocks.foldl (fun n b => n + b.succs.size) 0 + 2
  let (st, visited) ← renameLoop C I cer fuel st [] #[(1, 0, init)]
  -- Delete any instruction in unreachable blocks (except for terminators)
  let mut code := st.code
  for bb in irange 1 nb do
    if visited.contains bb then continue
    let b ← aget cfg.blocks bb
    for idx in irange b.first b.last do
      match ← aget code idx with
      | .goto _ | .gotoifnot .. | .ret _ => code ← aset code idx (.ret none)
      | _ => code ← aset code idx .nothing
  -- Convert into IRCode form
  let ir := st.ir
  let nstmts := ir.stmts.size
  let mut ssavalmap : Array Int := Array.replicate (code.size + 1) (-1)
  let mut newCode : Array IRV := Array.replicate nstmts .nothing
  for (bb, idx) in ← bbIdxIter ir.cfg nstmts do
    let (s, m) ← convertStmt ir.cfg bb idx (← aget code idx)
    newCode ← aset newCode idx s
    if let some v := m then ssavalmap ← aset ssavalmap idx v
  let mut stmts : Array IRV := #[]
  for i in irange 1 nstmts do
    stmts := stmts.push (← newToRegular (← renumberSsa! (← aget newCode i) ssavalmap) nstmts)
  let newNodes ← ir.newNodes.mapM fun nn => do
    pure { nn with stmt := ← newToRegular (← renumberSsa! nn.stmt ssavalmap) nstmts }
  pure { ir with stmts, newNodes }

/-- `construct_ssa!(ci, ir, sv, domtree, defuses, 𝕃ₒ)`: the body above (everything before the
last line), then `ir = domsort_ssa!(ir, domtree)` (Compiler/src/ssair/slot2ssa.jl:880). -/
def constructSsa! (I : SSAInputs) (ir0 : SIR) (dt : GenericDomTree) (defuses : Array SlotInfo) :
    JM SIR := do
  domsortSsa! (← constructSsaBody! I ir0 dt defuses) dt

/-- `slot2reg`'s use of `construct_ssa!` (Compiler/src/optimize.jl:1773-1778): the domtree of
the CFG, the def/use scan, then `construct_ssa!`. -/
def slot2regSsa (I : SSAInputs) (ir : SIR) : JM SIR := do
  let dt ← constructDomtree ir.cfg.domBlocks
  let defuses ← scanSlotDefUse I.nargs I.slotnames.size ir.stmts
  constructSsa! I ir dt defuses

end JuliaLean.Compiler.ssair
