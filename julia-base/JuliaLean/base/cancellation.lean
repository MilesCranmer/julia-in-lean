import JuliaLean.Core

/-!
# Source model of `base/cancellation.jl`

Cancellation source/task/atomic operations are typed callbacks because their storage and wake
protocol are implemented by Julia's C runtime. `WaitEntryOps` callbacks preserve field atomicity,
slot layout, casts, and the source operation's memory order. Source branches, slot order, and loop
order remain explicit here. The two compiler-managed macro expansions remain visible as
untranslated blocks.
-/

namespace JuliaLean.base.cancellation

open JuliaLean

abbrev U8 := JInt .u8
abbrev U32 := JInt .u32
abbrev U64 := JInt .u64
abbrev I64 := JInt .i64

def i64 (n : Int) : I64 := JInt.wrap .i64 n

def u64 (n : Int) : U64 := JInt.wrap .u64 n

inductive CancelError where
  | argumentError (message : String)
  | concurrencyViolationError (message : String)
  | fieldError (typeName fieldName : String)
  | cancellationRequest (request : U8)
  | other (message : String)
  deriving Repr, DecidableEq

abbrev M (World : Type) (A : Type) := World → Option (Except (CancelError × World) (A × World))

instance (World : Type) : Monad (M World) where
  pure value := fun world => some (.ok (value, world))
  bind action next := fun world =>
    match action world with
    | none => none
    | some (.error error) => some (.error error)
    | some (.ok (value, nextWorld)) => next value nextWorld

instance (World : Type) : MonadExceptOf CancelError (M World) where
  throw error := fun world => some (.error (error, world))
  tryCatch action handler := fun world =>
    match action world with
    | none => none
    | some (.ok result) => some (.ok result)
    | some (.error (error, nextWorld)) => handler error nextWorld

def liftExceptM {World A : Type} [Monad (M World)] [MonadExceptOf CancelError (M World)]
    (result : Except CancelError A) : M World A :=
  match result with
  | .ok value => pure value
  | .error error => throw error

/-- A fuel-free loop; `none` records divergence. -/
def whileLoop {World S A : Type} (step : S → M World (Sum A S)) (state : S) : M World A :=
  fun world =>
    match step state world with
    | none => none
    | some (.error error) => some (.error error)
    | some (.ok (.inl result, nextWorld)) => some (.ok (result, nextWorld))
    | some (.ok (.inr next, nextWorld)) => whileLoop step next nextWorld
  partial_fixpoint

inductive MemoryOrder where
  | monotonic | acquire | release | acquireRelease | sequentiallyConsistent
  deriving Repr, DecidableEq

-- UNTRANSLATED
-- Source: base/cancellation.jl:1-18 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- ## Cancellation tokens
-- #
-- # Cancellation is organized around *cancellation token sources*
-- # (`Core.CancellationTokenSource`): level-triggered condition nodes arranged
-- # in a DAG (a source may have several parents). Cancelling a source cancels
-- # all of its descendants; the cancelled state is monotonic (severities only
-- # escalate, never reset). Following the
-- # .NET split, a `CancellationToken` is the observe view handed to code that
-- # may only *react* to cancellation; the source is the capability to *request*
-- # it.
-- #
-- # For convenience, the scoped value `CANCEL_TOKEN` carries the default
-- # cancellation token governing the current dynamic extent.
-- 
-- const CancellationTokenSource = Core.CancellationTokenSource
-- 
-- /Source
-- Reason: The Core source type and module prose are represented by the typed source and operation parameters below.
/--
Julia source: base/cancellation.jl:19-34 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    CancellationToken(src::CancellationTokenSource)

The observe side of a [`CancellationTokenSource`](@ref): code holding a
token can be interrupted by - and can query ([`iscancelled`](@ref)) -
cancellation of the associated source, but cannot request cancellation
itself. Only the holder of the *source* can call [`cancel!`](@ref).

A token takes effect by scoping it over a computation via the
[`CANCEL_TOKEN`](@ref) scoped value or by explicit token passing.
Once the associated source is cancelled, the computation's cancellation points (see
[`@cancel_check`](@ref)) throw a [`CancellationRequest`](@ref).
"""
struct CancellationToken
    source::CancellationTokenSource
end
```
-/
structure CancellationToken (Source : Type) where
  source : Source

/--
Julia source: base/cancellation.jl:36-47 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    CancellationRequest

The exception thrown by cancellation points whose governing cancellation
token has been cancelled. The `request` field records the severity
([`CANCEL_REQUEST_SAFE`](@ref), [`CANCEL_REQUEST_ABANDON_EXTERNAL`](@ref) or
[`CANCEL_REQUEST_ABANDON_ALL`](@ref)) as observed at delivery time; the
source may escalate afterwards.
"""
struct CancellationRequest <: Exception
    request::UInt8
end
```
-/
structure CancellationRequest where
  request : U8
  deriving Repr, DecidableEq

/--
Julia source: base/cancellation.jl:49-61 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    CANCEL_REQUEST_SAFE

Request safe cancellation. Code observing the cancellation will request safe
cancellation of any resources it is waiting for and wait for the cancellation
of such resources to be completed.

As a result, if either the cancelled code or any of its dependent resources
are currently unable to process cancellation, the request may hang and a more
aggressive cancellation severity may be required. However, in general _SAFE
should be tried first.
"""
const CANCEL_REQUEST_SAFE = CancellationRequest(0x1)
```
-/
def cancelRequestSafe : CancellationRequest := ⟨JInt.lit .u8 0x1⟩

/--
Julia source: base/cancellation.jl:63-74 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    CANCEL_REQUEST_ABANDON_EXTERNAL

Request a cancellation that will cease waiting for any external resources
(e.g. I/O objects) without going through a safe cancellation procedure for
such resources. However, internal computational tasks are still awaited.

This is a middleground between CANCEL_REQUEST_SAFE and
CANCEL_REQUEST_ABANDON_ALL, as external I/O is often engineered for
robustness in case of sudden disappearance of peers.
"""
const CANCEL_REQUEST_ABANDON_EXTERNAL = CancellationRequest(0x3)
```
-/
def cancelRequestAbandonExternal : CancellationRequest := ⟨JInt.lit .u8 0x3⟩

/--
Julia source: base/cancellation.jl:76-91 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    CANCEL_REQUEST_ABANDON_ALL

Request a cancellation that will cease waiting for all external resources,
and give up on tasks that have not responded to the cancellation: they are
frozen in place and never scheduled again.

!!! warning
    If any cancelled task has acquired locks or other resources that are
    contested, this method of cancellation may leak such resources and create
    deadlocks in future code. It is intended as a last-resort method to
    recover a system, but the necessity of this operation should in general
    be considered a bug (e.g. due to insufficient cancellation points in
    computationally-heavy code).
"""
const CANCEL_REQUEST_ABANDON_ALL = CancellationRequest(0x4)
```
-/
def cancelRequestAbandonAll : CancellationRequest := ⟨JInt.lit .u8 0x4⟩

/--
Julia source: base/cancellation.jl:93-99 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# The status byte reported by a cancellation point (`Core.cancellation_point!`)
# is the governing source's state byte (0 while uncancelled, the severity once
# cancelled) with the 0x40 bit merged in when the task has a pending
# cooperative-yield request. The mask recovers the severity half of such a
# status byte; source state reads themselves need no masking.
const STATUS_PREEMPT_BIT = 0x40
const SEVERITY_MASK = 0x3f
```
-/
def statusPreemptBit : U8 := JInt.lit .u8 0x40
def severityMask : U8 := JInt.lit .u8 0x3f

/--
Julia source: base/cancellation.jl:101-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# The severity of a request, for the delivery layer's comparisons.
severity(cr::CancellationRequest) = cr.request
```
-/
def severity (request : CancellationRequest) : U8 := request.request

structure TokenOps (World Source : Type) where
  atomicLoadState : MemoryOrder → Source → M World U8
  atomicReplaceState : MemoryOrder → MemoryOrder → Source → U8 → U8 → M World (U8 × Bool)
  newSource : List Source → M World Source
  parentAt : Source → I64 → M World Source
  nextChild : Source → Source → M World (Option Source)
  sameSource : Source → Source → Bool

/--
Julia source: base/cancellation.jl:104-116 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    cancel_severity(src::CancellationTokenSource) -> Union{Nothing, CancellationRequest}
    cancel_severity(tok::CancellationToken)

Return `nothing` if the source has not been cancelled, or a
`CancellationRequest` recording the current (monotonically escalating)
severity if it has.
"""
function cancel_severity(src::CancellationTokenSource)
    st = @atomic :acquire src.state
    st == 0x00 && return nothing
    return CancellationRequest(st)
end
```
-/
def cancelSeveritySource {World Source : Type} [Monad (M World)]
    (ops : TokenOps World Source) (source : Source) : M World (Option CancellationRequest) := do
  let state ← ops.atomicLoadState .acquire source
  if state.val == 0 then pure none else pure (some ⟨state⟩)

/--
Julia source: base/cancellation.jl:117-117 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cancel_severity(tok::CancellationToken) = cancel_severity(tok.source)
```
-/
def cancelSeverityToken {World Source : Type} [Monad (M World)]
    (ops : TokenOps World Source) (token : CancellationToken Source) : M World (Option CancellationRequest) :=
  cancelSeveritySource ops token.source

/--
Julia source: base/cancellation.jl:119-126 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    iscancelled(src::CancellationTokenSource)::Bool
    iscancelled(tok::CancellationToken)::Bool

Whether the source has been cancelled (level-triggered: once cancelled, a
source stays cancelled).
"""
iscancelled(src::CancellationTokenSource) = (@atomic :monotonic src.state) != 0x00
```
-/
def isCancelledSource {World Source : Type} [Monad (M World)]
    (ops : TokenOps World Source) (source : Source) : M World Bool := do
  pure ((← ops.atomicLoadState .monotonic source).val != 0)

/--
Julia source: base/cancellation.jl:127-127 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iscancelled(tok::CancellationToken) = iscancelled(tok.source)
```
-/
def isCancelledToken {World Source : Type} [Monad (M World)]
    (ops : TokenOps World Source) (token : CancellationToken Source) : M World Bool :=
  isCancelledSource ops token.source

/--
Julia source: base/cancellation.jl:131-153 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    CancellationTokenSource() -> CancellationTokenSource
    CancellationTokenSource(parents::CancellationToken...)

Create a new cancellation token source. With no arguments the source is a
standalone root; given one or more parent tokens, the new source is linked
underneath each of them, so that cancellation of *any* parent (or any of its
ancestors) also cancels the new source - at the highest severity requested
among them. Sources therefore form a directed acyclic graph; a source
created under an already-cancelled parent is born cancelled. Linking one
source under several parents is how an operation respects two independent
lifetimes at once (say, a request scope and the connection it arrived on).

A child source stays linked to its parents for exactly as long as it is
reachable - a held token, or work governed by it, keeps it alive. Once
nothing can observe it any more, it is garbage collected and thereby drops
out of the graph; there is no explicit detach operation.

Use [`CancellationToken`](@ref)`(src)` for the observe view, and
[`cancel!`](@ref)`(src)` to request cancellation.
"""
CancellationTokenSource(parent::CancellationToken) =
    Core._new_cancel_source(parent.source)::CancellationTokenSource
```
-/
def cancellationSourceForParent {World Source : Type} [Monad (M World)]
    (ops : TokenOps World Source) (parent : CancellationToken Source) : M World Source :=
  ops.newSource [parent.source]

/--
Julia source: base/cancellation.jl:154-160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function CancellationTokenSource(parent::CancellationToken, rest::CancellationToken...)
    srcs = CancellationTokenSource[parent.source]
    for tok in rest
        any(s -> s === tok.source, srcs) || push!(srcs, tok.source)
    end
    return Core._new_cancel_source(srcs...)::CancellationTokenSource
end
```
-/
def cancellationSourceForParents {World Source : Type} [Monad (M World)]
    (ops : TokenOps World Source) (parent : CancellationToken Source)
    (rest : List (CancellationToken Source)) : M World Source := do
  let parents := rest.foldl (fun sources token =>
    if sources.any (ops.sameSource token.source) then sources else sources ++ [token.source]) [parent.source]
  ops.newSource parents

/--
Julia source: base/cancellation.jl:161-161 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
CancellationTokenSource(::Nothing) = Core._new_cancel_source()::CancellationTokenSource
```
-/
def cancellationSourceForNothing {World Source : Type} [Monad (M World)]
    (ops : TokenOps World Source) : M World Source := ops.newSource []

/--
Julia source: base/cancellation.jl:162-162 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
CancellationTokenSource() = Core._new_cancel_source()::CancellationTokenSource
```
-/
def cancellationSourceRoot {World Source : Type} [Monad (M World)]
    (ops : TokenOps World Source) : M World Source := ops.newSource []

/--
Julia source: base/cancellation.jl:164-167 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# The i-th (1-based) parent of `src`. Parent links are strong and const, so
# these reads need no synchronization.
_cancel_parent(src::CancellationTokenSource, i::Int) =
    ccall(:jl_cancel_source_parent, Any, (Any, Csize_t), src, i - 1)::CancellationTokenSource
```
-/
def cancelParent {World Source : Type} [Monad (M World)]
    (ops : TokenOps World Source) (source : Source) (index : I64) : M World Source :=
  ops.parentAt source (i64 (index.val - 1))

/--
Julia source: base/cancellation.jl:169-175 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# The sibling after `child` on `parent`'s child list (`nothing` at its end).
# Weak, but safe to traverse from Julia: the returned reference is rooted the
# moment the ccall returns, and the GC's splice pass keeps the lists free of
# collected entries at every safepoint, so a traversal (re-)started from a
# rooted node only ever sees live sources.
_cancel_next_child(parent::CancellationTokenSource, child::CancellationTokenSource) =
    ccall(:jl_cancel_source_next_child, Any, (Any, Any), parent, child)::Union{Nothing, CancellationTokenSource}
```
-/
def cancelNextChild {World Source : Type} [Monad (M World)]
    (ops : TokenOps World Source) (parent child : Source) : M World (Option Source) :=
  ops.nextChild parent child

/--
Julia source: base/cancellation.jl:177-191 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# CAS-max the source's state to `sev` (a valid, nonzero severity). Returns
# true if the state was raised, false if it was already at (or above) the
# severity.
# seq_cst: pairs with the (child-list publication; state read) sequence in
# `jl_new_cancel_source` - see the walk in `_cancel_walk_node!`.
function _raise_state!(src::CancellationTokenSource, sev::UInt8)
    old = @atomic :monotonic src.state
    while true
        if old >= sev
            return false
        end
        old, success = @atomicreplace :sequentially_consistent :monotonic src.state old => sev
        success && return true
    end
end
```
-/
def raiseState {World Source : Type}
    (ops : TokenOps World Source) (source : Source) (requested : U8) : M World Bool := do
  let initial ← ops.atomicLoadState .monotonic source
  whileLoop (fun old => do
    if old.val >= requested.val then
      pure (.inl false)
    else
      let (observed, success) ← ops.atomicReplaceState .sequentiallyConsistent .monotonic
        source old requested
      if success then pure (.inl true) else pure (.inr observed)) initial

structure Tuple1 (α : Type) where
  only : α

-- UNTRANSLATED
-- Source: base/cancellation.jl:236-241 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- typegroup
--     mutable struct WaitEntry1
--         @atomic task::Union{Task, Nothing}
--         @atomic owner1::Any
--         next1::Union{WaitEntry1, WaitEntry2, Core.WaitEntryN, Nothing}
--         aux1::UInt64
-- /Source
-- Reason: Mutable wait-entry field layout is represented by typed entry parameters and the `WaitEntryOps` accessors.
/--
Julia source: base/cancellation.jl:242-242 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        WaitEntry1(task::Union{Task, Nothing}) = new(task, nothing, nothing, 0x0)
```
-/
def newWaitEntryOne {World Task Entry1 : Type} [Monad (M World)]
    (newOne : Option Task → M World Entry1) (task : Option Task) : M World Entry1 :=
  newOne task

-- UNTRANSLATED
-- Source: base/cancellation.jl:243-251 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     end
--     mutable struct WaitEntry2
--         @atomic task::Union{Task, Nothing}
--         @atomic owner1::Any
--         next1::Union{WaitEntry1, WaitEntry2, Core.WaitEntryN, Nothing}
--         aux1::UInt64
--         @atomic owner2::Any
--         next2::Union{WaitEntry1, WaitEntry2, Core.WaitEntryN, Nothing}
--         aux2::UInt64
-- /Source
-- Reason: The mutable two-slot entry layout is represented by its typed entry parameter and slot accessors.
/--
Julia source: base/cancellation.jl:252-253 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        WaitEntry2(task::Union{Task, Nothing}) =
            new(task, nothing, nothing, 0x0, nothing, nothing, 0x0)
```
-/
def newWaitEntryTwo {World Task Entry2 : Type} [Monad (M World)]
    (newTwo : Option Task → M World Entry2) (task : Option Task) : M World Entry2 :=
  newTwo task

-- UNTRANSLATED
-- Source: base/cancellation.jl:254-256 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     end
-- end
-- const WaitEntryN = Core.WaitEntryN
-- /Source
-- Reason: The mutable entry typegroup and Core-owned variable-slot layout are represented by typed parameters.
/--
Julia source: base/cancellation.jl:257-258 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
WaitEntryN(task::Union{Task, Nothing}, nslots::Integer) =
    ccall(:jl_new_wait_entry, Any, (Any, Csize_t), task, nslots)::WaitEntryN
```
-/
def newWaitEntryMany {World Task EntryN Count : Type} [Monad (M World)]
    (newMany : Option Task → Count → M World EntryN)
    (task : Option Task) (slots : Count) : M World EntryN :=
  newMany task slots

/--
Julia source: base/cancellation.jl:259-259 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const WaitEntry = Union{WaitEntry1, WaitEntry2, WaitEntryN}
```
-/
inductive WaitEntry (Entry1 Entry2 EntryN : Type) where
  | one (entry : Entry1)
  | two (entry : Entry2)
  | many (entry : EntryN)

inductive WaitSlotValue (Value Entry1 Entry2 EntryN : Type) where
  | owner (value : Value)
  | next (value : Option (WaitEntry Entry1 Entry2 EntryN))
  | aux (value : U64)
  | entry (value : WaitEntry Entry1 Entry2 EntryN)
  | index (value : I64)

structure WaitEntryOps (World Source Task Value Entry1 Entry2 EntryN : Type) where
  newOne : Option Task → M World Entry1
  newTwo : Option Task → M World Entry2
  manySlots : EntryN → I64
  readOwnerOne : Entry1 → M World Value
  writeOwnerOne : Entry1 → Value → M World Unit
  readOwnerTwoOne : Entry2 → M World Value
  readOwnerTwoTwo : Entry2 → M World Value
  writeOwnerTwoOne : Entry2 → Value → M World Unit
  writeOwnerTwoTwo : Entry2 → Value → M World Unit
  readOwnerMany : EntryN → I64 → M World Value
  writeOwnerMany : EntryN → I64 → Value → M World Unit
  readNextOne : Entry1 → M World (Option (WaitEntry Entry1 Entry2 EntryN))
  writeNextOne : Entry1 → Option (WaitEntry Entry1 Entry2 EntryN) → M World Unit
  readNextTwoOne : Entry2 → M World (Option (WaitEntry Entry1 Entry2 EntryN))
  readNextTwoTwo : Entry2 → M World (Option (WaitEntry Entry1 Entry2 EntryN))
  writeNextTwoOne : Entry2 → Option (WaitEntry Entry1 Entry2 EntryN) → M World Unit
  writeNextTwoTwo : Entry2 → Option (WaitEntry Entry1 Entry2 EntryN) → M World Unit
  readNextMany : EntryN → I64 → M World (Option (WaitEntry Entry1 Entry2 EntryN))
  writeNextMany : EntryN → I64 → Option (WaitEntry Entry1 Entry2 EntryN) → M World Unit
  readAuxOne : Entry1 → M World U64
  writeAuxOne : Entry1 → U64 → M World Unit
  readAuxTwoOne : Entry2 → M World U64
  readAuxTwoTwo : Entry2 → M World U64
  writeAuxTwoOne : Entry2 → U64 → M World Unit
  writeAuxTwoTwo : Entry2 → U64 → M World Unit
  readAuxMany : EntryN → I64 → M World U64
  writeAuxMany : EntryN → I64 → U64 → M World Unit
  writeTaskOne : Entry1 → Option Task → M World Unit
  writeTaskTwo : Entry2 → Option Task → M World Unit
  writeTaskMany : EntryN → Option Task → M World Unit
  cacheWaitEntry : Task → M World (Option (WaitEntry Entry1 Entry2 EntryN))
  setCacheWaitEntry : Task → WaitEntry Entry1 Entry2 EntryN → M World Unit
  cacheCancelEntry : Task → M World (Option (WaitEntry Entry1 Entry2 EntryN))
  setCacheCancelEntry : Task → WaitEntry Entry1 Entry2 EntryN → M World Unit
  sameIdentity : Value → Value → Bool
  isNothing : Value → Bool
  isCancellationSource : Value → Bool
  nothingValue : Value
  sourceValue : Source → Value
  sourceFromOwner : Value → Except CancelError Source
  unregisterCancellation : Source → WaitEntry Entry1 Entry2 EntryN → M World Unit
  castNext : Value → Except CancelError (Option (WaitEntry Entry1 Entry2 EntryN))
  castAux : Value → Except CancelError U64
  armWaitingOn : Task → WaitEntry Entry1 Entry2 EntryN → M World Bool
  claimWaitingOn : Task → WaitEntry Entry1 Entry2 EntryN → M World Bool

/--
Julia source: base/cancellation.jl:274-274 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_nslots(w::WaitEntry1) = 1
```
-/
def nslotsOne {World Source Task Value Entry1 Entry2 EntryN : Type}
    (_ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN) (_entry : Entry1) : I64 := i64 1

/--
Julia source: base/cancellation.jl:275-275 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_nslots(w::WaitEntry2) = 2
```
-/
def nslotsTwo {World Source Task Value Entry1 Entry2 EntryN : Type}
    (_ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN) (_entry : Entry2) : I64 := i64 2

/--
Julia source: base/cancellation.jl:276-276 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_nslots(w::WaitEntryN) = Int(w.nslots)
```
-/
def nslotsMany {World Source Task Value Entry1 Entry2 EntryN : Type}
    (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN) (entry : EntryN) : I64 :=
  ops.manySlots entry

/--
Julia source: base/cancellation.jl:281-281 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _slot_owner(w::WaitEntry1, i::Int) = @atomic :monotonic w.owner1
```
-/
def slotOwnerOne {World Source Task Value Entry1 Entry2 EntryN : Type} [Monad (M World)]
    (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (entry : Entry1) (_index : I64) : M World Value := ops.readOwnerOne entry

/--
Julia source: base/cancellation.jl:282-283 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _slot_owner(w::WaitEntry2, i::Int) =
    i == 1 ? (@atomic :monotonic w.owner1) : (@atomic :monotonic w.owner2)
```
-/
def slotOwnerTwo {World Source Task Value Entry1 Entry2 EntryN : Type} [Monad (M World)]
    (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (entry : Entry2) (index : I64) : M World Value :=
  if index.val == 1 then ops.readOwnerTwoOne entry else ops.readOwnerTwoTwo entry

/--
Julia source: base/cancellation.jl:284-285 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _slot_owner(w::WaitEntryN, i::Int) =
    ccall(:jl_wait_entry_slot_owner, Any, (Any, Csize_t), w, i - 1)
```
-/
def slotOwnerMany {World Source Task Value Entry1 Entry2 EntryN : Type} [Monad (M World)]
    (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (entry : EntryN) (index : I64) : M World Value :=
  ops.readOwnerMany entry (i64 (index.val - 1))

/--
Julia source: base/cancellation.jl:287-290 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _set_slot_owner!(w::WaitEntry1, i::Int, @nospecialize(v))
    @atomic :monotonic w.owner1 = v
    return nothing
end
```
-/
def setSlotOwnerOne {World Source Task Value Entry1 Entry2 EntryN : Type} [Monad (M World)]
    (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (entry : Entry1) (_index : I64) (value : Value) : M World Unit := do
  ops.writeOwnerOne entry value

/--
Julia source: base/cancellation.jl:291-298 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _set_slot_owner!(w::WaitEntry2, i::Int, @nospecialize(v))
    if i == 1
        @atomic :monotonic w.owner1 = v
    else
        @atomic :monotonic w.owner2 = v
    end
    return nothing
end
```
-/
def setSlotOwnerTwo {World Source Task Value Entry1 Entry2 EntryN : Type} [Monad (M World)]
    (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (entry : Entry2) (index : I64) (value : Value) : M World Unit := do
  if index.val == 1 then ops.writeOwnerTwoOne entry value else ops.writeOwnerTwoTwo entry value

/--
Julia source: base/cancellation.jl:299-300 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _set_slot_owner!(w::WaitEntryN, i::Int, @nospecialize(v)) =
    ccall(:jl_wait_entry_set_slot_owner, Cvoid, (Any, Csize_t, Any), w, i - 1, v)
```
-/
def setSlotOwnerMany {World Source Task Value Entry1 Entry2 EntryN : Type} [Monad (M World)]
    (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (entry : EntryN) (index : I64) (value : Value) : M World Unit :=
  ops.writeOwnerMany entry (i64 (index.val - 1)) value

/--
Julia source: base/cancellation.jl:302-302 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _slot_next(w::WaitEntry1, i::Int) = w.next1
```
-/
def slotNextOne {World Source Task Value Entry1 Entry2 EntryN : Type} [Monad (M World)]
    (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (entry : Entry1) (_index : I64) : M World (Option (WaitEntry Entry1 Entry2 EntryN)) :=
  ops.readNextOne entry

/--
Julia source: base/cancellation.jl:303-303 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _slot_next(w::WaitEntry2, i::Int) = i == 1 ? w.next1 : w.next2
```
-/
def slotNextTwo {World Source Task Value Entry1 Entry2 EntryN : Type} [Monad (M World)]
    (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (entry : Entry2) (index : I64) : M World (Option (WaitEntry Entry1 Entry2 EntryN)) :=
  if index.val == 1 then ops.readNextTwoOne entry else ops.readNextTwoTwo entry

/--
Julia source: base/cancellation.jl:304-305 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _slot_next(w::WaitEntryN, i::Int) =
    ccall(:jl_wait_entry_slot_next, Any, (Any, Csize_t), w, i - 1)::Union{WaitEntry, Nothing}
```
-/
def slotNextMany {World Source Task Value Entry1 Entry2 EntryN : Type} [Monad (M World)]
    (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (entry : EntryN) (index : I64) : M World (Option (WaitEntry Entry1 Entry2 EntryN)) :=
  ops.readNextMany entry (i64 (index.val - 1))

/--
Julia source: base/cancellation.jl:307-307 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _set_slot_next!(w::WaitEntry1, i::Int, v::Union{WaitEntry, Nothing}) = (w.next1 = v; nothing)
```
-/
def setSlotNextOne {World Source Task Value Entry1 Entry2 EntryN : Type} [Monad (M World)]
    (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (entry : Entry1) (_index : I64) (value : Option (WaitEntry Entry1 Entry2 EntryN)) : M World Unit :=
  ops.writeNextOne entry value

/--
Julia source: base/cancellation.jl:308-311 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _set_slot_next!(w::WaitEntry2, i::Int, v::Union{WaitEntry, Nothing})
    i == 1 ? (w.next1 = v) : (w.next2 = v)
    return nothing
end
```
-/
def setSlotNextTwo {World Source Task Value Entry1 Entry2 EntryN : Type} [Monad (M World)]
    (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (entry : Entry2) (index : I64) (value : Option (WaitEntry Entry1 Entry2 EntryN)) : M World Unit := do
  if index.val == 1 then ops.writeNextTwoOne entry value else ops.writeNextTwoTwo entry value

/--
Julia source: base/cancellation.jl:312-314 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _set_slot_next!(w::WaitEntryN, i::Int, v::Union{WaitEntry, Nothing}) =
    ccall(:jl_wait_entry_set_slot_next, Cvoid, (Any, Csize_t, Any), w, i - 1,
          v === nothing ? nothing : v)
```
-/
def setSlotNextMany {World Source Task Value Entry1 Entry2 EntryN : Type} [Monad (M World)]
    (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (entry : EntryN) (index : I64) (value : Option (WaitEntry Entry1 Entry2 EntryN)) : M World Unit :=
  ops.writeNextMany entry (i64 (index.val - 1)) value

/--
Julia source: base/cancellation.jl:316-316 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _slot_aux(w::WaitEntry1, i::Int) = w.aux1
```
-/
def slotAuxOne {World Source Task Value Entry1 Entry2 EntryN : Type} [Monad (M World)]
    (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (entry : Entry1) (_index : I64) : M World U64 := ops.readAuxOne entry

/--
Julia source: base/cancellation.jl:317-317 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _slot_aux(w::WaitEntry2, i::Int) = i == 1 ? w.aux1 : w.aux2
```
-/
def slotAuxTwo {World Source Task Value Entry1 Entry2 EntryN : Type} [Monad (M World)]
    (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (entry : Entry2) (index : I64) : M World U64 :=
  if index.val == 1 then ops.readAuxTwoOne entry else ops.readAuxTwoTwo entry

/--
Julia source: base/cancellation.jl:318-319 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _slot_aux(w::WaitEntryN, i::Int) =
    ccall(:jl_wait_entry_slot_aux, UInt64, (Any, Csize_t), w, i - 1)
```
-/
def slotAuxMany {World Source Task Value Entry1 Entry2 EntryN : Type} [Monad (M World)]
    (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (entry : EntryN) (index : I64) : M World U64 :=
  ops.readAuxMany entry (i64 (index.val - 1))

/--
Julia source: base/cancellation.jl:321-321 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _set_slot_aux!(w::WaitEntry1, i::Int, v::UInt64) = (w.aux1 = v; nothing)
```
-/
def setSlotAuxOne {World Source Task Value Entry1 Entry2 EntryN : Type} [Monad (M World)]
    (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (entry : Entry1) (_index : I64) (value : U64) : M World Unit :=
  ops.writeAuxOne entry value

/--
Julia source: base/cancellation.jl:322-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _set_slot_aux!(w::WaitEntry2, i::Int, v::UInt64)
    i == 1 ? (w.aux1 = v) : (w.aux2 = v)
    return nothing
end
```
-/
def setSlotAuxTwo {World Source Task Value Entry1 Entry2 EntryN : Type} [Monad (M World)]
    (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (entry : Entry2) (index : I64) (value : U64) : M World Unit := do
  if index.val == 1 then ops.writeAuxTwoOne entry value else ops.writeAuxTwoTwo entry value

/--
Julia source: base/cancellation.jl:326-327 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _set_slot_aux!(w::WaitEntryN, i::Int, v::UInt64) =
    ccall(:jl_wait_entry_set_slot_aux, Cvoid, (Any, Csize_t, UInt64), w, i - 1, v)
```
-/
def setSlotAuxMany {World Source Task Value Entry1 Entry2 EntryN : Type} [Monad (M World)]
    (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (entry : EntryN) (index : I64) (value : U64) : M World Unit :=
  ops.writeAuxMany entry (i64 (index.val - 1)) value

/--
Julia source: base/cancellation.jl:330-331 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _find_slot(w::WaitEntry1, @nospecialize(owner)) =
    (@atomic :monotonic w.owner1) === owner ? 1 : 0
```
-/
def findSlotOne {World Source Task Value Entry1 Entry2 EntryN : Type} [Monad (M World)]
    (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (entry : Entry1) (owner : Value) : M World I64 := do
  pure (if ops.sameIdentity (← ops.readOwnerOne entry) owner then i64 1 else i64 0)

/--
Julia source: base/cancellation.jl:332-334 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _find_slot(w::WaitEntry2, @nospecialize(owner)) =
    (@atomic :monotonic w.owner1) === owner ? 1 :
    (@atomic :monotonic w.owner2) === owner ? 2 : 0
```
-/
def findSlotTwo {World Source Task Value Entry1 Entry2 EntryN : Type} [Monad (M World)]
    (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (entry : Entry2) (owner : Value) : M World I64 := do
  if ops.sameIdentity (← ops.readOwnerTwoOne entry) owner then pure (i64 1)
  else if ops.sameIdentity (← ops.readOwnerTwoTwo entry) owner then pure (i64 2)
  else pure (i64 0)

/--
Julia source: base/cancellation.jl:335-340 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _find_slot(w::WaitEntryN, @nospecialize(owner))
    for i in 1:_nslots(w)
        _slot_owner(w, i) === owner && return i
    end
    return 0
end
```
-/
def findSlotMany {World Source Task Value Entry1 Entry2 EntryN : Type} [Monad (M World)]
    (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (entry : EntryN) (owner : Value) : M World I64 := do
  whileLoop (fun index => do
    if index.val > (ops.manySlots entry).val then pure (.inl (i64 0))
    else if ops.sameIdentity (← ops.readOwnerMany entry (i64 (index.val - 1))) owner then
      pure (.inl index)
    else pure (.inr (i64 (index.val + 1))) ) (i64 1)

/--
Julia source: base/cancellation.jl:343-343 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _free_slot(w::WaitEntry1) = (@atomic :monotonic w.owner1) === nothing ? 1 : 0
```
-/
def freeSlotOne {World Source Task Value Entry1 Entry2 EntryN : Type} [Monad (M World)]
    (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN) (entry : Entry1) : M World I64 := do
  pure (if ops.isNothing (← ops.readOwnerOne entry) then i64 1 else i64 0)

/--
Julia source: base/cancellation.jl:344-346 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _free_slot(w::WaitEntry2) =
    (@atomic :monotonic w.owner1) === nothing ? 1 :
    (@atomic :monotonic w.owner2) === nothing ? 2 : 0
```
-/
def freeSlotTwo {World Source Task Value Entry1 Entry2 EntryN : Type} [Monad (M World)]
    (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN) (entry : Entry2) : M World I64 := do
  if ops.isNothing (← ops.readOwnerTwoOne entry) then pure (i64 1)
  else if ops.isNothing (← ops.readOwnerTwoTwo entry) then pure (i64 2)
  else pure (i64 0)

/--
Julia source: base/cancellation.jl:347-347 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_free_slot(w::WaitEntryN) = _find_slot(w, nothing)
```
-/
def freeSlotMany {World Source Task Value Entry1 Entry2 EntryN : Type} [Monad (M World)]
    (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN) (entry : EntryN) : M World I64 :=
  findSlotMany ops entry ops.nothingValue

/--
Julia source: base/cancellation.jl:349-350 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline _slot_overflow_error() =
    throw(ConcurrencyViolationError("wait entry has no free slot for this registration"))
```
-/
def slotOverflowError {World : Type} : M World Unit :=
  throw (.concurrencyViolationError "wait entry has no free slot for this registration")

/--
Julia source: base/cancellation.jl:353-358 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _acquire_slot!(w::WaitEntry, @nospecialize(owner))
    i = _free_slot(w)
    i == 0 && _slot_overflow_error()
    _set_slot_owner!(w, i, owner)
    return i
end
```
-/
def acquireSlot {World Source Task Value Entry1 Entry2 EntryN : Type}
    [Monad (M World)] (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (entry : WaitEntry Entry1 Entry2 EntryN) (owner : Value) : M World I64 := do
  let index ← match entry with
    | .one w => freeSlotOne ops w
    | .two w => freeSlotTwo ops w
    | .many w => freeSlotMany ops w
  if index.val == 0 then slotOverflowError
  match entry with
  | .one w => setSlotOwnerOne ops w index owner
  | .two w => setSlotOwnerTwo ops w index owner
  | .many w => setSlotOwnerMany ops w index owner
  pure index

/--
Julia source: base/cancellation.jl:360-368 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# A reference to one slot of a wait entry, with `owner`/`next`/`aux`
# property access (owner accesses are relaxed-atomic; see above), and a
# vector view of an entry's slots. `slots(w)[i].owner === src`,
# `slot.next = x`, `for slot in slots(w)` are the intended spellings for
# code that is generic over the slot count.
struct WaitSlotRef{T<:WaitEntry}
    entry::T
    i::Int
end
```
-/
structure WaitSlotRef (Entry1 Entry2 EntryN : Type) where
  entry : WaitEntry Entry1 Entry2 EntryN
  index : I64

/--
Julia source: base/cancellation.jl:369-374 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function getproperty(s::WaitSlotRef, f::Symbol)
    f === :owner && return _slot_owner(getfield(s, :entry), getfield(s, :i))
    f === :next && return _slot_next(getfield(s, :entry), getfield(s, :i))
    f === :aux && return _slot_aux(getfield(s, :entry), getfield(s, :i))
    return getfield(s, f)
end
```
-/
def waitSlotRefGetProperty {World Source Task Value Entry1 Entry2 EntryN : Type}
    [Monad (M World)] (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (slot : WaitSlotRef Entry1 Entry2 EntryN) (field : String) : M World (WaitSlotValue Value Entry1 Entry2 EntryN) := do
  if field == "owner" then
    match slot.entry with
    | .one w => return .owner (← slotOwnerOne ops w slot.index)
    | .two w => return .owner (← slotOwnerTwo ops w slot.index)
    | .many w => return .owner (← slotOwnerMany ops w slot.index)
  else if field == "next" then
    match slot.entry with
    | .one w => return .next (← slotNextOne ops w slot.index)
    | .two w => return .next (← slotNextTwo ops w slot.index)
    | .many w => return .next (← slotNextMany ops w slot.index)
  else if field == "aux" then
    match slot.entry with
    | .one w => return .aux (← slotAuxOne ops w slot.index)
    | .two w => return .aux (← slotAuxTwo ops w slot.index)
    | .many w => return .aux (← slotAuxMany ops w slot.index)
  else if field == "entry" then pure (.entry slot.entry)
  else if field == "i" then pure (.index slot.index)
  else throw (.fieldError "WaitSlotRef" field)

/--
Julia source: base/cancellation.jl:375-386 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function setproperty!(s::WaitSlotRef, f::Symbol, @nospecialize(v))
    if f === :owner
        _set_slot_owner!(getfield(s, :entry), getfield(s, :i), v)
    elseif f === :next
        _set_slot_next!(getfield(s, :entry), getfield(s, :i), v::Union{WaitEntry, Nothing})
    elseif f === :aux
        _set_slot_aux!(getfield(s, :entry), getfield(s, :i), v::UInt64)
    else
        throw(FieldError(WaitSlotRef, f))
    end
    return v
end
```
-/
def waitSlotRefSetProperty {World Source Task Value Entry1 Entry2 EntryN : Type}
    [Monad (M World)] (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (slot : WaitSlotRef Entry1 Entry2 EntryN) (field : String) (value : Value) : M World Value := do
  if field == "owner" then
    match slot.entry with
    | .one w => setSlotOwnerOne ops w slot.index value
    | .two w => setSlotOwnerTwo ops w slot.index value
    | .many w => setSlotOwnerMany ops w slot.index value
  else if field == "next" then
    let next ← liftExceptM (ops.castNext value)
    match slot.entry with
    | .one w => setSlotNextOne ops w slot.index next
    | .two w => setSlotNextTwo ops w slot.index next
    | .many w => setSlotNextMany ops w slot.index next
  else if field == "aux" then
    let aux ← liftExceptM (ops.castAux value)
    match slot.entry with
    | .one w => setSlotAuxOne ops w slot.index aux
    | .two w => setSlotAuxTwo ops w slot.index aux
    | .many w => setSlotAuxMany ops w slot.index aux
  else
    throw (.fieldError "WaitSlotRef" field)
  pure value

def entrySlotCount {World Source Task Value Entry1 Entry2 EntryN : Type}
    (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (entry : WaitEntry Entry1 Entry2 EntryN) : I64 :=
  match entry with
  | .one w => nslotsOne ops w
  | .two w => nslotsTwo ops w
  | .many w => nslotsMany ops w

/--
Julia source: base/cancellation.jl:388-390 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct WaitSlots{T<:WaitEntry} <: AbstractVector{WaitSlotRef{T}}
    entry::T
end
```
-/
structure WaitSlots (Entry1 Entry2 EntryN : Type) where
  entry : WaitEntry Entry1 Entry2 EntryN

/--
Julia source: base/cancellation.jl:391-391 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(s::WaitSlots) = (_nslots(getfield(s, :entry)),)
```
-/
def waitSlotsSize {World Source Task Value Entry1 Entry2 EntryN : Type}
    (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (slots : WaitSlots Entry1 Entry2 EntryN) : Tuple1 I64 :=
  ⟨entrySlotCount ops slots.entry⟩

/--
Julia source: base/cancellation.jl:392-392 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline getindex(s::WaitSlots, i::Int) = WaitSlotRef(getfield(s, :entry), i)
```
-/
def waitSlotsGetIndex {Entry1 Entry2 EntryN : Type}
    (slots : WaitSlots Entry1 Entry2 EntryN) (index : I64) : WaitSlotRef Entry1 Entry2 EntryN :=
  ⟨slots.entry, index⟩

/--
Julia source: base/cancellation.jl:393-393 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
slots(w::WaitEntry) = WaitSlots(w)
```
-/
def slots {Entry1 Entry2 EntryN : Type}
    (entry : WaitEntry Entry1 Entry2 EntryN) : WaitSlots Entry1 Entry2 EntryN :=
  ⟨entry⟩

/--
Julia source: base/cancellation.jl:399-404 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _release_slot!(w::WaitEntry, i::Int)
    _set_slot_next!(w, i, nothing)
    _set_slot_aux!(w, i, UInt64(0))
    _set_slot_owner!(w, i, nothing)
    return nothing
end
```
-/
def releaseSlot {World Source Task Value Entry1 Entry2 EntryN : Type}
    [Monad (M World)] (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (entry : WaitEntry Entry1 Entry2 EntryN) (index : I64) : M World Unit := do
  match entry with
  | .one w =>
      ops.writeNextOne w none
      ops.writeAuxOne w (JInt.lit .u64 0)
      ops.writeOwnerOne w ops.nothingValue
  | .two w =>
      if index.val == 1 then
        ops.writeNextTwoOne w none
        ops.writeAuxTwoOne w (JInt.lit .u64 0)
        ops.writeOwnerTwoOne w ops.nothingValue
      else
        ops.writeNextTwoTwo w none
        ops.writeAuxTwoTwo w (JInt.lit .u64 0)
        ops.writeOwnerTwoTwo w ops.nothingValue
  | .many w =>
      let i := i64 (index.val - 1)
      ops.writeNextMany w i none
      ops.writeAuxMany w i (JInt.lit .u64 0)
      ops.writeOwnerMany w i ops.nothingValue

/--
Julia source: base/cancellation.jl:408-411 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _next_on(w::WaitEntry, @nospecialize(owner))
    i = _find_slot(w, owner)
    return i == 0 ? nothing : _slot_next(w, i)
end
```
-/
def nextOn {World Source Task Value Entry1 Entry2 EntryN : Type}
    [Monad (M World)] (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (entry : WaitEntry Entry1 Entry2 EntryN) (owner : Value) : M World (Option (WaitEntry Entry1 Entry2 EntryN)) := do
  let index ← match entry with
    | .one w => findSlotOne ops w owner
    | .two w => findSlotTwo ops w owner
    | .many w => findSlotMany ops w owner
  if index.val == 0 then pure none
  else
    match entry with
    | .one w => slotNextOne ops w index
    | .two w => slotNextTwo ops w index
    | .many w => slotNextMany ops w index

/--
Julia source: base/cancellation.jl:416-416 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_set_wait_witness!(w::WaitEntry, @nospecialize(x)) = (_acquire_slot!(w, x); nothing)
```
-/
def setWaitWitness {World Source Task Value Entry1 Entry2 EntryN : Type}
    [Monad (M World)] (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (entry : WaitEntry Entry1 Entry2 EntryN) (owner : Value) : M World Unit := do
  let _ ← acquireSlot ops entry owner
  pure ()

/--
Julia source: base/cancellation.jl:417-421 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _clear_wait_witness!(w::WaitEntry, @nospecialize(x))
    i = _find_slot(w, x)
    i == 0 || _release_slot!(w, i)
    return nothing
end
```
-/
def clearWaitWitness {World Source Task Value Entry1 Entry2 EntryN : Type}
    [Monad (M World)] (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (entry : WaitEntry Entry1 Entry2 EntryN) (owner : Value) : M World Unit := do
  let index ← match entry with
    | .one w => findSlotOne ops w owner
    | .two w => findSlotTwo ops w owner
    | .many w => findSlotMany ops w owner
  if index.val != 0 then releaseSlot ops entry index

/--
Julia source: base/cancellation.jl:427-437 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _clear_uv_witness!(w::WaitEntry)
    for slot in slots(w)
        o = slot.owner
        (o === nothing || o isa CancellationTokenSource) && continue
        slot.next = nothing
        slot.aux = UInt64(0) # e.g. the uv write cancel flag; see _release_slot!
        slot.owner = nothing
        break
    end
    return nothing
end
```
-/
def clearUvWitness {World Source Task Value Entry1 Entry2 EntryN : Type}
    [Monad (M World)] (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (entry : WaitEntry Entry1 Entry2 EntryN) : M World Unit := do
  let _ ← whileLoop (fun index => do
    if index.val > (entrySlotCount ops entry).val then pure (.inl ())
    else
      let owner ← match entry with
        | .one w => slotOwnerOne ops w index
        | .two w => slotOwnerTwo ops w index
        | .many w => slotOwnerMany ops w index
      if ops.isNothing owner || ops.isCancellationSource owner then
        pure (.inr (i64 (index.val + 1)))
      else do
        match entry with
        | .one w =>
            ops.writeNextOne w none
            ops.writeAuxOne w (JInt.lit .u64 0)
            ops.writeOwnerOne w ops.nothingValue
        | .two _ => releaseSlot ops entry index
        | .many _ => releaseSlot ops entry index
        pure (.inl ())) (i64 1)
  pure ()

/--
Julia source: base/cancellation.jl:439-461 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Return `waiter`'s cached wait entry for a *plain* (non-cancellable) park,
# or a fresh (and newly cached) one if the cached one is still in use.
#
# Plain parks arm a *distinct* entry from cancellable parks
# (`_cancel_wait_entry`), and that identity split is what keeps shields
# shielded: the cancellation walk's only sound eligibility gate is its
# expected-entry claim CAS, so an entry registered on a source must never
# be armed for a wait that is not cancellable under it. (Aux data outside
# the claim word - the severity floors - is read racily by the walk and may
# be judged against an adjacent arm of the same entry; that misfire is
# tolerable for a teardown wait's floor, never for a shield: sharing one
# entry would let a walk claim a shielded re-arm using the previous arm's
# eligibility.)
function _cached_wait_entry(waiter::Task)
    w = waiter.cached_wait_entry
    if w isa WaitEntry1 && (@atomic :monotonic w.owner1) === nothing
        @atomic :monotonic w.task = waiter
    else
        w = WaitEntry1(waiter)
        waiter.cached_wait_entry = w
    end
    return w
end
```
-/
def cachedWaitEntry {World Source Task Value Entry1 Entry2 EntryN : Type}
    [Monad (M World)] (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (task : Task) : M World (WaitEntry Entry1 Entry2 EntryN) := do
  match ← ops.cacheWaitEntry task with
  | some (.one entry) =>
      if ops.isNothing (← ops.readOwnerOne entry) then
        ops.writeTaskOne entry (some task)
        pure (.one entry)
      else do
        let fresh ← ops.newOne (some task)
        ops.setCacheWaitEntry task (.one fresh)
        pure (.one fresh)
  | _ => do
      let fresh ← ops.newOne (some task)
      ops.setCacheWaitEntry task (.one fresh)
      pure (.one fresh)

/--
Julia source: base/cancellation.jl:463-468 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# A source slot's aux: the low byte is the minimum delivery severity (the
# "floor"); the watcher bit marks a `wait(::CancellationToken)` slot, whose
# claimed wake the walk *completes* with the request as a value instead of
# interrupting the task - the cancellation is the event that wait is for.
# Staged pre-arm like the floor (see below).
const WAIT_AUX_WATCHER_BIT = UInt64(0x100)
```
-/
def waitAuxWatcherBit : U64 := JInt.lit .u64 0x100

/--
Julia source: base/cancellation.jl:470-506 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Return the entry for a cancellable park of `waiter` governed by `src`,
# with the minimum delivery severity staged on the source slot. Must run
# before the arm: the cancellation walk reads the slot's aux only through
# an armed entry, so it has to be in place when `waiting_on` is published.
# Convention: `min_severity` is the lowest severity that may wake the wait
# (inclusive comparisons on both the registration and walk sides); a
# teardown wait that already acknowledged a delivery at severity `s` stages
# `s + 0x01` so only an escalation wakes it.
#
# The cached entry is reused when its sticky source slot is compatible:
# already on `src` (the common case - a task parking repeatedly under its
# ambient token pays no registry work after the first park), or free. When
# it is bound to a *different* source (the task's governing token changed),
# the owner unregisters it - the one O(list) operation on a park path, paid
# once per token migration - and rebinds. A cache entry stuck on a wait
# queue (stale registration from an interrupted wait, not yet collected)
# leaves a fresh single-use entry whose source registration becomes an
# unarmed corpse for pruning.
function _cancel_wait_entry(waiter::Task, src::CancellationTokenSource,
                            min_severity::UInt8)
    w = waiter.cached_cancel_entry
    if w isa WaitEntry2 && (@atomic :monotonic w.owner1) === nothing
        o = @atomic :monotonic w.owner2
        if !(o === src || o === nothing)
            # rebind: physically drop the stale sticky registration first
            unregister_cancellation!(o::CancellationTokenSource, w)
        end
        @atomic :monotonic w.task = waiter
    elseif w isa WaitEntry2
        w = WaitEntry2(waiter)
    else
        w = WaitEntry2(waiter)
        waiter.cached_cancel_entry = w
    end
    w.aux2 = UInt64(min_severity)
    return w
end
```
-/
def cachedCancelEntry {World Source Task Value Entry1 Entry2 EntryN : Type}
    [Monad (M World)] (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (task : Task) (source : Source) (minSeverity : U8) : M World (WaitEntry Entry1 Entry2 EntryN) := do
  let entry ← ops.cacheCancelEntry task
  let result ← match entry with
    | some (.two old) =>
        if ops.isNothing (← ops.readOwnerTwoOne old) then do
          let owner := ← ops.readOwnerTwoTwo old
          if !ops.sameIdentity owner (ops.sourceValue source) && !ops.isNothing owner then do
            let oldSource ← liftExceptM (ops.sourceFromOwner owner)
            ops.unregisterCancellation oldSource (.two old)
          ops.writeTaskTwo old (some task)
          pure (.two old)
        else
          pure (.two (← ops.newTwo (some task)))
    | _ => do
        let fresh ← ops.newTwo (some task)
        ops.setCacheCancelEntry task (.two fresh)
        pure (.two fresh)
  match result with
  | .two entry => ops.writeAuxTwoTwo entry (JInt.wrap .u64 minSeverity.val)
  | _ => pure ()
  pure result

/--
Julia source: base/cancellation.jl:508-510 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function _wait_registration_error()
    throw(ConcurrencyViolationError("Task is already registered on a wait queue"))
end
```
-/
def waitRegistrationError {World : Type} : M World Unit :=
  throw (.concurrencyViolationError "Task is already registered on a wait queue")

/--
Julia source: base/cancellation.jl:512-517 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Publish `w` as `waiter`'s only armed wait registration.
function _arm_wait(waiter::Task, w::WaitEntry)
    armed = @atomicreplace :release :monotonic waiter.waiting_on nothing => w
    armed.success || _wait_registration_error()
    return w
end
```
-/
def armWait {World Source Task Value Entry1 Entry2 EntryN : Type}
    [Monad (M World)] (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (waitRegistrationError : M World Unit) (task : Task)
    (entry : WaitEntry Entry1 Entry2 EntryN) : M World (WaitEntry Entry1 Entry2 EntryN) := do
  let armed ← ops.armWaitingOn task entry
  if armed then pure entry else do
    let _ ← waitRegistrationError
    pure entry

/--
Julia source: base/cancellation.jl:519-523 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Claim the wake of the wait that `w` was registered for (returns whether the
# claim succeeded). `w` must be an entry armed for `t` (`_arm_wait`).
function claim_wait(t::Task, w::WaitEntry)
    return (@atomicreplace t.waiting_on w => nothing).success
end
```
-/
def claimWait {World Source Task Value Entry1 Entry2 EntryN : Type}
    [Monad (M World)] (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (task : Task) (entry : WaitEntry Entry1 Entry2 EntryN) : M World Bool :=
  ops.claimWaitingOn task entry

structure RegistryOps (World Source Task Lock Entry1 Entry2 EntryN : Type) where
  atomicLoadWalkLock : MemoryOrder → Source → M World (Option Lock)
  newWalkLock : M World Lock
  atomicReplaceWalkLock : MemoryOrder → MemoryOrder → Source → Option Lock → Lock → M World (Option Lock × Bool)
  lock : Lock → M World Unit
  trylock : Lock → M World Bool
  unlock : Lock → M World Unit
  atomicIncrementDead : Source → M World U32
  atomicLoadRegCount : Source → M World U32
  atomicStoreDeadCount : Source → U32 → M World Unit
  atomicStoreRegCount : Source → U32 → M World Unit
  waitersHead : MemoryOrder → Source → M World (Option (WaitEntry Entry1 Entry2 EntryN))
  atomicReplaceWaitersHead : MemoryOrder → MemoryOrder → Source → WaitEntry Entry1 Entry2 EntryN → Option (WaitEntry Entry1 Entry2 EntryN) → M World Bool
  taskOfEntry : WaitEntry Entry1 Entry2 EntryN → M World (Option Task)
  isTaskDone : Task → M World Bool
  waitingOn : Task → MemoryOrder → M World (Option (WaitEntry Entry1 Entry2 EntryN))
  sameEntry : WaitEntry Entry1 Entry2 EntryN → WaitEntry Entry1 Entry2 EntryN → Bool
  childHead : MemoryOrder → Source → M World (Option Source)

structure CancellationRuntimeOps (World Source Task Entry1 Entry2 EntryN : Type) where
  currentTask : M World Task
  clearPreemptRequest : Task → U8 → M World Unit
  yield : M World Unit
  atomicFenceHeavy : M World Unit
  shootdownCancelledTasks : M World Unit
  deliverClaimedValueWake : Task → WaitEntry Entry1 Entry2 EntryN → CancellationRequest → M World Unit
  deliverClaimedWake : Task → WaitEntry Entry1 Entry2 EntryN → CancellationRequest → M World Unit
  renderSeverity : U8 → String

structure ScopeOps (World Source Task Scope : Type) where
  currentTask : M World Task
  taskScope : Task → M World (Option Scope)
  currentScope : M World (Option Scope)
  scopeCancelToken : Scope → M World (Option (Option (CancellationToken Source)))
  boundCancelDefault : Task → M World U8
  boundCancelToken : Task → M World (Option Source)
  setBoundCancelToken : Task → Option Source → M World Unit
  setBoundCancelDefault : Task → U8 → M World Unit

def entryFindSlot {World Source Task Value Entry1 Entry2 EntryN : Type} [Monad (M World)]
    (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (entry : WaitEntry Entry1 Entry2 EntryN) (owner : Value) : M World I64 := do
  match entry with
  | .one w => findSlotOne ops w owner
  | .two w => findSlotTwo ops w owner
  | .many w => findSlotMany ops w owner

def entryOwnerAt {World Source Task Value Entry1 Entry2 EntryN : Type} [Monad (M World)]
    (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (entry : WaitEntry Entry1 Entry2 EntryN) (index : I64) : M World Value := do
  match entry with
  | .one w => slotOwnerOne ops w index
  | .two w => slotOwnerTwo ops w index
  | .many w => slotOwnerMany ops w index

def entrySetOwnerAt {World Source Task Value Entry1 Entry2 EntryN : Type} [Monad (M World)]
    (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (entry : WaitEntry Entry1 Entry2 EntryN) (index : I64) (value : Value) : M World Unit := do
  match entry with
  | .one w => setSlotOwnerOne ops w index value
  | .two w => setSlotOwnerTwo ops w index value
  | .many w => setSlotOwnerMany ops w index value

def entryNextAt {World Source Task Value Entry1 Entry2 EntryN : Type} [Monad (M World)]
    (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (entry : WaitEntry Entry1 Entry2 EntryN) (index : I64) : M World (Option (WaitEntry Entry1 Entry2 EntryN)) := do
  match entry with
  | .one w => slotNextOne ops w index
  | .two w => slotNextTwo ops w index
  | .many w => slotNextMany ops w index

def entrySetNextAt {World Source Task Value Entry1 Entry2 EntryN : Type} [Monad (M World)]
    (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (entry : WaitEntry Entry1 Entry2 EntryN) (index : I64)
    (value : Option (WaitEntry Entry1 Entry2 EntryN)) : M World Unit := do
  match entry with
  | .one w => setSlotNextOne ops w index value
  | .two w => setSlotNextTwo ops w index value
  | .many w => setSlotNextMany ops w index value

def entryAuxAt {World Source Task Value Entry1 Entry2 EntryN : Type} [Monad (M World)]
    (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (entry : WaitEntry Entry1 Entry2 EntryN) (index : I64) : M World U64 := do
  match entry with
  | .one w => slotAuxOne ops w index
  | .two w => slotAuxTwo ops w index
  | .many w => slotAuxMany ops w index

def entrySetAuxAt {World Source Task Value Entry1 Entry2 EntryN : Type} [Monad (M World)]
    (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (entry : WaitEntry Entry1 Entry2 EntryN) (index : I64) (value : U64) : M World Unit := do
  match entry with
  | .one w => setSlotAuxOne ops w index value
  | .two w => setSlotAuxTwo ops w index value
  | .many w => setSlotAuxMany ops w index value

def entrySetTask {World Source Task Value Entry1 Entry2 EntryN : Type} [Monad (M World)]
    (ops : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (entry : WaitEntry Entry1 Entry2 EntryN) (task : Option Task) : M World Unit := do
  match entry with
  | .one w => ops.writeTaskOne w task
  | .two w => ops.writeTaskTwo w task
  | .many w => ops.writeTaskMany w task

/--
Julia source: base/cancellation.jl:537-547 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Serialize walks on `src` (cancellation delivery, pruning, owner-side
# unregistration). Never taken on park/wake paths; contended walkers sleep.
# The lock object is installed lazily by the first walker, so sources that
# are never walked stay two words smaller than a ReentrantLock.
function _walk_lock(src::CancellationTokenSource)
    l = @atomic :acquire src.walk_lock
    l === nothing || return l::ReentrantLock
    newl = ReentrantLock()
    old, ok = @atomicreplace :acquire_release :acquire src.walk_lock nothing => newl
    return ok ? newl : old::ReentrantLock
end
```
-/
def walkLock {World Source Task Lock Entry1 Entry2 EntryN : Type} [Monad (M World)]
    (ops : RegistryOps World Source Task Lock Entry1 Entry2 EntryN) (source : Source) : M World Lock := do
  match ← ops.atomicLoadWalkLock .acquire source with
  | some lock => pure lock
  | none => do
      let fresh ← ops.newWalkLock
      let (old, succeeded) ← ops.atomicReplaceWalkLock .acquireRelease .acquire source none fresh
      if succeeded then pure fresh else
        match old with
        | some lock => pure lock
        | none => throw (.other "walk-lock compare-and-swap returned no lock")

/--
Julia source: base/cancellation.jl:548-550 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# A walk delivers (or collects for) cancellations, possibly of the very
# scope the walking task runs under: the acquire must be shielded.
_lock_walk(src::CancellationTokenSource) = lock(_walk_lock(src); cancel=nothing)
```
-/
def lockWalk {World Source Task Lock Entry1 Entry2 EntryN : Type} [Monad (M World)]
    (ops : RegistryOps World Source Task Lock Entry1 Entry2 EntryN) (source : Source) : M World Unit := do
  ops.lock (← walkLock ops source)

/--
Julia source: base/cancellation.jl:551-551 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_trylock_walk(src::CancellationTokenSource) = trylock(_walk_lock(src))
```
-/
def tryLockWalk {World Source Task Lock Entry1 Entry2 EntryN : Type} [Monad (M World)]
    (ops : RegistryOps World Source Task Lock Entry1 Entry2 EntryN) (source : Source) : M World Bool := do
  ops.trylock (← walkLock ops source)

/--
Julia source: base/cancellation.jl:552-552 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_unlock_walk(src::CancellationTokenSource) = unlock(_walk_lock(src))
```
-/
def unlockWalk {World Source Task Lock Entry1 Entry2 EntryN : Type} [Monad (M World)]
    (ops : RegistryOps World Source Task Lock Entry1 Entry2 EntryN) (source : Source) : M World Unit := do
  ops.unlock (← walkLock ops source)

/--
Julia source: base/cancellation.jl:560-560 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const _PRUNE_DEAD_THRESHOLD = UInt32(16)
```
-/
def pruneDeadThreshold : U32 := JInt.lit .u32 16

/--
Julia source: base/cancellation.jl:562-578 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Account a newly dead registration on `src` and prune when enough have
# accumulated. `>=`, not `==`: when the incrementer that crosses the
# threshold loses `_try_prune!`'s trylock to a concurrent walk, corpses that
# walk had already passed remain counted here, and the next death must retry
# the prune rather than let the count sail past the threshold forever.
# The threshold scales with the (approximate) list length: a prune walk is
# O(list), so tripping it every fixed number of deaths makes a mass fan-out
# parking under one source - e.g. any large task tree governed by a shared
# ambient token - quadratic in its waiter count. Requiring the dead to be a
# constant fraction of the list amortizes each walk against the corpses it
# collects.
function _note_dead_registration!(src::CancellationTokenSource)
    dc = @atomic :monotonic src.dead_count += UInt32(1)
    threshold = max(_PRUNE_DEAD_THRESHOLD, (@atomic :monotonic src.reg_count) >> 2)
    dc >= threshold && _try_prune!(src)
    return nothing
end
```
-/
def noteDeadRegistration {World Source Task Lock Entry1 Entry2 EntryN : Type} [Monad (M World)]
    (ops : RegistryOps World Source Task Lock Entry1 Entry2 EntryN)
    (tryPrune : Source → M World Unit) (source : Source) : M World Unit := do
  let dead ← ops.atomicIncrementDead source
  let registered ← ops.atomicLoadRegCount source
  let threshold := if registered.val / 4 > pruneDeadThreshold.val
    then JInt.wrap .u32 (registered.val / 4) else pruneDeadThreshold
  if dead.val >= threshold.val then tryPrune source
  pure ()

/--
Julia source: base/cancellation.jl:580-586 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Relaxed load of the waiter-list head (an `Any` field whose non-entry
# initial value means the empty list). The walk's seq_cst head read stays
# spelled out at its use site.
@inline function _waiters_head(src::CancellationTokenSource)
    h = @atomic :monotonic src.waiters_head
    return h isa WaitEntry ? h : nothing
end
```
-/
def waitersHead {World Source Task Lock Entry1 Entry2 EntryN : Type} [Monad (M World)]
    (ops : RegistryOps World Source Task Lock Entry1 Entry2 EntryN) (source : Source) :
    M World (Option (WaitEntry Entry1 Entry2 EntryN)) :=
  ops.waitersHead .monotonic source

/--
Julia source: base/cancellation.jl:593-632 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Owner-side physical unregistration of `w` from `src`'s waiter list: an
# O(list) walk under the walk lock. Used on the rare paths that must drop a
# sticky registration eagerly - rebinding the cached cancel entry after a
# token migration - not on any wakeup path (normal wakeups leave the
# registration in place). `w` must be unarmed and owned by the caller.
function unregister_cancellation!(src::CancellationTokenSource, w::WaitEntry)
    wi = _find_slot(w, src)
    wi == 0 && return nothing
    wslot = slots(w)[wi]
    _lock_walk(src)
    prev = nothing # the predecessor's slot for `src`, once past the head
    x = _waiters_head(src)
    while x isa WaitEntry
        xi = x === w ? wi : _find_slot(x, src)
        # a linked entry always has a slot for this source (see
        # _walk_waiters!); bail out without touching the structure otherwise
        xi == 0 && break
        slot = slots(x)[xi]
        xnext = slot.next
        if x === w
            if prev === nothing
                # racing pushes prepend; retrying against the fresh head
                # re-finds `w`'s predecessor
                if !(@atomicreplace :monotonic :monotonic src.waiters_head x => xnext).success
                    x = _waiters_head(src)
                    continue
                end
            else
                prev.next = xnext
            end
            wslot.next = nothing
            break
        end
        prev = slot
        x = xnext
    end
    wslot.owner = nothing
    _unlock_walk(src)
    return nothing
end
```
-/
def unregisterCancellation {World Source Task Value Lock Entry1 Entry2 EntryN : Type}
    [Monad (M World)] (waitOps : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (registry : RegistryOps World Source Task Lock Entry1 Entry2 EntryN)
    (source : Source) (entry : WaitEntry Entry1 Entry2 EntryN) : M World Unit := do
  let owner := waitOps.sourceValue source
  let index ← entryFindSlot waitOps entry owner
  if index.val == 0 then return ()
  let sourceSlot : WaitSlotRef Entry1 Entry2 EntryN :=
    @waitSlotsGetIndex Entry1 Entry2 EntryN
      (@slots Entry1 Entry2 EntryN entry) index
  lockWalk registry source
  let start ← waitersHead registry source
  let _ ← whileLoop (fun (previous, current) => do
    match current with
    | none => pure (.inl ())
    | some candidate => do
        let sameEntry := registry.sameEntry candidate entry
        let candidateIndex ← if sameEntry then pure index else entryFindSlot waitOps candidate owner
        if candidateIndex.val == 0 then pure (.inl ())
        else do
          let slot : WaitSlotRef Entry1 Entry2 EntryN :=
            @waitSlotsGetIndex Entry1 Entry2 EntryN
              (@slots Entry1 Entry2 EntryN candidate) candidateIndex
          let next ← entryNextAt waitOps candidate candidateIndex
          if sameEntry then
            match previous with
            | none => do
                let removed ← registry.atomicReplaceWaitersHead .monotonic .monotonic source candidate next
                if removed then
                  let _ ← entrySetNextAt waitOps entry index none
                  pure (.inl ())
                else
                  pure (.inr (none, ← waitersHead registry source))
            | some previousSlot => do
                let _ ← entrySetNextAt waitOps previousSlot.entry previousSlot.index next
                let _ ← entrySetNextAt waitOps entry index none
                pure (.inl ())
          else
            pure (.inr (some slot, next))) (none, start)
  let _ ← waitSlotRefSetProperty waitOps sourceSlot "owner" waitOps.nothingValue
  unlockWalk registry source
  pure ()

/--
Julia source: base/cancellation.jl:634-645 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Mark the single-use entry `w` as done with its (sticky) source
# registrations: walks then collect it like an entry of a completed task.
# For per-call entries (`Experimental.wait_with_timeout`, waitany) whose
# task may live - and keep registering - indefinitely.
function retire_cancellation_entry!(w::WaitEntry)
    @atomic :monotonic w.task = nothing
    for slot in slots(w)
        o = slot.owner
        o isa CancellationTokenSource && _note_dead_registration!(o)
    end
    return nothing
end
```
-/
def retireCancellationEntry {World Source Task Value Entry1 Entry2 EntryN : Type}
    [Monad (M World)] (waitOps : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (noteDead : Source → M World Unit) (entry : WaitEntry Entry1 Entry2 EntryN) : M World Unit := do
  entrySetTask waitOps entry none
  let _ ← whileLoop (fun index => do
    if index.val > (entrySlotCount waitOps entry).val then pure (.inl ())
    else do
      let owner ← entryOwnerAt waitOps entry index
      if waitOps.isCancellationSource owner then do
        let source ← liftExceptM (waitOps.sourceFromOwner owner)
        noteDead source
      pure (.inr (i64 (index.val + 1)))) (i64 1)
  pure ()

/--
Julia source: base/cancellation.jl:647-655 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Prune walk: collect unarmed corpses (completed tasks, retired entries).
# Never delivers - delivery is `cancel!`'s walk, and any registrant racing
# a cancellation is covered by its own state recheck.
@noinline function _try_prune!(src::CancellationTokenSource)
    _trylock_walk(src) || return nothing  # a running walk collects anyway
    _walk_waiters!(src, 0x00)
    _unlock_walk(src)
    return nothing
end
```
-/
def tryPrune {World Source Task Lock Entry1 Entry2 EntryN : Type}
    [Monad (M World)] (registry : RegistryOps World Source Task Lock Entry1 Entry2 EntryN)
    (walkWaiters : Source → U8 → M World (List (Task × WaitEntry Entry1 Entry2 EntryN × U64)))
    (source : Source) : M World Unit := do
  if !(← tryLockWalk registry source) then pure ()
  else do
    let _ ← walkWaiters source (JInt.lit .u8 0)
    unlockWalk registry source
    pure ()

/--
Julia source: base/cancellation.jl:662-700 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    cancel!(src::CancellationTokenSource,
            request::CancellationRequest=CANCEL_REQUEST_SAFE)::Bool

Cancel `src` and all of its descendants at the given severity. Level-triggered
and monotonic: observers (including future registrants) see the cancellation
until the source is discarded, and repeated calls only have an effect when
they *escalate* the severity ([`CANCEL_REQUEST_SAFE`](@ref) ->
[`CANCEL_REQUEST_ABANDON_EXTERNAL`](@ref) ->
[`CANCEL_REQUEST_ABANDON_ALL`](@ref)). Returns whether the call changed the
state.

Computations governed by a token of `src` or a descendant observe the cancellation at
their cancellation points (see [`@cancel_check`](@ref)), which throw a
[`CancellationRequest`](@ref).

When `cancel!` returns, every source currently reachable from `src` has
been advanced to (at least) the requested severity by this very call.
"""
function cancel!(src::CancellationTokenSource,
                 request::CancellationRequest=CANCEL_REQUEST_SAFE)
    sev = request.request
    if !(sev == 0x1 || sev == 0x3 || sev == 0x4)
        throw(ArgumentError("invalid cancellation severity $(repr(request.request))"))
    end
    raised = _raise_state!(src, sev)
    # Mark the cancelled subgraph (waking parked waiters): each node is
    # marked before its children so a concurrent construction of a child
    # source is level-triggered.
    _cancel_walk!(src, sev)
    Threads.atomic_fence_heavy()
    # Shoot down any task now bound to a cancelled source: threads inside a
    # compiled cancellation region are asynchronously reset to their
    # cancellation point, which observes the cancellation and throws.
    # Best-effort: a task the walk misses recovers level-triggered at its
    # next cancellation point (or reset-safe allocation).
    ccall(:jl_shootdown_cancelled_tasks, Cvoid, ())
    return raised
end
```
-/
def cancelSource {World Source Task Entry1 Entry2 EntryN : Type}
    [Monad (M World)] (tokenOps : TokenOps World Source)
    (runtime : CancellationRuntimeOps World Source Task Entry1 Entry2 EntryN)
    (cancelWalk : Source → U8 → M World Unit)
    (source : Source) (request : CancellationRequest) : M World Bool := do
  let severity := request.request
  if !(severity.val == 0x1 || severity.val == 0x3 || severity.val == 0x4) then
    throw (.argumentError ("invalid cancellation severity " ++ runtime.renderSeverity severity))
  let raised ← raiseState tokenOps source severity
  cancelWalk source severity
  runtime.atomicFenceHeavy
  runtime.shootdownCancelledTasks
  pure raised

/--
Julia source: base/cancellation.jl:702-721 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Base.redeliver!(src::CancellationTokenSource) -> Bool

Re-run the delivery pass for an already-cancelled source at its current
severity: wakes waiters that registered without observing the cancellation
and re-sends the interruption signal to bound running computations (the
signal-based delivery is best-effort and can be missed while a reset point
is unpublished). Used by the ^C machinery when a press finds the episode
source already marked cancelled (e.g. by the C-side fast path in
`jl_sigint_request_cancellation`, which cannot wake parked waiters itself).
Returns whether the source was cancelled at all.
"""
function redeliver!(src::CancellationTokenSource)
    st = @atomic :acquire src.state
    st == 0x00 && return false
    _cancel_walk!(src, st)
    Threads.atomic_fence_heavy()
    ccall(:jl_shootdown_cancelled_tasks, Cvoid, ())
    return true
end
```
-/
def redeliver {World Source Task Entry1 Entry2 EntryN : Type}
    [Monad (M World)] (tokenOps : TokenOps World Source)
    (runtime : CancellationRuntimeOps World Source Task Entry1 Entry2 EntryN)
    (cancelWalk : Source → U8 → M World Unit) (source : Source) : M World Bool := do
  let state ← tokenOps.atomicLoadState .acquire source
  if state.val == 0 then pure false
  else do
    cancelWalk source state
    runtime.atomicFenceHeavy
    runtime.shootdownCancelledTasks
    pure true

def popLast {α : Type} : List α → Option (List α × α)
  | [] => none
  | [value] => some ([], value)
  | head :: tail =>
      match popLast tail with
      | none => none
      | some (rest, value) => some (head :: rest, value)

/--
Julia source: base/cancellation.jl:723-735 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _cancel_walk!(src::CancellationTokenSource, sev::UInt8)
    # Iterative worklist (no recursion): a deep source chain must not
    # overflow the canceller's stack, and a reconverging ("linked") graph
    # must deliver at each node once, not once per path (deduplicated by the
    # visited set).
    visited = IdSet{CancellationTokenSource}()
    push!(visited, src)
    pending = CancellationTokenSource[src]
    while !isempty(pending)
        _cancel_walk_node!(pop!(pending), sev, pending, visited)
    end
    return nothing
end
```
-/
def cancelWalk {World Source : Type}
    [Monad (M World)] (nodeWalk : Source → U8 → List Source → List Source → M World (List Source × List Source))
    (source : Source) (severity : U8) : M World Unit := do
  let _ ← whileLoop (fun (pending, visited) => do
    match popLast pending with
    | none => pure (.inl ())
    | some (rest, node) => do
        let (nextPending, nextVisited) ← nodeWalk node severity rest visited
        pure (.inr (nextPending, nextVisited))) ([source], [source])
  pure ()

/--
Julia source: base/cancellation.jl:737-822 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Walk `node`'s waiter list under the walk lock: physically unlink the
# registrations of completed tasks and retired entries (the only removal in
# the registry - a live task's registration is sticky and stays linked
# between parks) and, when `sev` is nonzero, claim armed waiters eligible
# at that severity. Returns the claimed tasks as a cons list of
# `Pair{Tuple{Task, WaitEntry, UInt64}, Any}` cells (a Pair's declared
# parameters make every cell one type - a tuple cons would mint a fresh
# concrete tuple type per list depth); the caller wakes them after
# releasing the walk lock.
function _walk_waiters!(node::CancellationTokenSource, sev::UInt8)
    @atomic :monotonic node.dead_count = UInt32(0)
    nlive = UInt32(0)
    towake = nothing
    prev = nothing # the predecessor's slot for `node`, once past the head
    # seq_cst: the S-ordered counterpart of a registrant's seq_cst push -
    # a push this read misses is later in the total order, so that
    # registrant's state recheck observes the cancellation (see
    # `SourceWait`'s registration, base/park.jl); pairs with the seq_cst
    # state read the caller performed under the walk lock.
    x = @atomic :sequentially_consistent node.waiters_head
    w = x isa WaitEntry ? x : nothing
    while w isa WaitEntry
        wi = _find_slot(w, node)
        # a linked entry always has a slot for this source (its owner is
        # the membership witness, cleared only on unlink, under this lock);
        # bail out without touching the structure if that is ever violated
        wi == 0 && break
        slot = slots(w)[wi]
        wnext = slot.next
        t = @atomic :monotonic w.task
        if t === nothing || istaskdone(t)
            # Unlink. Interior links are rewritten only under the walk lock,
            # so they are plain stores; unlinking the head races concurrent
            # pushes and simply keeps the entry for the next walk when it
            # loses.
            unlinked = if prev === nothing
                (@atomicreplace :monotonic :monotonic node.waiters_head w => wnext).success
            else
                prev.next = wnext
                true
            end
            if unlinked
                # The slot `owner` is cleared last: it is the membership
                # witness whose clearing hands the (dead) slot back.
                slot.next = nothing
                t === nothing || (@atomic :monotonic w.task = nothing)
                slot.owner = nothing
            else
                prev = slot
            end
        else
            # Claim order: the armed check must come first - the slot's aux
            # (the minimum delivery severity) is only meaningful for the arm
            # it was staged for, and reading it after observing the arm pins
            # it to that arm or a later one. An arm this (seq_cst, pairing
            # with the source registration's re-arm fence) read misses
            # is covered by its own post-arm state recheck, so skipping it
            # here is sound. The claim CAS itself may still land on a
            # *later* arm of the same entry than the one whose aux was
            # judged - which is why every arm of a source-linked entry must
            # be a cancellable park under it (shields arm a distinct
            # entry; see _cached_wait_entry): the worst misfire is then a
            # spurious below-floor wake into a teardown re-park, which
            # handles it like any interruption of its wait
            # (conservatively, e.g. by detaching the awaited request).
            aux = slot.aux
            if sev != 0x00 && (@atomic :sequentially_consistent t.waiting_on) === w &&
                    aux % UInt8 <= sev
                if (@atomicreplace t.waiting_on w => nothing).success
                    towake = Pair{Tuple{Task, WaitEntry, UInt64}, Any}((t, w, aux), towake)
                end
                # a lost claim: a completion or interrupter won the race;
                # the waiter resumes through that wake
            end
            nlive += UInt32(1)
            prev = slot
        end
        w = wnext
    end
    # Resync the approximate list length (see _note_dead_registration!'s
    # scaled prune threshold) to what this walk left linked. Entries kept
    # only because their head-unlink CAS lost count as live: conservative,
    # and the next walk resyncs.
    @atomic :monotonic node.reg_count = nlive
    return towake
end
```
-/
def walkWaiters {World Source Task Value Lock Entry1 Entry2 EntryN : Type}
    [Monad (M World)] (waitOps : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (registry : RegistryOps World Source Task Lock Entry1 Entry2 EntryN)
    (node : Source) (severity : U8) : M World (List (Task × WaitEntry Entry1 Entry2 EntryN × U64)) := do
  registry.atomicStoreDeadCount node (JInt.lit .u32 0)
  let empty ← registry.waitersHead .sequentiallyConsistent node
  let (live, wakeups) ← whileLoop (fun (previous, current, nlive, towake) => do
    match current with
    | none => pure (.inl (nlive, towake))
    | some entry => do
        let nodeOwner := waitOps.sourceValue node
        let index ← entryFindSlot waitOps entry nodeOwner
        if index.val == 0 then pure (.inl (nlive, towake))
        else do
          let slot : WaitSlotRef Entry1 Entry2 EntryN :=
            @waitSlotsGetIndex Entry1 Entry2 EntryN
              (@slots Entry1 Entry2 EntryN entry) index
          let next ← entryNextAt waitOps entry index
          let task ← registry.taskOfEntry entry
          let unlinkDead := do
            let unlinked ← match previous with
              | none => registry.atomicReplaceWaitersHead .monotonic .monotonic node entry next
              | some prev => do
                  let _ ← entrySetNextAt waitOps prev.entry prev.index next
                  pure true
            if unlinked then do
              let _ ← entrySetNextAt waitOps entry index none
              match task with
              | none => pure ()
              | some _ => entrySetTask waitOps entry none
              let _ ← entrySetOwnerAt waitOps entry index waitOps.nothingValue
              pure (.inr (previous, next, nlive, towake))
            else
              pure (.inr (some slot, next, nlive, towake))
          match task with
          | none => unlinkDead
          | some task => do
              if ← registry.isTaskDone task then unlinkDead
              else do
                let aux ← entryAuxAt waitOps entry index
                if severity.val != 0 &&
                    (match ← registry.waitingOn task .sequentiallyConsistent with
                     | some waiting => registry.sameEntry waiting entry
                     | none => false) && aux.val % 256 ≤ severity.val then
                  let claimed ← waitOps.claimWaitingOn task entry
                  let nextWakeups := if claimed then (task, entry, aux) :: towake else towake
                  pure (.inr (some slot, next, JInt.wrap .u32 (nlive.val + 1), nextWakeups))
                else
                  pure (.inr (some slot, next, JInt.wrap .u32 (nlive.val + 1), towake)))
    (none, empty, JInt.lit .u32 0, [])
  registry.atomicStoreRegCount node live
  pure wakeups

/--
Julia source: base/cancellation.jl:824-888 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _cancel_walk_node!(node::CancellationTokenSource, sev::UInt8,
                            pending::Vector{CancellationTokenSource},
                            visited::IdSet{CancellationTokenSource})
    _lock_walk(node)
    # Deliver at least the node's current severity: a concurrent higher-
    # severity cancel! may have raised the state after this walk's own
    # transition, and its walk can run before this one takes the walk lock -
    # the claims below must then honor the escalated request. (Read under
    # the walk lock so the claim section cannot act on a stale, lower
    # severity.) seq_cst, matching the C-side propagate: when this walk's
    # own raise of the node was lost, this load is the walk's sole operation
    # on the state that can order the winner's write before the child_head
    # read below; it also pairs with the seq_cst push/arm-fence in
    # the source registration (state write before walk on this side, push
    # or arm before state recheck on the registrant's).
    st = @atomic :sequentially_consistent node.state
    sev < st && (sev = st)
    creq = CancellationRequest(sev)
    towake = _walk_waiters!(node, sev)
    # The actual wakes happen after the walk lock is released: holding it
    # across `schedule` would only stretch the window against concurrent
    # escalation walks. Claimed entries stay registered (sticky); the
    # claimed *waitee*-queue entry also stays linked, and the waiter's own
    # cleanup (or a later notify) lazily unlinks it.
    _unlock_walk(node)
    while towake !== nothing
        towake = towake::Pair{Tuple{Task, WaitEntry, UInt64}, Any}
        (t, w, aux) = towake.first
        towake = towake.second
        if aux & WAIT_AUX_WATCHER_BIT != 0x00
            # A watcher (`wait(::CancellationToken)`): this cancellation is
            # the event its wait completes on, so it is woken with the
            # request as a *value* - a watcher observes this source but
            # does not run under it.
            deliver_claimed_value_wake!(t, w, creq)
            continue
        end
        # N.B.: an ABANDON_ALL request also delivers by interruption for
        # now (freezing the task in place is not yet implemented). The
        # delivery is claim-scoped - the claim above is the wake ticket, so
        # no re-claiming swap - and dropped when the task has re-armed
        # meanwhile (see deliver_claimed_wake!).
        deliver_claimed_wake!(t, w, creq)
    end
    # Walk the node's (weak, intrusive) child list, advancing every child to
    # this severity and queueing the ones not yet visited (a reconverging
    # graph must deliver at each node once, not once per path). The seq_cst
    # `child_head` read below (paired with the seq_cst state access above)
    # closes the race against a concurrent attach: a child that this read
    # misses was published after our state write, so its constructor
    # observes that write and the child is born at (at least) this severity.
    # Children attached concurrently *during* the walk are prepended before
    # the list positions already traversed and are likewise born cancelled.
    c = @atomic node.child_head
    while c !== nothing
        c = c::CancellationTokenSource
        _raise_state!(c, sev)
        if !(c in visited)
            push!(visited, c)
            push!(pending, c)
        end
        c = _cancel_next_child(node, c)
    end
    return nothing
end
```
-/
def cancelWalkNode {World Source Task Value Lock Entry1 Entry2 EntryN : Type}
    [Monad (M World)] (tokenOps : TokenOps World Source)
    (waitOps : WaitEntryOps World Source Task Value Entry1 Entry2 EntryN)
    (registry : RegistryOps World Source Task Lock Entry1 Entry2 EntryN)
    (runtime : CancellationRuntimeOps World Source Task Entry1 Entry2 EntryN)
    (node : Source) (severity : U8) (pending visited : List Source) :
    M World (List Source × List Source) := do
  lockWalk registry node
  let state ← tokenOps.atomicLoadState .sequentiallyConsistent node
  let severity := if severity.val < state.val then state else severity
  let request : CancellationRequest := ⟨severity⟩
  let wakeups ← walkWaiters waitOps registry node severity
  unlockWalk registry node
  let _ ← whileLoop (fun wakes => do
    match wakes with
    | [] => pure (.inl ())
    | (task, entry, aux) :: rest => do
        if aux.val / 256 % 2 != 0 then
          runtime.deliverClaimedValueWake task entry request
        else
          runtime.deliverClaimedWake task entry request
        pure (.inr rest)) wakeups
  let firstChild ← registry.childHead .sequentiallyConsistent node
  let (pending, visited) ← whileLoop (fun (child, pending, visited) => do
    match child with
    | none => pure (.inl (pending, visited))
    | some child => do
        let _ ← raiseState tokenOps child severity
        let seen := visited.any (tokenOps.sameSource child)
        let pending := if seen then pending else pending ++ [child]
        let visited := if seen then visited else visited ++ [child]
        let next ← tokenOps.nextChild node child
        pure (.inr (next, pending, visited))) (firstChild, pending, visited)
  pure (pending, visited)

/--
Julia source: base/cancellation.jl:892-912 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# The slow path of `@cancel_check`: `st` is the (non-zero) status byte
# reported by the cancellation point.
@noinline function handle_cancellation!(src::Union{Nothing, CancellationTokenSource}, st::UInt8)
    ct = current_task()
    if st & STATUS_PREEMPT_BIT != 0x00
        # consume the cooperative-yield request
        @atomic :monotonic ct.preempt_request = 0x00
    end
    # Without a source the cancellation point never reports a severity, which also lets
    # inference drop the rest of this function for `src::Nothing`.
    if src === nothing || st & SEVERITY_MASK == 0x00
        # preempt-only (a pending yield request, or a preempt shootdown that
        # reset this point): let another task run, then resume
        yield()
        return nothing
    end
    # re-read: deliver the severity current at throw time, not the one the
    # fast path happened to observe
    st = @atomic :acquire src.state
    throw(CancellationRequest(st))
end
```
-/
def handleCancellation {World Source Task Entry1 Entry2 EntryN : Type}
    [Monad (M World)] (tokenOps : TokenOps World Source)
    (runtime : CancellationRuntimeOps World Source Task Entry1 Entry2 EntryN)
    (source : Option Source) (status : U8) : M World Unit := do
  let task ← runtime.currentTask
  if status.val / 64 % 2 != 0 then
    runtime.clearPreemptRequest task (JInt.lit .u8 0)
  if source.isNone || status.val % 64 == 0 then
    runtime.yield
  else
    match source with
    | none => pure ()
    | some source =>
        let current ← tokenOps.atomicLoadState .acquire source
        throw (.cancellationRequest current)

-- UNTRANSLATED
-- Source: base/cancellation.jl:947-963 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro cancel_check()
--     quote
--         # compiled cancellation points are also GC safepoints, so that a tight
--         # polling loop cannot starve a concurrent stop-the-world.
--         # The loop re-executes the point whenever the slow path returns (a
--         # preempt-only status yields and resumes): the slow-path call tears
--         # down the point's reset region, so passing the point again is what
--         # re-establishes it before the code the region is meant to cover.
--         local s = default_cancel_source()
--         while true
--             local st = Core.cancellation_point!(s)::UInt8
--             st == 0x00 && break
--             handle_cancellation!(s, st)
--         end
--         nothing
--     end
-- end
-- /Source
-- Reason: This macro constructs a compiler-managed cancellation-point region as Julia AST; the typed runtime model does not represent macro-expansion syntax.
-- UNTRANSLATED
-- Source: base/cancellation.jl:965-976 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro cancel_check(tok)
--     quote
--         local t = $(esc(tok))
--         local s = t === nothing ? nothing : (t::CancellationToken).source
--         while true
--             local st = Core.cancellation_point!(s)::UInt8
--             st == 0x00 && break
--             handle_cancellation!(s, st)
--         end
--         nothing
--     end
-- end
-- /Source
-- Reason: This macro constructs a compiler-managed cancellation-point region as Julia AST; the typed runtime model does not represent macro-expansion syntax.
/--
Julia source: base/cancellation.jl:978-988 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Throw the `CancellationRequest` if `src` is cancelled (level-triggered:
# no per-task state is consulted). Unlike `@cancel_check` this is not a
# compiled cancellation point (it opens no async-interruptible region).
# This is the entry check of every blocking API taking a `cancel` keyword
# argument: it must run *before* the operation has any side effects.
@inline function checkcancel(src::CancellationTokenSource)
    st = @atomic :monotonic src.state
    st == 0x00 && return nothing
    handle_cancellation!(src, st)
    return nothing
end
```
-/
def checkCancelSource {World Source : Type}
    [Monad (M World)] (tokenOps : TokenOps World Source)
    (handleCancellation : Option Source → U8 → M World Unit) (source : Source) : M World Unit := do
  let status ← tokenOps.atomicLoadState .monotonic source
  if status.val != 0 then handleCancellation (some source) status
  pure ()

/--
Julia source: base/cancellation.jl:989-989 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checkcancel(::Nothing) = nothing
```
-/
def checkCancelNone {World : Type} : M World Unit := pure ()

/--
Julia source: base/cancellation.jl:990-990 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checkcancel(tok::CancellationToken) = checkcancel(tok.source)
```
-/
def checkCancelToken {World Source : Type}
    [Monad (M World)] (tokenOps : TokenOps World Source)
    (handleCancellation : Option Source → U8 → M World Unit)
    (token : CancellationToken Source) : M World Unit :=
  checkCancelSource tokenOps handleCancellation token.source

/--
Julia source: base/cancellation.jl:993-1020 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
struct CancelTokenKey <: AbstractScopedValue{Union{Nothing, CancellationToken}} end

"""
    CANCEL_TOKEN

The scoped value carrying the [`CancellationToken`](@ref) that governs the
current dynamic extent, or `nothing` if there is none. [`@cancel_check`](@ref)
checks it, and tasks spawned within a scope inherit it.

Establish a governing token with the standard scoped-value API
([`ScopedValues.@with`](@ref) / [`ScopedValues.with`](@ref)):

```julia
using Base.ScopedValues

src = Base.CancellationTokenSource()
with(Base.CANCEL_TOKEN => Base.CancellationToken(src)) do
    ...   # cancellation points in here observe `cancel!(src)`
end
```

Scoping `Base.CANCEL_TOKEN => nothing` instead *shields* the enclosed code
from an outer (possibly cancelled) token; use this for cleanup that must
complete while the surrounding computation is being cancelled.

The current value can be read with `Base.CANCEL_TOKEN[]`.
"""
const CANCEL_TOKEN = CancelTokenKey()
````
-/
inductive CancelTokenKey where
  | key

def cancelTokenKey : CancelTokenKey := .key

/--
Julia source: base/cancellation.jl:1022-1041 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# The cancellation source a task inherited at birth: the CANCEL_TOKEN
# binding of the scope captured at its construction (`nothing` for tasks
# constructed outside any governing scope, or shielded with
# `CANCEL_TOKEN => nothing`). Subscriptions (`schedule_on_notify!`) are
# governed by this source: a task whose birth source is cancelled dies
# instead of starting.
function _birth_cancel_source(t::Task)
    # Raw field read: the `t.scope` property guard exists because a
    # *running* task swaps its scope as `with` blocks enter and exit -
    # racy to read from outside. Subscriptions enforce a never-started
    # waiter (see schedule_on_notify!), whose construction-time scope is
    # stable until its first schedule.
    scope = getfield(t, :scope)
    scope isa Scope || return nothing
    v = KeyValue.get(scope.values, CANCEL_TOKEN)
    v === nothing && return nothing
    tok = something(v)
    tok === nothing && return nothing
    return (tok::CancellationToken).source
end
```
-/
def birthCancelSource {World Source Task Scope : Type} [Monad (M World)]
    (ops : ScopeOps World Source Task Scope) (task : Task) : M World (Option Source) := do
  match ← ops.taskScope task with
  | none => pure none
  | some scope =>
      match ← ops.scopeCancelToken scope with
      | none => pure none
      | some none => pure none
      | some (some token) => pure (some token.source)

/--
Julia source: base/cancellation.jl:1043-1064 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# The scoped-default resolution, with a per-task cache: when the task's
# `bound_cancel_default` flag is set, `bound_cancel_token` holds the source
# this lookup would resolve to under the task's current scope (or `nothing`),
# placed there by the slow path below. The flag is dropped wherever a scope
# is installed (`with` enter and its inline exit) and by cancellation points
# publishing a different source, and travels with the token through the
# exception-handler and finalizer save/restore brackets, so a set flag
# always describes the current scope (see bound_cancel_default in
# src/julia_threads.h). Reconstructing the token from the cached source is
# exact: `CancellationToken` is an immutable wrapper, so the copy is egal to
# the token in the scope.
@inline function default_cancel_token()
    ct = current_task()
    if getfield(ct, :bound_cancel_default) !== 0x00
        # the field's declared type (Union{Nothing, CancellationTokenSource})
        # narrows through the `=== nothing` check without a type-tag load
        s = @atomic :monotonic ct.bound_cancel_token
        s === nothing && return nothing
        return CancellationToken(s)
    end
    return _default_cancel_token_slow(ct)
end
```
-/
def defaultCancelToken {World Source Task Scope : Type} [Monad (M World)]
    (ops : ScopeOps World Source Task Scope)
    (slow : Task → M World (Option (CancellationToken Source))) :
    M World (Option (CancellationToken Source)) := do
  let task ← ops.currentTask
  if (← ops.boundCancelDefault task).val != 0 then
    match ← ops.boundCancelToken task with
    | none => pure none
    | some source => pure (some ⟨source⟩)
  else
    slow task

/--
Julia source: base/cancellation.jl:1066-1082 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function _default_cancel_token_slow(ct::Task)
    tok = nothing
    scope = Core.current_scope()::Union{Scope, Nothing}
    if scope !== nothing
        v = KeyValue.get(scope.values, CANCEL_TOKEN)
        if v !== nothing
            tok = something(v)::Union{Nothing, CancellationToken}
        end
    end
    # Cache the resolution for the current scope. The store is an untagged
    # unsafe point for CancellationLowering, so it cannot break a published
    # reset region's (region, token) coherence: any live region is torn down
    # before the store and re-established at the next cancellation point.
    @atomic :monotonic ct.bound_cancel_token = tok === nothing ? nothing : tok.source
    setfield!(ct, :bound_cancel_default, 0x01)
    return tok
end
```
-/
def defaultCancelTokenSlow {World Source Task Scope : Type} [Monad (M World)]
    (ops : ScopeOps World Source Task Scope) (task : Task) :
    M World (Option (CancellationToken Source)) := do
  let mut token := none
  match ← ops.currentScope with
  | none => pure ()
  | some scope =>
      match ← ops.scopeCancelToken scope with
      | none => pure ()
      | some value => token := value
  let source := token.map CancellationToken.source
  ops.setBoundCancelToken task source
  ops.setBoundCancelDefault task (JInt.lit .u8 1)
  pure token

/--
Julia source: base/cancellation.jl:1084-1088 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function default_cancel_source()
    tok = default_cancel_token()
    tok === nothing && return nothing
    return (tok::CancellationToken).source
end
```
-/
def defaultCancelSource {World Source Task Scope : Type} [Monad (M World)]
    (ops : ScopeOps World Source Task Scope)
    (slow : Task → M World (Option (CancellationToken Source))) : M World (Option Source) := do
  pure ((← defaultCancelToken ops slow).map CancellationToken.source)

/--
Julia source: base/cancellation.jl:1092-1104 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# The sentinel default for `cancel` keyword arguments: "use the scoped
# default token". Resolution to a concrete token happens once, at the first
# potential-block point of an operation, so fast paths never pay for the
# scope lookup. `cancel = nothing` makes a wait explicitly non-cancellable.
#
# N.B.: a resolved token (`Union{Nothing, CancellationToken}`) is passed
# through *positional* arguments internally: passing the union as a keyword
# argument builds an abstractly-typed NamedTuple whose kwcall the optimizer
# cannot devirtualize (which, among other things, breaks `juliac --trim`).
struct UseDefaultToken end
const DEFAULT_CANCEL = UseDefaultToken()
const CancelTokenArg = Union{UseDefaultToken, CancellationToken, Nothing}
const MaybeToken = Union{Nothing, CancellationToken}
```
-/
inductive CancelTokenArg (Source : Type) where
  | useDefault
  | token (token : CancellationToken Source)
  | none

def defaultCancelArg {Source : Type} : CancelTokenArg Source := .useDefault

def MaybeToken (Source : Type) := Option (CancellationToken Source)

/--
Julia source: base/cancellation.jl:1106-1106 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline resolve_cancel_token(::UseDefaultToken) = default_cancel_token()
```
-/
def resolveCancelTokenDefault {World Source Task Scope : Type}
    [Monad (M World)] (ops : ScopeOps World Source Task Scope)
    (slow : Task → M World (Option (CancellationToken Source))) :
    M World (Option (CancellationToken Source)) :=
  defaultCancelToken ops slow

/--
Julia source: base/cancellation.jl:1107-1107 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline resolve_cancel_token(tok::Union{CancellationToken, Nothing}) = tok
```
-/
def resolveCancelTokenExplicit {Source : Type}
    (token : Option (CancellationToken Source)) : Option (CancellationToken Source) := token

/--
Julia source: base/cancellation.jl:1109-1110 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# The source of a resolved token (`nothing` stays `nothing`).
cancel_source(tok::CancellationToken) = tok.source
```
-/
def cancelSourceToken {Source : Type} (token : CancellationToken Source) : Source := token.source

/--
Julia source: base/cancellation.jl:1111-1111 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cancel_source(::Nothing) = nothing
```
-/
def cancelSourceNothing {Source : Type} : Option Source := none

/--
Julia source: base/cancellation.jl:1113-1120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# The entry check of a public API taking a `cancel` keyword argument:
# resolve the token and throw if it is already cancelled (uniformly
# level-triggered for the scoped default and explicit tokens alike).
@inline function check_cancel_arg(cancel::CancelTokenArg)
    tok = resolve_cancel_token(cancel)
    tok === nothing || checkcancel(tok.source)
    return tok
end
```
-/
def checkCancelArg {World Source Task Scope : Type}
    [Monad (M World)] (scopeOps : ScopeOps World Source Task Scope)
    (tokenOps : TokenOps World Source)
    (slow : Task → M World (Option (CancellationToken Source)))
    (handleCancellation : Option Source → U8 → M World Unit)
    (cancel : CancelTokenArg Source) : M World (Option (CancellationToken Source)) := do
  let token ← match cancel with
    | .useDefault => resolveCancelTokenDefault scopeOps slow
    | .token token => pure (resolveCancelTokenExplicit (some token))
    | .none => pure (resolveCancelTokenExplicit none)
  match token with
  | none => pure none
  | some token =>
      checkCancelSource tokenOps handleCancellation token.source
      pure (some token)

/--
Julia source: base/cancellation.jl:1122-1129 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# The lighter entry check for APIs with a non-blocking fast path: an
# explicitly passed token is resolved and checked (throwing when already
# cancelled) right here, while the scoped-default sentinel passes through
# untouched, deferring the scope lookup - and its (level-triggered) check -
# to the operation's first potential-block point, so fast paths pay neither.
# Spelled `cancel = precheck_cancel_arg(cancel)` at the top of such APIs.
@inline precheck_cancel_arg(cancel::CancelTokenArg) =
    cancel isa UseDefaultToken ? cancel : check_cancel_arg(cancel)
```
-/
def precheckCancelArg {World Source Task Scope : Type}
    [Monad (M World)] (scopeOps : ScopeOps World Source Task Scope)
    (tokenOps : TokenOps World Source)
    (slow : Task → M World (Option (CancellationToken Source)))
    (handleCancellation : Option Source → U8 → M World Unit)
    (cancel : CancelTokenArg Source) : M World (CancelTokenArg Source) := do
  match cancel with
  | .useDefault => pure .useDefault
  | _ =>
      match ← checkCancelArg scopeOps tokenOps slow handleCancellation cancel with
      | none => pure .none
      | some token => pure (.token token)

end JuliaLean.base.cancellation

namespace JuliaLean.Tasks



/-- CAS-max at `base/cancellation.jl:177-191`. The Boolean reports whether
the stored severity changed. Naturals represent the mathematical value of the
source's UInt8 state. -/
def raiseCancellation (old requested : Nat) : Bool × Nat :=
  if old ≥ requested then (false, old) else (true, requested)
def cancellationRun : List Nat → Nat → Nat
  | [], state => state
  | requested :: requests, state =>
      cancellationRun requests (raiseCancellation state requested).2

end JuliaLean.Tasks

namespace JuliaLean.Tasks



/-! ## base/cancellation.jl:102-191, token queries and source linkage -/

def cancellationSeverity (state : Nat) : Option Nat :=
  if state == 0 then none else some state

def cancellationIsCancelled (state : Nat) : Bool := state != 0

def uniqueParents (first : Nat) (rest : List Nat) : List Nat :=
  rest.foldl (fun parents parent => if parent ∈ parents then parents else parents ++ [parent]) [first]

/-! ## base/cancellation.jl:242-437, uniform WaitEntry slots -/

structure CoverageWaitSlot where
  owner : Option Nat := none
  next : Option Nat := none
  aux : Nat := 0
  deriving Repr, DecidableEq, Inhabited

structure CoverageWaitEntry where
  task : Option Nat
  slots : List CoverageWaitSlot
  deriving Repr, DecidableEq, Inhabited

def emptyWaitSlot : CoverageWaitSlot := ⟨none, none, 0⟩

def waitEntry (task : Option Nat) (slots : Nat) : CoverageWaitEntry :=
  ⟨task, List.replicate slots emptyWaitSlot⟩

def waitSlot (entry : CoverageWaitEntry) (index : Nat) : CoverageWaitSlot :=
  entry.slots.getD (index - 1) emptyWaitSlot

def setWaitSlot (entry : CoverageWaitEntry) (index : Nat) (slot : CoverageWaitSlot) :
    CoverageWaitEntry :=
  { entry with slots := entry.slots.set (index - 1) slot }

def findWaitSlotFrom (owner : Option Nat) : Nat → List CoverageWaitSlot → Nat
  | _, [] => 0
  | index, slot :: slots =>
      if slot.owner == owner then index else findWaitSlotFrom owner (index + 1) slots

def findWaitSlot (entry : CoverageWaitEntry) (owner : Option Nat) : Nat :=
  findWaitSlotFrom owner 1 entry.slots

def acquireWaitSlot (entry : CoverageWaitEntry) (owner : Nat) : Option CoverageWaitEntry :=
  let index := findWaitSlot entry none
  if index == 0 then none
  else some (setWaitSlot entry index { (waitSlot entry index) with owner := some owner })

def releaseWaitSlot (entry : CoverageWaitEntry) (index : Nat) : CoverageWaitEntry :=
  setWaitSlot entry index emptyWaitSlot

/-! ## base/cancellation.jl:452-523, cached entries, arming, and claims -/

structure WaitArm where
  entry : Option Nat := none
  armed : Bool := false
  deriving Repr, DecidableEq

def armWait (state : WaitArm) (entry : Nat) : Option WaitArm :=
  if state.armed then none else some ⟨some entry, true⟩

def claimWait (state : WaitArm) (entry : Nat) : Bool × WaitArm :=
  if state.armed && state.entry == some entry then (true, ⟨none, false⟩)
  else (false, state)

def cancelWaitEntrySlots (hasCached : Bool) : Nat := if hasCached then 2 else 2

/-! ## base/cancellation.jl:541-655, registration bookkeeping -/

structure RegistrationState where
  waiters : List Nat := []
  deadCount : Nat := 0
  deriving Repr, DecidableEq

def unregisterBody (state : RegistrationState) (waiter : Nat) : RegistrationState :=
  { waiters := state.waiters.erase waiter, deadCount := state.deadCount }

def retireBody (state : RegistrationState) (waiter : Nat) : RegistrationState :=
  { state with waiters := state.waiters.erase waiter }

def noteDeadBody (state : RegistrationState) : RegistrationState :=
  { state with deadCount := state.deadCount + 1 }

/-! ## base/cancellation.jl:681-912, cancellation delivery -/

def validCancellationSeverity (severity : Nat) : Bool :=
  severity == 1 || severity == 3 || severity == 4

def cancelBody (state severity : Nat) : Except Unit (Bool × Nat) :=
  if validCancellationSeverity severity then .ok (raiseCancellation state severity)
  else .error ()

def redeliverBody (state : Nat) : Bool := state != 0

def walkNodeBody (requested current : Nat) : Nat := max requested current

def handleCancellationBody (hasSource preempt : Bool) (status current : Nat) : Except Nat Unit :=
  if preempt && (!hasSource || status % 64 == 0) then .ok ()
  else if hasSource && status % 64 != 0 then .error current
  else .ok ()

/-! ## base/cancellation.jl:947-1129, checks and default token wrappers -/

inductive TokenArgument where | useDefault | none | token (source : Nat)
  deriving Repr, DecidableEq

def resolveToken (defaultSource : Option Nat) : TokenArgument → Option Nat
  | .useDefault => defaultSource
  | .none => none
  | .token source => some source

def cancelSource : TokenArgument → Option Nat
  | .token source => some source
  | _ => none

def checkCancelBody (source : Option Nat) (state : Nat) : Except Nat Unit :=
  match source with
  | none => .ok ()
  | some _ => if state == 0 then .ok () else .error state

end JuliaLean.Tasks
