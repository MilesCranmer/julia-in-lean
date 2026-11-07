import JuliaLean.Proofs.base.locks_mt.common
import JuliaLean.Core
import JuliaLean.base.io
import JuliaLean.base.int

/-!
# Model of `base/park.jl`

The parked-wait driver of Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`: wait-entry acquisition,
`park!`/`repark!`, `wait_safe_interrupt`, `withdraw!`, the interrupted-wait cleanup, and the
`SourceWait`/`WatcherWait` waitables of a cancellation source, with `wait(::CancellationToken)`.
A park's waitables are a list, kept as a `Tuple` or another iterable to select the methods
Julia's dispatch picks. Waitables of other kinds dispatch to their own `wait_enqueue!`,
`wait_recheck` and `wait_dequeue!` methods, given as typed parameters. Tasks, wait entries and
cancellation sources are references into the mutable world, read and written through typed
accessors that carry the source's atomic ordering; the scheduler's `wait()` and the entry and
slot primitives of other files are typed parameters with no assumed laws.
-/

namespace JuliaLean.base.park

open JuliaLean
open JuliaLean.base.io (M Error CancelArg whileLoop)

abbrev U8 := JInt .u8
abbrev U32 := JInt .u32
abbrev U64 := JInt .u64

/-- A memory ordering of an atomic access. -/
inductive Ordering where
  | plain
  | monotonic
  | acquire
  | sequentially_consistent
  deriving DecidableEq, Repr

/-- A waitable in a park: a `SourceWait`, a `WatcherWait`, or a waitable of another kind `X`. -/
inductive Waitable (Src X : Type) where
  | source (src : Src) (floor : U8)
  | watcher (src : Src) (floor : U8)
  | other (x : X)

/-- A park's waitables, as a `Tuple` or as another iterable. -/
inductive Waitables (Src X : Type) where
  | tuple (ws : List (Waitable Src X))
  | iterable (ws : List (Waitable Src X))

def Waitables.items {Src X : Type} : Waitables Src X → List (Waitable Src X)
  | .tuple ws => ws
  | .iterable ws => ws

/-- The waitable protocol methods of the other kinds of waitables. -/
structure Protocol (World X Entry : Type) where
  enqueue : X → Entry → Bool → M World Bool
  /-- A `wait_recheck` method of another file, or `none` for the vacuous default. -/
  recheck : X → Option (Entry → M World Bool)
  dequeue : X → Entry → U8 → M World Unit

/-- Task and wait-entry fields and primitives. -/
structure Tasks (World Task Entry Queue Value : Type) where
  currentTask : M World Task
  sameEntry : Entry → Entry → Bool
  cachedWaitEntry : Task → M World (Option Entry)
  setCachedWaitEntry : Task → Option Entry → M World Unit
  cachedCancelEntry : Task → M World (Option Entry)
  setCachedCancelEntry : Task → Option Entry → M World Unit
  /-- `(@atomicreplace ct.waiting_on w => nothing).success`. -/
  replaceWaitingOn : Task → Entry → M World Bool
  /-- `@atomic :monotonic w.task`, `none` for `nothing`. -/
  entryTask : Entry → M World (Option Task)
  retireCancellationEntry : Entry → M World Unit
  armWait : Task → Entry → M World Unit
  /-- `wait()`: suspend until scheduled, returning the wake's payload. -/
  waitScheduler : M World Value
  queue : Task → M World (Option Queue)
  listDeletefirst : Queue → Task → M World Unit

/-- Cancellation sources `Src`, their registration lists and their requests `Req`. -/
structure Sources (World Task Entry Src Slot Token Req : Type) where
  sameSource : Src → Src → Bool
  /-- `_cached_wait_entry(ct)`, `_cancel_wait_entry(ct, src, floor)`, `WaitEntryN(ct, n)`,
  `WaitEntry1(ct)` and `WaitEntry2(ct)`. -/
  cachedWaitEntryFor : Task → M World Entry
  cancelWaitEntry : Task → Src → U8 → M World Entry
  waitEntryN : Task → Nat → M World Entry
  waitEntry1 : Task → M World Entry
  waitEntry2 : Task → M World Entry
  findSlot : Entry → Src → M World Int
  acquireSlot : Entry → Src → M World Int
  setSlotAux : Entry → Int → U64 → M World Unit
  /-- `slots(w)[i]`. -/
  slot : Entry → Int → M World Slot
  setSlotNext : Slot → Option Entry → M World Unit
  waitersHead : Src → M World (Option Entry)
  /-- `(@atomicreplace :sequentially_consistent :monotonic src.waiters_head h => w).success`. -/
  replaceWaitersHead : Src → Option Entry → Entry → M World Bool
  /-- `@atomic :monotonic src.reg_count += UInt32(1)`. -/
  incrementRegCount : Src → M World Unit
  /-- `Core.Intrinsics.atomic_fence(:sequentially_consistent, :system)`. -/
  fence : M World Unit
  state : Src → Ordering → M World U8
  /-- `tok.source` and `resolve_cancel_token(cancel)`. -/
  tokenSource : Token → Src
  resolveCancelToken : CancelArg Token → M World (Option Token)
  checkcancel : Src → M World Unit
  /-- `CancellationRequest(st)`, and a scheduler payload as a `CancellationRequest`. -/
  request : U8 → Req
  asRequest : {Value : Type} → Value → M World Req
  /-- `CANCEL_REQUEST_SAFE.request` and `WAIT_AUX_WATCHER_BIT`. -/
  cancelRequestSafe : U8
  waitAuxWatcherBit : U64

section
variable {World Task Entry Queue Value Src Slot Token Req X : Type}
variable (p : Protocol World X Entry) (t : Tasks World Task Entry Queue Value)
  (s : Sources World Task Entry Src Slot Token Req)

def capture {A : Type} (action : M World A) : M World (Except Error A) :=
  tryCatch (do pure (.ok (← action))) (fun error => pure (.error error))

def maxU8 (a b : U8) : U8 := if a.val ≥ b.val then a else b

-- Reason: The design comment of the driver has no method.
-- UNTRANSLATED
-- Source: base/park.jl:1-52 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- ## The parked-wait driver
-- #
-- # Every parked wait proceeds in six phases, uniformly over the set of
-- # things it waits for:
-- #
-- #   1. CHECK    the caller's fast-path satisfaction tests - no allocation,
-- #               no publication (stays at the call sites).
-- #   2. ENTRY    allocate the wait entry or reuse the task's cached one;
-- #               stage per-slot aux (severity floors) that the claim side
-- #               may read through an already-linked entry.
-- #   3. ARM      publish the entry as the task's sole claimable
-- #               registration: CAS(t.waiting_on, nothing => w).
-- #   4. ENQUEUE  register the entry with every waitable, each under that
-- #               waitable's own protection discipline.
-- #   5. RECHECK  re-test satisfaction where the enqueue could have raced
-- #               the firing; on a hit, self-claim: won => withdraw and
-- #               return (or deliver the refusal); lost => a waker owns our
-- #               wake - suspend and consume it.
-- #   6. SUSPEND  release the locks that must not be held while parked,
-- #               `wait()`, then reacquire per policy and settle.
-- #
-- # A *waitable* is the identity a slot's `owner` records. The waitable
-- # protocol is ordinary generic functions - the set is open; each call
-- # site's concrete container type carries the dispatch:
-- #
-- #   wait_enqueue!(x, w, first) -> Bool   phase 4, under x's discipline;
-- #                                        false = x already fired and
-- #                                        declined (one-shot waitables)
-- #   wait_recheck(x, w) -> Bool           phase 5, after ALL enqueues;
-- #                                        vacuous default
-- #   wait_dequeue!(x, w, why) -> Nothing  withdraw x's slot. Lock
-- #                                        discipline is per `why`: on
-- #                                        WAKE_VALUE/WAKE_FIRED the caller
-- #                                        holds the kind's protection; on
-- #                                        WAKE_INTERRUPTED/WAKE_WITHDRAWN
-- #                                        the method takes it itself
-- #
-- # The driver takes and releases no locks: lock choreography is plain
-- # caller code (`unlockall`/`relockall` around `wait_safe_interrupt`,
-- # `iolock_end`/`iolock_begin` at the uv sites, ...), so there is no
-- # release/reacquire protocol and no relock policy.
-- #
-- # Lock rule: from phase 3 on the entry is the task's armed registration,
-- # so a lock acquisition *inside* phase 4 must never park (a nested park
-- # would try to arm a second registration). Parking locks must be
-- # caller-held before `park!` begins (the `wait(c)` contract); locks a
-- # `wait_enqueue!` method takes itself must be spin locks. The cleanup's
-- # reacquire is exempt: it runs disarmed and may itself park with a fresh
-- # entry (the cache-blank dance below exists for exactly that).
-- 
-- /Source

/--
Julia source: base/park.jl:53-58 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# why-codes for wait_dequeue!
const WAKE_VALUE       = 0x00  # normal wake consumed (lazy settle)
const WAKE_FIRED       = 0x01  # fired; self-claim won; no suspend
const WAKE_INTERRUPTED = 0x03  # exceptional wake (cleanup path)
const WAKE_WITHDRAWN   = 0x04  # withdraw! - the caller is done waiting

```
-/
def WAKE_VALUE : U8 := JInt.lit .u8 0x00
def WAKE_FIRED : U8 := JInt.lit .u8 0x01
def WAKE_INTERRUPTED : U8 := JInt.lit .u8 0x03
def WAKE_WITHDRAWN : U8 := JInt.lit .u8 0x04

-- Reason: `function wait_enqueue! end` and `function wait_dequeue! end` declare generic functions with no methods; the methods are the protocol dispatch below.
-- UNTRANSLATED
-- Source: base/park.jl:59-60 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function wait_enqueue! end
-- function wait_dequeue! end
-- /Source

/--
Julia source: base/park.jl:61-62 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
wait_recheck(@nospecialize(x), w::WaitEntry) = false

```
-/
def wait_recheck_default (_w : Entry) : M World Bool := pure false

/--
Julia source: base/park.jl:63-68 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Lock acquisition for self-protecting `wait_dequeue!` methods (the
# cleanup/withdraw paths): must not observe cancellation - the cleanup
# may be unwinding the very CancellationRequest a cancellable acquire
# would rethrow. The `ReentrantLock` method (lock.jl) shields itself.
_uncancellable_lock(l) = lock(l)

```
-/
def uncancellable_lock {L : Type} (lock : L → M World Unit) (l : L) : M World Unit := lock l

/--
Julia source: base/park.jl:69-82 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
## The cancellation source as a waitable
#
# `SourceWait(src, floor)` in a park's waitables makes the wait
# cancellable under `src` at severities >= `floor`: its enqueue is the
# sticky lock-free registration, its recheck is the seq_cst state read
# closing the arm-vs-cancel race (a Dekker - both sides need their
# seq_cst upgrade), and its fired outcome throws the refusal.
# Registrations are sticky: no dequeue on any path - collection is the
# walk's job (prune/dead accounting).
struct SourceWait
    src::CancellationTokenSource
    floor::UInt8
end

```
-/
-- `SourceWait(src, floor)` is the `Waitable.source` constructor.
def SourceWait (src : Src) (floor : U8) : Waitable Src X := .source src floor

/--
Julia source: base/park.jl:303-338 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
## SourceWait methods (the struct and its doc live above, before the
## entry-acquisition contract that dispatches on it)

function _source_wait_enqueue!(src::CancellationTokenSource, w::WaitEntry, aux::UInt64)
    i = _find_slot(w, src)
    if i == 0
        # First registration under `src`: claim a slot (the slot's `owner`
        # is the push ticket) and stage the aux (the floor, plus the
        # watcher bit for a `WatcherWait`) - pre-publication, so any walk
        # that can see the slot sees its aux - then publish with a
        # lock-free push. seq_cst, pairing with the cancellation walk's
        # state-write-then-head-read: if the walk's head read misses this
        # push, this push is later in the total order, so the recheck
        # below observes the raised state.
        i = _acquire_slot!(w, src)
        _set_slot_aux!(w, i, aux)
        slot = slots(w)[i]
        while true
            h = _waiters_head(src)
            slot.next = h
            if (@atomicreplace :sequentially_consistent :monotonic src.waiters_head h => w).success
                break
            end
        end
        # approximate list length, feeding the scaled prune threshold
        # (resynced by every walk; see _note_dead_registration!)
        @atomic :monotonic src.reg_count += UInt32(1)
    else
        # Sticky re-arm (already registered): upgrade this thread's
        # arm-then-recheck to the store-load ordering the race argument
        # needs (the arm CAS itself is only `release`).
        Core.Intrinsics.atomic_fence(:sequentially_consistent, :system)
    end
    return true
end

```
-/
def source_wait_enqueue (src : Src) (w : Entry) (aux : U64) : M World Bool := do
  let i ← s.findSlot w src
  if i == 0 then
    let i ← s.acquireSlot w src
    s.setSlotAux w i aux
    let slot ← s.slot w i
    whileLoop (fun (_ : Unit) => do
      let h ← s.waitersHead src
      s.setSlotNext slot h
      if ← s.replaceWaitersHead src h w then return .inl ()
      return .inr ()) ()
    s.incrementRegCount src
  else
    s.fence
  return true

/--
Julia source: base/park.jl:339-341 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
wait_enqueue!(x::SourceWait, w::WaitEntry, first::Bool) =
    _source_wait_enqueue!(x.src, w, UInt64(x.floor))

```
-/
def wait_enqueue_source (src : Src) (floor : U8) (w : Entry) (_first : Bool) : M World Bool :=
  source_wait_enqueue s src w (JInt.wrap .u64 floor.val)

/--
Julia source: base/park.jl:342-348 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function wait_recheck(x::SourceWait, w::WaitEntry)
    # Post-publication recheck: either the concurrent cancellation walk
    # observes our push/arm, or we observe its state write here.
    st = @atomic :sequentially_consistent x.src.state
    return st != 0x00 && st >= x.floor
end

```
-/
def wait_recheck_source (src : Src) (floor : U8) (_w : Entry) : M World Bool := do
  let st ← s.state src .sequentially_consistent
  return st.val != 0 && st.val ≥ floor.val

/--
Julia source: base/park.jl:349-350 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
wait_dequeue!(x::SourceWait, w::WaitEntry, why::UInt8) = nothing

```
-/
def wait_dequeue_source (_src : Src) (_floor : U8) (_w : Entry) (_why : U8) : M World Unit := pure ()

/--
Julia source: base/park.jl:351-369 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
## Watching a cancellation source (`wait(::CancellationToken)`)

# `WatcherWait(src)` in a park's waitables makes the wait *complete* when
# `src` is cancelled: its slot stages the watcher aux bit, which the
# cancellation walk delivers value-mode - the request is the payload, at
# any severity (see `_cancel_walk_node!`).
# The registration and recheck follow `SourceWait`'s Dekker exactly; only
# the staged aux and the meaning of firing (the awaited event, not a
# refusal) differ. Watcher parks always use a fresh single-use entry:
# neither cache slot may ever carry a registration on a source the arm is
# not an ordinary cancellable park under (the shield/claim soundness
# argument in the cache contract above).
struct WatcherWait
    src::CancellationTokenSource
    # The lowest severity that fires this watcher (inclusive; normalized to
    # at least SAFE). Non-throwing teardown waits re-park with the
    # acknowledged severity's successor, so only an escalation wakes them.
    floor::UInt8
end
```
-/
-- `WatcherWait(src, floor)` is the `Waitable.watcher` constructor.
def WatcherWait (src : Src) (floor : U8) : Waitable Src X := .watcher src floor

/--
Julia source: base/park.jl:370-371 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
WatcherWait(src::CancellationTokenSource) = WatcherWait(src, CANCEL_REQUEST_SAFE.request)

```
-/
def WatcherWaitDefault (src : Src) : Waitable Src X := .watcher src s.cancelRequestSafe

/--
Julia source: base/park.jl:374-378 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

wait_enqueue!(x::WatcherWait, w::WaitEntry, first::Bool) =
    _source_wait_enqueue!(x.src, w,
        WAIT_AUX_WATCHER_BIT | UInt64(max(x.floor, CANCEL_REQUEST_SAFE.request)))

```
-/
def wait_enqueue_watcher (src : Src) (floor : U8) (w : Entry) (_first : Bool) : M World Bool :=
  source_wait_enqueue s src w (JuliaLean.base.int.or_int s.waitAuxWatcherBit
    (JInt.wrap .u64 (maxU8 floor s.cancelRequestSafe).val))

/--
Julia source: base/park.jl:379-381 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
wait_recheck(x::WatcherWait, w::WaitEntry) =
    (@atomic :sequentially_consistent x.src.state) >= max(x.floor, CANCEL_REQUEST_SAFE.request)

```
-/
def wait_recheck_watcher (src : Src) (floor : U8) (_w : Entry) : M World Bool := do
  return (← s.state src .sequentially_consistent).val ≥ (maxU8 floor s.cancelRequestSafe).val

/--
Julia source: base/park.jl:382-383 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
wait_dequeue!(x::WatcherWait, w::WaitEntry, why::UInt8) = nothing

```
-/
def wait_dequeue_watcher (_src : Src) (_floor : U8) (_w : Entry) (_why : U8) : M World Unit := pure ()

/-- `wait_enqueue!`, `wait_recheck` and `wait_dequeue!` as dispatched on a waitable. -/
def wait_enqueue (x : Waitable Src X) (w : Entry) (first : Bool) : M World Bool :=
  match x with
  | .source src floor => wait_enqueue_source s src floor w first
  | .watcher src floor => wait_enqueue_watcher s src floor w first
  | .other x => p.enqueue x w first

def wait_recheck (x : Waitable Src X) (w : Entry) : M World Bool :=
  match x with
  | .source src floor => wait_recheck_source s src floor w
  | .watcher src floor => wait_recheck_watcher s src floor w
  | .other x =>
    match p.recheck x with
    | some recheck => recheck w
    | none => wait_recheck_default w

def wait_dequeue (x : Waitable Src X) (w : Entry) (why : U8) : M World Unit :=
  match x with
  | .source src floor => wait_dequeue_source src floor w why
  | .watcher src floor => wait_dequeue_watcher src floor w why
  | .other x => p.dequeue x w why

/--
Julia source: base/park.jl:83-94 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
## Entry acquisition - the cache contract
#
# The two canonical tuple shapes are served from the task's caches; any
# other iterable gets a fresh, single-use entry. Freshness is what makes
# specific-wait wakers (a timeout's expected-entry CAS) safe: entry
# identity scopes a claim to this wait - the same principle that gives
# shielded parks a distinct entry from cancellable ones.
acquire_wait_entry!(ct::Task, ws::Tuple{Any}) = _cached_wait_entry(ct)
acquire_wait_entry!(ct::Task, ws::Tuple{Any, SourceWait}) =
    _cancel_wait_entry(ct, ws[2].src, ws[2].floor)
acquire_wait_entry!(ct::Task, ws) = WaitEntryN(ct, length(ws))

```
-/
def acquire_wait_entry (ct : Task) (ws : Waitables Src X) : M World Entry :=
  match ws with
  | .tuple [.watcher _ _] => s.waitEntry1 ct
  | .tuple [.watcher _ _, .source _ _] => s.waitEntry2 ct
  | .tuple [_] => s.cachedWaitEntryFor ct
  | .tuple [_, .source src floor] => s.cancelWaitEntry ct src floor
  | ws => s.waitEntryN ct ws.items.length

/-- `x === y` on optional entries. -/
def sameOptEntry (x : Option Entry) (w : Entry) : Bool :=
  match x with
  | some x => t.sameEntry x w
  | none => false

/--
Julia source: base/park.jl:95-104 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Retire a fresh (uncached) entry that is done waiting: its sticky source
# registrations become prunable corpses. Cached entries stay live.
function release_wait_entry!(ct::Task, w::WaitEntry)
    (w === ct.cached_wait_entry || w === ct.cached_cancel_entry) && return nothing
    # idempotent: several exits may withdraw the same fresh entry
    (@atomic :monotonic w.task) === nothing && return nothing
    retire_cancellation_entry!(w)
    return nothing
end

```
-/
def release_wait_entry (ct : Task) (w : Entry) : M World Unit := do
  if sameOptEntry t (← t.cachedWaitEntry ct) w || sameOptEntry t (← t.cachedCancelEntry ct) w then
    return
  if (← t.entryTask w).isNone then return
  t.retireCancellationEntry w

/--
Julia source: base/park.jl:105-107 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Self-claim: take back the wake of our own armed registration.
disarm!(ct::Task, w::WaitEntry) = (@atomicreplace ct.waiting_on w => nothing).success

```
-/
def disarm (ct : Task) (w : Entry) : M World Bool := t.replaceWaitingOn ct w

/--
Julia source: base/park.jl:144-157 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Per-waitable phases. Unrolled by tuple recursion: a generic `for x in ws`
# loop would re-box every element through its dynamic tuple index.
@inline _enqueue_until_fired(ws::Tuple{}, w::WaitEntry, first::Bool) = nothing
@inline function _enqueue_until_fired(ws::Tuple, w::WaitEntry, first::Bool)
    x = ws[1]
    wait_enqueue!(x, w, first) || return x
    return _enqueue_until_fired(tail(ws), w, first)
end
@inline function _enqueue_until_fired(ws, w::WaitEntry, first::Bool)
    for x in ws
        wait_enqueue!(x, w, first) || return x
    end
    return nothing
end
```
-/
def enqueue_until_fired_tuple : List (Waitable Src X) → Entry → Bool → M World (Option (Waitable Src X))
  | [], _, _ => pure none
  | x :: rest, w, first => do
    if !(← wait_enqueue p s x w first) then return some x
    enqueue_until_fired_tuple rest w first

def enqueue_until_fired_iterable (ws : List (Waitable Src X)) (w : Entry) (first : Bool) :
    M World (Option (Waitable Src X)) := do
  for x in ws do
    if !(← wait_enqueue p s x w first) then return some x
  return none

def enqueue_until_fired (ws : Waitables Src X) (w : Entry) (first : Bool) :
    M World (Option (Waitable Src X)) :=
  match ws with
  | .tuple ws => enqueue_until_fired_tuple p s ws w first
  | .iterable ws => enqueue_until_fired_iterable p s ws w first

/--
Julia source: base/park.jl:158-169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _recheck_until_fired(ws::Tuple{}, w::WaitEntry) = nothing
@inline function _recheck_until_fired(ws::Tuple, w::WaitEntry)
    x = ws[1]
    wait_recheck(x, w) && return x
    return _recheck_until_fired(tail(ws), w)
end
@inline function _recheck_until_fired(ws, w::WaitEntry)
    for x in ws
        wait_recheck(x, w) && return x
    end
    return nothing
end
```
-/
def recheck_until_fired_tuple : List (Waitable Src X) → Entry → M World (Option (Waitable Src X))
  | [], _ => pure none
  | x :: rest, w => do
    if ← wait_recheck p s x w then return some x
    recheck_until_fired_tuple rest w

def recheck_until_fired_iterable (ws : List (Waitable Src X)) (w : Entry) :
    M World (Option (Waitable Src X)) := do
  for x in ws do
    if ← wait_recheck p s x w then return some x
  return none

def recheck_until_fired (ws : Waitables Src X) (w : Entry) : M World (Option (Waitable Src X)) :=
  match ws with
  | .tuple ws => recheck_until_fired_tuple p s ws w
  | .iterable ws => recheck_until_fired_iterable p s ws w

/--
Julia source: base/park.jl:170-181 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _dequeue_each!(ws::Tuple{}, w::WaitEntry, why::UInt8) = nothing
@inline function _dequeue_each!(ws::Tuple, w::WaitEntry, why::UInt8)
    wait_dequeue!(ws[1], w, why)
    return _dequeue_each!(tail(ws), w, why)
end
@inline function _dequeue_each!(ws, w::WaitEntry, why::UInt8)
    for x in ws
        wait_dequeue!(x, w, why)
    end
    return nothing
end

```
-/
def dequeue_each_tuple : List (Waitable Src X) → Entry → U8 → M World Unit
  | [], _, _ => pure ()
  | x :: rest, w, why => do
    wait_dequeue p x w why
    dequeue_each_tuple rest w why

def dequeue_each_iterable (ws : List (Waitable Src X)) (w : Entry) (why : U8) : M World Unit := do
  for x in ws do
    wait_dequeue p x w why

def dequeue_each (ws : Waitables Src X) (w : Entry) (why : U8) : M World Unit :=
  match ws with
  | .tuple ws => dequeue_each_tuple p ws w why
  | .iterable ws => dequeue_each_iterable p ws w why

/--
Julia source: base/park.jl:108-143 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
## The verbs

"""
    park!(ws, w::WaitEntry, first::Bool) -> Bool

Phases 3-5 of the protocol over the flat waitable iterable `ws`: arm
`w`, enqueue it with every waitable, and run the rechecks. Returns
`true` when the task is parked - a wake is (or will be) in flight, and
the caller must suspend through [`wait_safe_interrupt`](@ref) to consume
it. Returns `false` when a waitable fired and the self-claim won:
nothing is in flight, and the caller owns the outcome (for a fired
source, re-checking cancellation - `checkcancel` - throws the refusal
exactly like the entry check) as well as every remaining registration
(usually `withdraw!(ws, w, WAKE_FIRED)` under its still-held locks). A
fired recheck whose self-claim *loses* returns `true`: the concurrent
claimer's wake delivers the outcome.

The driver takes and releases no locks: protection the caller holds is
held throughout - which is what makes the enqueue/recheck window sound -
and lock choreography around the suspend is plain caller code. The one
dequeue the driver performs itself is the *fired slot* on the `false`
path (self-protecting; a done-but-still-linked predicate would re-fire
on every `repark!` until its notify drains).
"""
function park!(ws, w::WaitEntry, first::Bool)
    ct = current_task()
    _arm_wait(ct, w)                                     # 3
    fx = _enqueue_until_fired(ws, w, first)              # 4
    fx === nothing && (fx = _recheck_until_fired(ws, w)) # 5
    if fx !== nothing && disarm!(ct, w)
        wait_dequeue!(fx, w, WAKE_FIRED)
        return false
    end
    return true
end

```
-/
def park (ws : Waitables Src X) (w : Entry) (first : Bool) : M World Bool := do
  let ct ← t.currentTask
  t.armWait ct w
  let mut fx ← enqueue_until_fired p s ws w first
  if fx.isNone then fx ← recheck_until_fired p s ws w
  match fx with
  | some x =>
    if ← disarm t ct w then
      wait_dequeue p x w WAKE_FIRED
      return false
    return true
  | none => return true

/--
Julia source: base/park.jl:182-201 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    repark!(ws, w::WaitEntry) -> Bool

Re-arm and recheck `w`, with the same `Bool` contract as [`park!`](@ref).
The caller must ensure every pending waitable is still registered and its
recheck observes notifications delivered while `w` was unarmed. `DoneWait`
does not satisfy this contract: notification removes the slot required by
its recheck. Multi-task waits must enqueue pending tasks with [`park!`](@ref).
"""
function repark!(ws, w::WaitEntry)
    ct = current_task()
    _arm_wait(ct, w)
    fx = _recheck_until_fired(ws, w)
    if fx !== nothing && disarm!(ct, w)
        wait_dequeue!(fx, w, WAKE_FIRED)
        return false
    end
    return true
end

```
-/
def repark (ws : Waitables Src X) (w : Entry) : M World Bool := do
  let ct ← t.currentTask
  t.armWait ct w
  match ← recheck_until_fired p s ws w with
  | some x =>
    if ← disarm t ct w then
      wait_dequeue p x w WAKE_FIRED
      return false
    return true
  | none => return true

/--
Julia source: base/park.jl:253-302 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# The interrupted-wait cleanup (see wait_safe_interrupt). In order:
#  1. Disarm the registration - before any reacquire below can register a
#     new wait. When the disarm loses, a claimer got the wake: its
#     schedule is either already enqueued or still in flight under the
#     waitee's protection.
#  2. Blank the entry's cache slot: a notifier may have popped the stale
#     entry without scheduling us and may still retain its identity for
#     the wake-claim CAS, so `w` must not be reused (e.g. by a park
#     inside a self-protecting dequeue's lock acquire) before the
#     unlinks below.
#  3. Withdraw every registration through its kind's self-protecting
#     dequeue; the per-kind lock round-trips serialize any claimer's
#     in-flight schedule ...
#  4. ... which is what makes the pending-wake drop here deterministic:
#     a wake claimed-and-enqueued by such a claimer must not leak into
#     this task's next wait. (A claim-less raw wake delivered outside any
#     lock - the documented-unsafe `schedule(t, exc, error=true)` of a
#     running task - can still land after this drop; that hazard is the
#     primitive's, not this path's.)
#  5. Restore `w` to its cache slot unless a nested park cached a
#     replacement - then `w` is unreachable garbage (unarmed, off every
#     waitq), so retire it; fresh entries are always retired.
function interrupted_park_cleanup!(ct::Task, ws, w::WaitEntry)
    @atomicreplace ct.waiting_on w => nothing
    was_plain = ct.cached_wait_entry === w
    was_cancel = !was_plain && ct.cached_cancel_entry === w
    was_plain && (ct.cached_wait_entry = nothing)
    was_cancel && (ct.cached_cancel_entry = nothing)
    _dequeue_each!(ws, w, WAKE_INTERRUPTED)
    q = ct.queue
    q === nothing || list_deletefirst!(q::StickyWorkqueue, ct)
    if was_plain
        if ct.cached_wait_entry === nothing
            ct.cached_wait_entry = w
        else
            retire_cancellation_entry!(w)
        end
    elseif was_cancel
        if ct.cached_cancel_entry === nothing
            ct.cached_cancel_entry = w
        else
            retire_cancellation_entry!(w)
        end
    else
        release_wait_entry!(ct, w)
    end
    return nothing
end

```
-/
def interrupted_park_cleanup (ct : Task) (ws : Waitables Src X) (w : Entry) : M World Unit := do
  let _ ← t.replaceWaitingOn ct w
  let was_plain := sameOptEntry t (← t.cachedWaitEntry ct) w
  let was_cancel := !was_plain && sameOptEntry t (← t.cachedCancelEntry ct) w
  if was_plain then t.setCachedWaitEntry ct none
  if was_cancel then t.setCachedCancelEntry ct none
  dequeue_each p ws w WAKE_INTERRUPTED
  match ← t.queue ct with
  | none => pure ()
  | some q => t.listDeletefirst q ct
  if was_plain then
    if (← t.cachedWaitEntry ct).isNone then t.setCachedWaitEntry ct (some w)
    else t.retireCancellationEntry w
  else if was_cancel then
    if (← t.cachedCancelEntry ct).isNone then t.setCachedCancelEntry ct (some w)
    else t.retireCancellationEntry w
  else
    release_wait_entry t ct w

/--
Julia source: base/park.jl:202-238 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    wait_safe_interrupt(ws, w::WaitEntry)

Phase 6: suspend and consume exactly one wake of the park `park!`
armed, returning its payload. This is the only legal way to suspend on
an armed park - a raw `wait()` would miss the interrupted-wait cleanup.
The caller must have released any parking locks it holds (plain caller
code, e.g. `unlockall`); on a normal wake it returns with no locks
touched, and the caller reacquires per its own contract.

On an exceptional resume (an interrupter's claim, a delivered
cancellation, a raw `throwto`) the cleanup runs here, then the exception
propagates: disarm; blank the entry's cache slot; withdraw every
registration through its kind's *self-protecting* dequeue - each takes
its own lock, and those round-trips serialize any claimer's in-flight
schedule - and only then drop a claimed-and-enqueued wake this unwind
will never consume (dropping earlier would race the in-flight claimer
and leak the wake into the task's next park); finally restore or retire
the entry. Because the registrations are already withdrawn when the
exception reaches the caller, its catch owes nothing to the protocol -
it only restores whatever lock contract its own callers require
(reacquiring shielded, and only what that contract demands: an unwind
that is itself a cancellation should not sleep on locks it does not
need).
"""
function wait_safe_interrupt(ws, w::WaitEntry)
    ct = current_task()
    local r
    try
        r = wait()
    catch
        interrupted_park_cleanup!(ct, ws, w)
        rethrow()
    end
    return r
end

```
-/
def wait_safe_interrupt (ws : Waitables Src X) (w : Entry) : M World Value := do
  let ct ← t.currentTask
  match ← capture t.waitScheduler with
  | .ok r => return r
  | .error e =>
    interrupted_park_cleanup p t ct ws w
    throw e

/--
Julia source: base/park.jl:239-252 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    withdraw!(ws, w::WaitEntry, why::UInt8=WAKE_WITHDRAWN)

Withdraw every registration of `w` per its kind's policy and release the
entry (retiring it when fresh; idempotent). The lock discipline follows
`why`: `WAKE_VALUE`/`WAKE_FIRED` run under the caller's still-held
protection (the lazy settle after a wake; the fired branch), while
`WAKE_WITHDRAWN` dequeues are self-protecting (leaving a multi-wait).
"""
function withdraw!(ws, w::WaitEntry, why::UInt8=WAKE_WITHDRAWN)
    _dequeue_each!(ws, w, why)
    release_wait_entry!(current_task(), w)
    return nothing
end
```
-/
def withdraw (ws : Waitables Src X) (w : Entry) (why : U8 := WAKE_WITHDRAWN) : M World Unit := do
  dequeue_each p ws w why
  release_wait_entry t (← t.currentTask) w

/--
Julia source: base/park.jl:372-373 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
acquire_wait_entry!(ct::Task, ws::Tuple{WatcherWait}) = WaitEntry1(ct)
acquire_wait_entry!(ct::Task, ws::Tuple{WatcherWait, SourceWait}) = WaitEntry2(ct)
```
-/
-- The `Tuple{WatcherWait}` and `Tuple{WatcherWait, SourceWait}` methods are the first two cases
-- of `acquire_wait_entry` above.
def acquire_wait_entry_watcher (ct : Task) (ws : Waitables Src X) : M World Entry :=
  acquire_wait_entry s ct ws

/--
Julia source: base/park.jl:384-429 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    wait(tok::CancellationToken; cancel=...)

Block until `tok`'s source is cancelled, and return the corresponding
[`CancellationRequest`](@ref) as an ordinary value; return immediately if it
already is. This inverts the usual delivery - cancellation of `tok` is the
event this operation waits *for*, not an interruption of it - and is the
building block of the watcher-task ("cancellation callback") pattern.

The wait itself accepts the standard `cancel` keyword argument (defaulting
to the scoped token) and is interrupted by that token like any other
blocking operation. Waiting on the token that also governs the wait is
refused with an `ArgumentError`, since completing and interrupting the wait
would be the same event; pass `cancel = nothing` to wait for `tok`
unconditionally.
"""
function wait(tok::CancellationToken; cancel::CancelTokenArg=DEFAULT_CANCEL)
    src = tok.source
    gov = resolve_cancel_token(cancel)
    govsrc = gov === nothing ? nothing : gov.source
    if govsrc === src
        throw(ArgumentError(
            "cannot wait for a token's cancellation under the same governing token; " *
            "pass `cancel = nothing` to wait for it unconditionally"))
    end
    govsrc === nothing || checkcancel(govsrc)
    st = @atomic :acquire src.state
    st != 0x00 && return CancellationRequest(st)
    ct = current_task()
    ws = govsrc === nothing ? (WatcherWait(src),) :
                              (WatcherWait(src), SourceWait(govsrc, CANCEL_REQUEST_SAFE.request))
    w = acquire_wait_entry!(ct, ws)
    if !park!(ws, w, true)
        # Fired, and the self-claim won: either the watched source's
        # cancellation (the awaited event, delivered as the return value)
        # or the governing token's (the refusal) - re-inspect to tell.
        withdraw!(ws, w, WAKE_FIRED)
        st = @atomic :acquire src.state
        st != 0x00 && return CancellationRequest(st)
        checkcancel(govsrc::CancellationTokenSource) # throws the refusal
        error("cancellation wait fired with no cancellation")
    end
    r = wait_safe_interrupt(ws, w)
    withdraw!(ws, w, WAKE_VALUE)
    return r::CancellationRequest
end
```
-/
def wait (tok : Token) (cancel : CancelArg Token := .default) : M World Req := do
  let src := s.tokenSource tok
  let gov ← s.resolveCancelToken cancel
  let govsrc := gov.map s.tokenSource
  let same := match govsrc with
    | some g => s.sameSource g src
    | none => false
  if same then
    throw (.jl (.argumentError
      ("cannot wait for a token's cancellation under the same governing token; " ++
       "pass `cancel = nothing` to wait for it unconditionally")))
  match govsrc with
  | some g => s.checkcancel g
  | none => pure ()
  let st ← s.state src .acquire
  if st.val != 0 then return s.request st
  let ct ← t.currentTask
  let ws : Waitables Src X := match govsrc with
    | none => .tuple [WatcherWaitDefault s src]
    | some g => .tuple [WatcherWaitDefault s src, SourceWait g s.cancelRequestSafe]
  let w ← acquire_wait_entry s ct ws
  if !(← park p t s ws w true) then
    withdraw p t ws w WAKE_FIRED
    let st ← s.state src .acquire
    if st.val != 0 then return s.request st
    match govsrc with
    | some g => s.checkcancel g
    | none => throw (.foreignError "TypeError"
        "in typeassert, expected CancellationTokenSource, got a value of type Nothing")
    throw (.errorException "cancellation wait fired with no cancellation")
  let r ← wait_safe_interrupt p t ws w
  withdraw p t ws w WAKE_VALUE
  s.asRequest r

end

end JuliaLean.base.park


namespace JuliaLean.ConcurrencyCov.Park

open JuliaLean JuliaLean.ConcurrencyCov

/-- `CANCEL_REQUEST_SAFE.request`. -/
def SAFE : Nat := 1
/-- `WAIT_AUX_WATCHER_BIT`. -/
def WATCHER_BIT : Nat := 0x100

/-- The why-codes of `wait_dequeue!`, lines 54-57. -/
def WAKE_VALUE : Nat := 0
def WAKE_FIRED : Nat := 1
def WAKE_INTERRUPTED : Nat := 3
def WAKE_WITHDRAWN : Nat := 4

/-- The identity a slot's `owner` records. -/
inductive Owner where
  | src (s : Nat)
  | obj (o : Nat)
  deriving DecidableEq, Repr

/-- The waitables of a park. `obj o hasRecheck`: an object with its own
`wait_enqueue!`, and with its own `wait_recheck` method when `hasRecheck`. -/
inductive Waitable where
  | source (src : Nat) (floor : Nat)
  | watcher (src : Nat) (floor : Nat)
  | obj (o : Nat) (hasRecheck : Bool)
  deriving DecidableEq, Repr

/-- A wait entry: its slots (`owner`), their aux words, and whether `w.task` is
the waiter (`false` once retired). -/
structure Entry where
  slots : List (Option Owner)
  aux : List Nat
  live : Bool
  deriving DecidableEq, Repr

def Entry.fresh (n : Nat) : Entry := ⟨List.replicate n none, List.replicate n 0, true⟩

structure St where
  waitingOn : Option Nat
  cachedWait : Option Nat
  cachedCancel : Option Nat
  /-- The task is linked in a `StickyWorkqueue`. -/
  queued : Bool
  /-- Entries by identity (index). -/
  entries : List Entry
  srcState : Nat → Nat
  /-- `waiters_head` list of each source, newest first. -/
  regs : Nat → List Nat
  regCount : Nat → Nat
  /-- `_note_dead_registration!` calls per source. -/
  dead : Nat → Nat
  objEnq : Nat → Bool
  objFired : Nat → Bool
  /-- Object dequeues: waitable, entry, why. -/
  dequeues : List (Waitable × Nat × Nat)

/-- Outcome and final state: an exception keeps the state at the throw. -/
def PM (α : Type) : Type := St → R α × St

instance : Monad PM where
  pure a := fun s => (.ok a, s)
  bind x f := fun s => match x s with
    | (.ok a, s') => f a s'
    | (.error e, s') => (.error e, s')

def get : PM St := fun s => (.ok s, s)
def set (s : St) : PM Unit := fun _ => (.ok (), s)
def modify (f : St → St) : PM Unit := fun s => (.ok (), f s)
def throwE {α : Type} (e : Exn) : PM α := fun s => (.error e, s)

namespace St
def entry (s : St) (w : Nat) : Entry := s.entries.getD w (Entry.fresh 0)
def setEntry (s : St) (w : Nat) (e : Entry) : St := { s with entries := s.entries.set w e }
end St

/-! ## Helpers from `base/cancellation.jl` -/

/-- `_find_slot(w, owner)`: the 1-based slot registered on `owner`, or 0. -/
def findSlot (e : Entry) (o : Owner) : Nat :=
  match e.slots.findIdx? (· = some o) with
  | some i => i + 1
  | none => 0

/-- `_free_slot(w)`. -/
def freeSlot (e : Entry) : Nat :=
  match e.slots.findIdx? (· = none) with
  | some i => i + 1
  | none => 0

/-- `_acquire_slot!(w, owner)`. -/
def acquireSlot (w : Nat) (o : Owner) : PM Nat := do
  let s ← get
  let e := s.entry w
  let i := freeSlot e
  if i = 0 then throwE .concurrencyViolation
  set (s.setEntry w { e with slots := e.slots.set (i - 1) (some o) })
  return i

/-- `_set_slot_aux!(w, i, v)`. -/
def setSlotAux (w i v : Nat) : PM Unit :=
  modify fun s => let e := s.entry w; s.setEntry w { e with aux := e.aux.set (i - 1) v }

/-- `_release_slot!(w, i)`: aux cleared, owner released. -/
def releaseSlot (w i : Nat) (s : St) : St :=
  let e := s.entry w
  s.setEntry w { e with aux := e.aux.set (i - 1) 0, slots := e.slots.set (i - 1) none }

/-- A fresh entry with `n` slots (`WaitEntry1`, `WaitEntry2`, `WaitEntryN`). -/
def newEntry (n : Nat) : PM Nat := fun s =>
  (.ok s.entries.length, { s with entries := s.entries ++ [Entry.fresh n] })

def setLive (w : Nat) (b : Bool) (s : St) : St :=
  let e := s.entry w
  s.setEntry w { e with live := b }

/-- `_arm_wait(waiter, w)`: CAS `waiting_on` from `nothing` to `w`. -/
def armWait (w : Nat) : PM Unit := do
  let s ← get
  if s.waitingOn = none then set { s with waitingOn := some w }
  else throwE .concurrencyViolation

/-- `_note_dead_registration!(o)` for every source slot, after `w.task = nothing`
(`retire_cancellation_entry!`). -/
def retireEntry (w : Nat) (s : St) : St :=
  let s := setLive w false s
  (s.entry w).slots.foldl (fun s o => match o with
    | some (.src src) => { s with dead := upd s.dead src (s.dead src + 1) }
    | _ => s) s

/-- `unregister_cancellation!(src, w)`: unlink `w` from the source's list and
free its slot. -/
def unregisterCancellation (src w : Nat) (s : St) : St :=
  let s := { s with regs := upd s.regs src ((s.regs src).filter (· ≠ w)),
                    regCount := upd s.regCount src (s.regCount src - 1) }
  let i := findSlot (s.entry w) (.src src)
  if i = 0 then s else releaseSlot w i s

/-- `_cached_wait_entry(waiter)`. -/
def cachedWaitEntry : PM Nat := do
  let s ← get
  match s.cachedWait with
  | some w =>
    if (s.entry w).slots = [none] then
      set (setLive w true s)
      return w
    else
      let w ← newEntry 1
      modify fun s => { s with cachedWait := some w }
      return w
  | none =>
    let w ← newEntry 1
    modify fun s => { s with cachedWait := some w }
    return w

/-- `_cancel_wait_entry(waiter, src, min_severity)`. -/
def cancelWaitEntry (src minSev : Nat) : PM Nat := do
  let s ← get
  let w ← match s.cachedCancel with
    | some w =>
      match (s.entry w).slots with
      | [none, o] =>
        if o = some (.src src) ∨ o = none then
          set (setLive w true s)
          pure w
        else match o with
          | some (.src o) =>
            set (setLive w true (unregisterCancellation o w s))
            pure w
          | _ => throwE .typeError
      | [_, _] => newEntry 2
      | _ => do
        let w ← newEntry 2
        modify fun s => { s with cachedCancel := some w }
        pure w
    | none => do
      let w ← newEntry 2
      modify fun s => { s with cachedCancel := some w }
      pure w
  setSlotAux w 2 minSev
  return w

/-- `checkcancel(src)`: throw `CancellationRequest(state)` when cancelled. -/
def checkcancel (src : Nat) : PM Unit := do
  let s ← get
  if s.srcState src = 0 then return ()
  throwE (.cancellation (s.srcState src))

/-! ## The waitable protocol -/

/-- `_source_wait_enqueue!(src, w, aux)`, lines 306-337. -/
def sourceWaitEnqueue (src w aux : Nat) : PM Bool := do
  let s ← get
  let i := findSlot (s.entry w) (.src src)
  if i = 0 then
    let i ← acquireSlot w (.src src)
    setSlotAux w i aux
    modify fun s => { s with regs := upd s.regs src (w :: s.regs src) }
    modify fun s => { s with regCount := upd s.regCount src (s.regCount src + 1) }
  return true

/-- `wait_enqueue!(x, w, first)`: lines 339-340 and 375-377 for the sources; an
object's own method registers `w` in a free slot unless it already fired. -/
def waitEnqueue (x : Waitable) (w : Nat) (_first : Bool) : PM Bool :=
  match x with
  | .source src floor => sourceWaitEnqueue src w floor
  | .watcher src floor => sourceWaitEnqueue src w (WATCHER_BIT ||| max floor SAFE)
  | .obj o _ => do
    let s ← get
    if s.objEnq o then
      let _ ← acquireSlot w (.obj o)
      return true
    else return false

/-- `wait_recheck(x, w)`: the vacuous default (line 61), the source state
reads (lines 342-347, 379-380), or the object's own method. -/
def waitRecheck (x : Waitable) (_w : Nat) (s : St) : Bool :=
  match x with
  | .source src floor => s.srcState src ≠ 0 && s.srcState src ≥ floor
  | .watcher src floor => s.srcState src ≥ max floor SAFE
  | .obj o hasRecheck => if hasRecheck then s.objFired o else false

/-- `wait_dequeue!(x, w, why)`: nothing for the sources (lines 349, 382:
registrations are sticky); an object releases its slot. -/
def waitDequeue (x : Waitable) (w why : Nat) (s : St) : St :=
  match x with
  | .source _ _ | .watcher _ _ => s
  | .obj o _ =>
    let i := findSlot (s.entry w) (.obj o)
    let s := if i = 0 then s else releaseSlot w i s
    { s with dequeues := s.dequeues ++ [(x, w, why)] }

/-- `WatcherWait(src)`, line 370. -/
def watcherWait (src : Nat) : Waitable := .watcher src SAFE

/-- `_uncancellable_lock(l)`, line 67: the plain `lock(l)`. -/
def uncancellableLock {α β : Type} (lock : α → β) (l : α) : β := lock l

/-- `acquire_wait_entry!(ct, ws)`, lines 90-93 and 372-373, by the most
specific tuple method; `tuple = false` is a non-tuple iterable. -/
def acquireWaitEntry (ws : List Waitable) (tuple : Bool) : PM Nat :=
  match tuple, ws with
  | true, [.watcher _ _] => newEntry 1
  | true, [.watcher _ _, .source _ _] => newEntry 2
  | true, [_] => cachedWaitEntry
  | true, [_, .source src floor] => cancelWaitEntry src floor
  | _, _ => newEntry ws.length

/-- `release_wait_entry!(ct, w)`, lines 97-103. -/
def releaseWaitEntry (w : Nat) (s : St) : St :=
  if s.cachedWait = some w ∨ s.cachedCancel = some w then s
  else if !(s.entry w).live then s
  else retireEntry w s

/-- `disarm!(ct, w)`, line 106. -/
def disarm (w : Nat) (s : St) : Bool × St :=
  if s.waitingOn = some w then (true, { s with waitingOn := none }) else (false, s)

/-- `_enqueue_until_fired`, lines 146-157 (the tuple and loop methods agree). -/
def enqueueUntilFired : List Waitable → Nat → Bool → PM (Option Waitable)
  | [], _, _ => pure none
  | x :: ws, w, first => do
    let ok ← waitEnqueue x w first
    if !ok then return some x
    enqueueUntilFired ws w first

/-- `_recheck_until_fired`, lines 158-169. -/
def recheckUntilFired : List Waitable → Nat → St → Option Waitable
  | [], _, _ => none
  | x :: ws, w, s => if waitRecheck x w s then some x else recheckUntilFired ws w s

/-- `_dequeue_each!`, lines 170-180. -/
def dequeueEach : List Waitable → Nat → Nat → St → St
  | [], _, _, s => s
  | x :: ws, w, why, s => dequeueEach ws w why (waitDequeue x w why s)

/-- A concurrent waker's claim of `w` (`claim_wait`). -/
def claim (claimed : Bool) (w : Nat) (s : St) : St :=
  if claimed ∧ s.waitingOn = some w then { s with waitingOn := none } else s

/-- `park!(ws, w, first)`, lines 132-142. -/
def park (ws : List Waitable) (w : Nat) (first claimed : Bool) : PM Bool := do
  armWait w
  let fx ← enqueueUntilFired ws w first
  let s ← get
  let fx := if fx.isNone then recheckUntilFired ws w s else fx
  modify (claim claimed w)
  match fx with
  | some x =>
    let s ← get
    let (won, s) := disarm w s
    set s
    if won then
      modify (waitDequeue x w WAKE_FIRED)
      return false
    return true
  | none => return true

/-- `repark!(ws, w)`, lines 191-200. -/
def repark (ws : List Waitable) (w : Nat) (claimed : Bool) : PM Bool := do
  armWait w
  let s ← get
  let fx := recheckUntilFired ws w s
  modify (claim claimed w)
  match fx with
  | some x =>
    let s ← get
    let (won, s) := disarm w s
    set s
    if won then
      modify (waitDequeue x w WAKE_FIRED)
      return false
    return true
  | none => return true

/-- `withdraw!(ws, w, why)`, lines 248-252. -/
def withdraw (ws : List Waitable) (w why : Nat) (s : St) : St :=
  releaseWaitEntry w (dequeueEach ws w why s)

/-- `interrupted_park_cleanup!(ct, ws, w)`, lines 276-301. `nested` are the
entries a nested park cached while the dequeues took their locks. -/
def interruptedParkCleanup (ws : List Waitable) (w : Nat) (nested : Option Nat × Option Nat)
    (s : St) : St :=
  let s := if s.waitingOn = some w then { s with waitingOn := none } else s
  let wasPlain := s.cachedWait = some w
  let wasCancel := !wasPlain && s.cachedCancel = some w
  let s := if wasPlain then { s with cachedWait := none } else s
  let s := if wasCancel then { s with cachedCancel := none } else s
  let s := dequeueEach ws w WAKE_INTERRUPTED s
  let s := { s with cachedWait := if s.cachedWait = none then nested.1 else s.cachedWait,
                    cachedCancel := if s.cachedCancel = none then nested.2 else s.cachedCancel }
  let s := { s with queued := false }
  if wasPlain then
    if s.cachedWait = none then { s with cachedWait := some w } else retireEntry w s
  else if wasCancel then
    if s.cachedCancel = none then { s with cachedCancel := some w } else retireEntry w s
  else releaseWaitEntry w s

/-- `wait_safe_interrupt(ws, w)`, lines 227-237: `wake` is what `wait()` returns
or throws. -/
def waitSafeInterrupt (ws : List Waitable) (w : Nat) (wake : R Nat)
    (nested : Option Nat × Option Nat) : PM Nat := fun s =>
  match wake with
  | .ok r => (.ok r, s)
  | .error e => (.error e, interruptedParkCleanup ws w nested s)

/-- `wait(tok; cancel)`, lines 400-429. `src` is `tok.source`; `gov` the
governing token's source (`resolve_cancel_token(cancel)`); a request is
represented by its severity. -/
def waitToken (src : Nat) (gov : Option Nat) (claimed : Bool) (wake : R Nat)
    (nested : Option Nat × Option Nat) : PM Nat := do
  if gov = some src then
    throwE (.argumentError ("cannot wait for a token's cancellation under the same governing token; " ++
      "pass `cancel = nothing` to wait for it unconditionally"))
  match gov with
  | some g => checkcancel g
  | none => pure ()
  let s ← get
  let st := s.srcState src
  if st ≠ 0 then return st
  let ws := match gov with
    | none => [watcherWait src]
    | some g => [watcherWait src, .source g SAFE]
  let w ← acquireWaitEntry ws true
  let parked ← park ws w true claimed
  if !parked then
    modify (withdraw ws w WAKE_FIRED)
    let s ← get
    let st := s.srcState src
    if st ≠ 0 then return st
    match gov with
    | some g => checkcancel g
    | none => throwE .typeError
    throwE (.errorException "cancellation wait fired with no cancellation")
  let r ← waitSafeInterrupt ws w wake nested
  modify (withdraw ws w WAKE_VALUE)
  return r

end JuliaLean.ConcurrencyCov.Park

namespace JuliaLean.ConcurrencyCov.FaithfulPark

open JuliaLean.ConcurrencyCov

def waitRecheckDefault (object entry : Nat) (s : Park.St) := Park.waitRecheck (.obj object false) entry s
def uncancellableLock (lock : Nat → Nat) (l : Nat) := Park.uncancellableLock lock l
def acquireTupleOne (x : Park.Waitable) := match x with
  | .watcher _ _ => Park.newEntry 1 | _ => Park.cachedWaitEntry
def acquireTupleSource (x : Park.Waitable) (src floor : Nat) := match x with
  | .watcher _ _ => Park.newEntry 2 | _ => Park.cancelWaitEntry src floor
def acquireGeneric (ws : List Park.Waitable) := Park.newEntry ws.length
def releaseWaitEntryM := Park.releaseWaitEntry
def disarmM := Park.disarm
def parkM := Park.park
def enqueueEmpty (w : Nat) (first : Bool) := Park.enqueueUntilFired [] w first
def enqueueTuple (ws : List Park.Waitable) (w : Nat) (first : Bool) := Park.enqueueUntilFired ws w first
def enqueueGeneric (ws : List Park.Waitable) (w : Nat) (first : Bool) := Park.enqueueUntilFired ws w first
def recheckEmpty (w : Nat) (s : Park.St) := Park.recheckUntilFired [] w s
def recheckTuple (ws : List Park.Waitable) (w : Nat) (s : Park.St) := Park.recheckUntilFired ws w s
def recheckGeneric (ws : List Park.Waitable) (w : Nat) (s : Park.St) := Park.recheckUntilFired ws w s
def dequeueEmpty (w why : Nat) (s : Park.St) := Park.dequeueEach [] w why s
def dequeueTuple (ws : List Park.Waitable) (w why : Nat) (s : Park.St) := Park.dequeueEach ws w why s
def dequeueGeneric (ws : List Park.Waitable) (w why : Nat) (s : Park.St) := Park.dequeueEach ws w why s
def reparkM := Park.repark
def waitSafeInterruptM := Park.waitSafeInterrupt
def withdrawM := Park.withdraw
def interruptedCleanupM := Park.interruptedParkCleanup
def sourceWaitEnqueueM := Park.sourceWaitEnqueue
def sourceWaitEnqueue (src floor w : Nat) (first : Bool) := Park.waitEnqueue (.source src floor) w first
def sourceWaitRecheck (src floor w : Nat) (s : Park.St) := Park.waitRecheck (.source src floor) w s
def sourceWaitDequeue (src floor w why : Nat) (s : Park.St) := Park.waitDequeue (.source src floor) w why s
def watcherWaitM := Park.watcherWait
def acquireWatcherOne (src floor : Nat) := Park.newEntry 1
def acquireWatcherSource (src floor gov minSev : Nat) := Park.newEntry 2
def watcherEnqueue (src floor w : Nat) (first : Bool) := Park.waitEnqueue (.watcher src floor) w first
def watcherRecheck (src floor w : Nat) (s : Park.St) := Park.waitRecheck (.watcher src floor) w s
def watcherDequeue (src floor w why : Nat) (s : Park.St) := Park.waitDequeue (.watcher src floor) w why s
def waitTokenM := Park.waitToken

end JuliaLean.ConcurrencyCov.FaithfulPark
