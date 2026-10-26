import JuliaLean.ConcurrencyCov.Common

/-!
# `base/park.jl` (master `bbfa0ce4150`)

The parked-wait driver of one task `ct`. The state holds the task's claim word
`waiting_on`, its two cached wait entries, its membership of a sticky work
queue, the wait entries (their slots, slot aux words and whether `w.task` is
still the waiter), and for every cancellation source its severity, its waiter
list and its registration counters. The helpers the driver calls from
`base/cancellation.jl` (`_arm_wait`, `_cached_wait_entry`, `_cancel_wait_entry`,
`retire_cancellation_entry!`, `unregister_cancellation!`, the slot primitives
and `checkcancel`) are mirrored here.

Waitables other than the two source kinds are objects with their own
`wait_enqueue!`/`wait_recheck` methods elsewhere in Base; their answers are
fields of the state (`objEnq`, `objFired`), and their `wait_dequeue!` releases
the object's slot and is recorded in `dequeues`.

Concurrency enters through three explicit inputs: `claimed` (a concurrent
waker claimed the armed registration before the self-claim), the payload or
exception of the suspending `wait()`, and the cache entries a nested park
installs while the cleanup's self-protecting dequeues take their locks.
-/

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
