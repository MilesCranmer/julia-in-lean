import JuliaLean.base.locks_mt
import JuliaLean.base.threadingconstructs

/-!
# Typed model of `base/condition.jl`

Conditions keep an intrusive wait queue and a constant lock reference. Task,
registration, cancellation, and scheduler operations are typed primitives over
one mutable world. A thrown wait retains the lock and queue changes that
preceded it; a non-returning wait is represented by nontermination.
-/
namespace JuliaLean.base.condition
open JuliaLean
open JuliaLean.base.locks_mt (M MemoryOrder loop finallyDo)
abbrev I := JInt .i64
abbrev I16 := JInt .i16
def int (x : Int) : I := JInt.wrap .i64 x

inductive CancelArg (Token : Type) where
  | default | shielded | explicit (token : Token)

structure AlwaysLockedST where
  ownerThread : I16

structure GenericCondition (Queue Lock : Type) where
  identity : Nat
  waitq : Queue
  lock : Lock

abbrev Condition (Queue : Type) := GenericCondition Queue AlwaysLockedST

inductive PrintArg (Lock : Type) where
  | genericConditionType | conditionType | text (value : String) | lock (value : Lock)

structure QueueRef (Queue Lock : Type) where
  queue : Queue
  owner : GenericCondition Queue Lock

inductive Owner (Queue Lock Source : Type) where
  | spin (condition : GenericCondition Queue Lock)
  | reentrant (condition : GenericCondition Queue Lock)
  | always (condition : GenericCondition Queue Lock)
  | cancellation (source : Source)
  | other

inductive Waitable (Queue Lock Source : Type) where
  | condition (condition : GenericCondition Queue Lock)
  | source (source : Source) (minSeverity : UInt8)
  | watcher (source : Source) (minSeverity : UInt8)

inductive WakeValue (Value : Type) where
  | nothing | value (value : Value) | cancellation (severity : UInt8)

structure Runtime (E W Queue Lock Task Entry Slot Source Token LockState Value : Type) where
  queries : JuliaLean.base.threadingconstructs.Queries E W
  newQueue : M E W Queue
  newLock : M E W Lock
  newIdentity : M E W Nat
  isLocked : Lock → M E W Bool
  lock : Lock → M E W Unit
  unlock : Lock → M E W Unit
  trylock : Lock → M E W Bool
  assertHaveLock : Lock → M E W Unit
  uncancellableLock : Lock → M E W Unit
  unlockAll : Lock → M E W LockState
  relockAll : Lock → LockState → M E W Unit
  relockAllButOne : Lock → LockState → M E W Unit
  pushFirst : QueueRef Queue Lock → Entry → M E W Unit
  pushLast : QueueRef Queue Lock → Entry → M E W Unit
  deleteFirst : QueueRef Queue Lock → Entry → M E W Unit
  popFirst : QueueRef Queue Lock → M E W Entry
  queueEmpty : Queue → M E W Bool
  refEmpty : QueueRef Queue Lock → M E W Bool
  slots : Entry → M E W (List Slot)
  owner : Slot → M E W (Option (Owner Queue Lock Source))
  entryTask : MemoryOrder → Entry → M E W (Option Task)
  claimWait : Task → Entry → M E W Bool
  currentTask : M E W Task
  isTaskStarted : Task → M E W Bool
  taskQueue : Task → M E W (Option Queue)
  waitingOn : MemoryOrder → Task → M E W (Option Entry)
  birthCancelSource : Task → M E W (Option Source)
  sourceCancelled : Source → M E W Bool
  sourceState : MemoryOrder → Option Source → M E W UInt8
  cachedWaitEntry : Task → M E W Entry
  cancelWaitEntry : Task → Source → UInt8 → M E W Entry
  newWaitEntry2 : Task → M E W Entry
  armWait : Task → Entry → M E W Unit
  disarm : Task → Entry → M E W Bool
  sourceEnqueue : Source → UInt8 → Entry → Bool → M E W Unit
  sourceRecheck : Source → UInt8 → Entry → M E W Bool
  park : List (Waitable Queue Lock Source) → Entry → Bool → M E W Bool
  withdraw : List (Waitable Queue Lock Source) → Entry → UInt8 → M E W Unit
  waitSafeInterrupt : List (Waitable Queue Lock Source) → Entry → M E W (WakeValue Value)
  checkCancelArg : CancelArg Token → M E W (Option Token)
  cancelSource : Option Token → Option Source
  checkCancel : Option Source → M E W Unit
  schedule : Task → WakeValue Value → Bool → M E W Unit
  sticky : Task → M E W Bool
  taskThreadId : Task → M E W I
  inFinalizer : M E W Bool
  setSticky : Task → Bool → M E W Unit
  setTaskThreadId : Task → I → M E W Unit
  wakeInterrupted : UInt8
  wakeWithdrawn : UInt8
  wakeFired : UInt8
  wakeValue : UInt8
  concurrencyError : String → E
  argumentError : String → E
  error : String → E

section
variable {E W Queue Lock Task Entry Slot Source Token LockState Value : Type}
variable (r : Runtime E W Queue Lock Task Entry Slot Source Token LockState Value)

-- Source: base/condition.jl:1-4 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- ## thread/task locking abstraction
-- 
-- /Source

-- Source: base/condition.jl:10-22 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     AbstractLock
-- 
-- Abstract supertype describing types that
-- implement the synchronization primitives:
-- [`lock`](@ref), [`trylock`](@ref), [`unlock`](@ref), and [`islocked`](@ref).
-- """
-- abstract type AbstractLock end
-- function lock end
-- function unlock end
-- function trylock end
-- function islocked end
-- /Source

-- Source: base/condition.jl:25-30 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # Restore all but one level of a hold captured by `unlockall` - the
-- # enclosing frames' levels, consuming the waiting frame's own - for the
-- # exceptional unwind out of the internal wait layer. A no-op when that
-- # frame's level was the only one (the common case: a depth-1 cancellation
-- # unwind performs no lock operation at all). The state stays opaque;
-- # shielded like `relockall` - a restore has no correct cancellable use.
-- /Source

-- Source: base/condition.jl:37-52 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     AlwaysLockedST
-- 
-- This struct does not implement a real lock, but instead
-- pretends to be always locked on the original thread it was allocated on,
-- and simply ignores all other interactions.
-- It also does not synchronize tasks; for that use a real lock such as [`ReentrantLock`](@ref).
-- This can be used in the place of a real lock to, instead, simply and cheaply assert
-- that the operation is only occurring on a single cooperatively-scheduled thread.
-- It is thus functionally equivalent to allocating a real, recursive, task-unaware lock
-- immediately calling `lock` on it, and then never calling a matching `unlock`,
-- except that calling `lock` from another thread will throw a concurrency violation exception.
-- """
-- struct AlwaysLockedST <: AbstractLock
--     ownertid::Int16
-- /Source

-- Source: base/condition.jl:54-54 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- end
-- /Source

-- Source: base/condition.jl:60-78 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- 
-- ## condition variables
-- 
-- # (The WaitEntry registration type and the wake-claim protocol live in
-- # cancellation.jl, which is included earlier in bootstrap: registrations
-- # carry the cancellation half of a parked wait.)
-- 
-- """
--     GenericCondition
-- 
-- Abstract implementation of a condition object
-- for synchronizing task objects with a given lock.
-- """
-- mutable struct GenericCondition{L<:AbstractLock}
--     # mutable for identity only
--     const waitq::IntrusiveLinkedList{WaitEntry}
--     const lock::L
-- 
-- /Source

-- Source: base/condition.jl:82-83 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- end
-- 
-- /Source

-- Source: base/condition.jl:85-92 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     try_unlink_claimed!(w::WaitEntry)
-- 
-- Opportunistically attempt to unlink a wait entry from its queue. This is a memory pressure
-- optimization. If the queue is locked by another task, the entry will remain linked and will
-- be unlinked upon the next wakeup attempt.
-- """
-- /Source

-- Source: base/condition.jl:114-114 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/condition.jl:124-124 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/condition.jl:126-126 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/condition.jl:129-130 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # (the `cancel`-forwarding lock method for ReentrantLock-backed conditions
-- # lives in lock.jl, after ReentrantLock is defined)
-- /Source

-- Source: base/condition.jl:134-134 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/condition.jl:136-139 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- ## GenericCondition as a waitable (see base/park.jl): the lock-carried
-- ## kind - its lock is caller-held from before phase 4 into the suspend
-- ## bracket, which is what makes its recheck vacuous.
-- /Source

-- Source: base/condition.jl:166-166 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/condition.jl:169-175 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Freshness is stricter than `!istaskstarted`: a task that
-- # `schedule`/`@async` has merely enqueued hasn't run yet, but arming it
-- # here would collide with the arm its own first park performs once it
-- # starts (that park's `_arm_wait` CAS fails and unwinds a wait's lock
-- # choreography from the outside). Reject anything started, queued, or
-- # already armed.
-- /Source

-- Source: base/condition.jl:181-185 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Start `waiter` with the (level-triggered) cancellation of its birth
-- # source: a subscribed task whose governing source is cancelled dies
-- # instead of running its body - a never-started task raises the scheduled
-- # exception at start.
-- /Source

-- Source: base/condition.jl:191-205 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Subscribe the not-yet-started task `waiter` to `c`'s next notify: arm
-- # its registration and enqueue it, so the notify's claim-and-schedule is
-- # the task's first schedule - a start trigger; the current task does not
-- # suspend. Waits of the *current* task go through `park!` (base/park.jl).
-- #
-- # Subscriptions are governed by the *waiter's* birth cancellation source
-- # (the CANCEL_TOKEN of the scope captured at its construction): if that
-- # source is - or becomes, while still subscribed - cancelled, the task
-- # dies with the CancellationRequest instead of starting. Cleanup-class
-- # subscribers (Timer/AsyncCondition callback tasks, channel close hooks,
-- # errormonitor, REPL teardown) are constructed under
-- # `CANCEL_TOKEN => nothing` and so are never killed this way.
-- # Returns the registration entry (or `nothing` when the subscription was
-- # refused and the waiter scheduled to die).
-- /Source

-- Source: base/condition.jl:250-290 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     wait([x])
-- 
-- Block the current task until some event occurs.
-- 
-- * [`Channel`](@ref): Wait for a value to be appended to the channel.
-- * [`Condition`](@ref): Wait for [`notify`](@ref) on a condition and return the `val`
--   parameter passed to `notify`. See the `Condition`-specific docstring of `wait` for
--   the exact behavior.
-- * `Process`: Wait for a process or process chain to exit. The `exitcode` field of a process
--   can be used to determine success or failure.
-- * [`Task`](@ref): Wait for a `Task` to finish. See the `Task`-specific docstring of `wait` for
--   the exact behavior.
-- * [`RawFD`](@ref): Wait for changes on a file descriptor (see the `FileWatching` package).
-- * [`Timer`](@ref), [`AsyncCondition`](@ref Base.AsyncCondition): Wait for the timer to trigger or
--   the condition to be notified. Throws an [`EOFError`](@ref) if the object has been closed; see
--   their docstrings for the exact behavior.
-- 
-- If no argument is passed, the task blocks for an undefined period. A task can only be
-- restarted by an explicit call to [`schedule`](@ref) or [`yieldto`](@ref).
-- 
-- Often `wait` is called within a `while` loop to ensure a waited-for condition is met before
-- proceeding.
-- """
-- function wait end
-- 
-- """
--     wait(c::GenericCondition; first::Bool=false, cancel=Base.DEFAULT_CANCEL)
-- 
-- Wait for [`notify`](@ref) on `c` and return the `val` parameter passed to `notify`.
-- 
-- If the keyword `first` is set to `true`, the waiter will be put _first_
-- in line to wake up on `notify`. Otherwise, `wait` has first-in-first-out (FIFO) behavior.
-- 
-- The `cancel` keyword argument controls which cancellation token may interrupt
-- the wait (throwing the [`CancellationRequest`](@ref) into the waiter): by
-- default the scoped token (see `Base.CANCEL_TOKEN`); pass a
-- [`CancellationToken`](@ref) to override it, or `nothing` to make the wait
-- non-cancellable.
-- """
-- /Source

-- Source: base/condition.jl:310-327 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # (The interrupted-wait cleanup lives in base/park.jl as
-- # interrupted_park_cleanup!, shared by every park site.)
-- 
-- # `min_severity` is the lowest severity that may wake (cancel) this wait -
-- # the comparisons are inclusive on both the registration and walk sides. A
-- # teardown wait that re-parks after acknowledging a delivery at severity
-- # `s` must therefore pass `s + 0x01` (exclusive staging), so a re-cancel at
-- # the acknowledged severity leaves it parked and only an escalation wakes
-- # it; see e.g. _uv_write_cancelled_finish.
-- #
-- # `cancel_value` makes a cancellation of the governing token complete the
-- # wait as an ordinary (value-mode) wake returning the `CancellationRequest`
-- # instead of throwing it - callers that must keep working through a
-- # cancellation (structured teardown) check the return value rather than
-- # catching. Value-mode returns follow the normal wake contract (the
-- # caller's lock is held), and the registration rides the walk's watcher
-- # delivery, so no exception is constructed anywhere on the path.
-- /Source

-- Source: base/condition.jl:406-415 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     notify(condition, val=nothing; all=true, error=false)
-- 
-- Wake up tasks waiting for a condition, passing them `val`. If `all` is `true` (the default),
-- all waiting tasks are woken, otherwise only one is. If `error` is `true`, the passed value
-- is raised as an exception in the woken tasks.
-- 
-- Return the count of tasks woken up. Return 0 if no tasks are waiting on `condition`.
-- """
-- /Source

-- Source: base/condition.jl:435-435 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/condition.jl:437-442 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     isempty(condition)
-- 
-- Return `true` if no tasks are waiting on the condition, `false` otherwise.
-- """
-- /Source

-- Source: base/condition.jl:444-462 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- 
-- # default (Julia v1.0) is currently single-threaded
-- # (although it uses MT-safe versions, when possible)
-- """
--     Condition()
-- 
-- Create an edge-triggered event source that tasks can wait for. Tasks that call [`wait`](@ref) on a
-- `Condition` are suspended and queued. Tasks are woken up when [`notify`](@ref) is later called on
-- the `Condition`. Waiting on a condition can return a value or raise an error if the optional arguments
-- of [`notify`](@ref) are used. Edge triggering means that only tasks waiting at the time [`notify`](@ref)
-- is called can be woken up. For level-triggered notifications, you must keep extra state to keep
-- track of whether a notification has happened. The [`Channel`](@ref) and [`Threads.Event`](@ref) types do
-- this, and can be used for level-triggered events.
-- 
-- This object is NOT thread-safe. See [`Threads.Condition`](@ref) for a thread-safe version.
-- """
-- const Condition = GenericCondition{AlwaysLockedST}
-- 
-- /Source

-- Source: base/condition.jl:464-464 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

/--
Julia source: base/condition.jl:5-9 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function concurrency_violation()
    # can be useful for debugging
    #try; error(); catch; ccall(:jlbacktrace, Cvoid, ()); end
    throw(ConcurrencyViolationError("lock must be held"))
end
```
-/
def concurrencyViolation : M E W Unit := throw (r.concurrencyError "lock must be held")

/--
Julia source: base/condition.jl:23-23 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unlockall(l::AbstractLock) = unlock(l) # internal function for implementing `wait`
```
-/
def unlockAll (l : Lock) : M E W Unit := r.unlock l

/--
Julia source: base/condition.jl:24-24 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
relockall(l::AbstractLock, state::Nothing) = lock(l) # internal function for implementing `wait`
```
-/
def relockAll (l : Lock) (_state : Unit) : M E W Unit := r.lock l

/--
Julia source: base/condition.jl:31-31 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
relockall_but_one(l::AbstractLock, state::Nothing) = nothing
```
-/
def relockAllButOne (_l : Lock) (_state : Unit) : M E W Unit := pure ()

/--
Julia source: base/condition.jl:32-33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
assert_havelock(l::AbstractLock, tid::Integer) =
    (islocked(l) && tid == Threads.threadid()) ? nothing : concurrency_violation()
```
-/
def assertHaveLockInteger {L Tid : Type} (islocked : L → M E W Bool)
    (equals : Tid → I → M E W Bool) (l : L) (tid : Tid) : M E W Unit := do
  if ← islocked l then
    if ← equals tid (← JuliaLean.base.threadingconstructs.threadid r.queries) then return ()
  concurrencyViolation r

/--
Julia source: base/condition.jl:34-35 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
assert_havelock(l::AbstractLock, tid::Task) =
    (islocked(l) && tid === current_task()) ? nothing : concurrency_violation()
```
-/
def assertHaveLockTask {L : Type} (islocked : L → M E W Bool)
    (sameTask : Task → Task → Bool) (l : L) (owner : Task) : M E W Unit := do
  if ← islocked l then
    if sameTask owner (← r.currentTask) then return ()
  concurrencyViolation r

/--
Julia source: base/condition.jl:36-36 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
assert_havelock(l::AbstractLock, tid::Nothing) = concurrency_violation()
```
-/
def assertHaveLockNothing (_l : Lock) : M E W Unit := concurrencyViolation r

/--
Julia source: base/condition.jl:53-53 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    AlwaysLockedST() = new(Threads.threadid())
```
-/
def newAlwaysLockedST : M E W AlwaysLockedST := do
  let tid ← JuliaLean.base.threadingconstructs.threadid r.queries
  let owner ← JuliaLean.base.threadingconstructs.liftResult
    ((JInt.convert "Int16" .i16 tid.val).mapError r.queries.juliaError)
  pure ⟨owner⟩

/--
Julia source: base/condition.jl:59-59 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
islocked(::AlwaysLockedST) = true
```
-/
def alwaysIslocked (_l : AlwaysLockedST) : Bool := true

/--
Julia source: base/condition.jl:55-55 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
assert_havelock(l::AlwaysLockedST) = assert_havelock(l, l.ownertid)
```
-/
def assertAlways (l : AlwaysLockedST) : M E W Unit :=
  assertHaveLockInteger r (fun l => pure (alwaysIslocked l))
    (fun (owner : I16) (tid : I) => pure (owner.val == tid.val)) l l.ownerThread

/--
Julia source: base/condition.jl:56-56 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lock(l::AlwaysLockedST) = assert_havelock(l)
```
-/
def lockAlways (l : AlwaysLockedST) : M E W Unit := assertAlways r l

/--
Julia source: base/condition.jl:57-57 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unlock(l::AlwaysLockedST) = assert_havelock(l)
```
-/
def unlockAlways (l : AlwaysLockedST) : M E W Unit := assertAlways r l

/--
Julia source: base/condition.jl:58-58 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
trylock(l::AlwaysLockedST) = l.ownertid == Threads.threadid()
```
-/
def trylockAlways (l : AlwaysLockedST) : M E W Bool := do
  pure (l.ownerThread.val == (← JuliaLean.base.threadingconstructs.threadid r.queries).val)

/--
Julia source: base/condition.jl:79-79 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    GenericCondition{L}() where {L<:AbstractLock} = new{L}(IntrusiveLinkedList{WaitEntry}(), L())
```
-/
def newGenericCondition : M E W (GenericCondition Queue Lock) := do
  let queue ← r.newQueue
  let lock ← r.newLock
  let identity ← r.newIdentity
  pure ⟨identity, queue, lock⟩

/--
Julia source: base/condition.jl:80-80 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    GenericCondition{L}(l::L) where {L<:AbstractLock} = new{L}(IntrusiveLinkedList{WaitEntry}(), l)
```
-/
def newGenericConditionWithLock (lock : Lock) : M E W (GenericCondition Queue Lock) := do
  let queue ← r.newQueue
  let identity ← r.newIdentity
  pure ⟨identity, queue, lock⟩

/--
Julia source: base/condition.jl:81-81 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    GenericCondition(l::AbstractLock) = new{typeof(l)}(IntrusiveLinkedList{WaitEntry}(), l)
```
-/
def newGenericConditionInferred (lock : Lock) : M E W (GenericCondition Queue Lock) := do
  let queue ← r.newQueue
  let identity ← r.newIdentity
  pure ⟨identity, queue, lock⟩

/--
Julia source: base/condition.jl:84-84 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
waitqueue(c::GenericCondition) = ILLRef(c.waitq, c)
```
-/
def waitqueue (c : GenericCondition Queue Lock) : QueueRef Queue Lock := ⟨c.waitq, c⟩

/--
Julia source: base/condition.jl:115-123 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _try_unlink_from!(c::GenericCondition, w::WaitEntry)
    trylock(c.lock) || return false
    try
        list_deletefirst!(waitqueue(c), w)
    finally
        unlock(c.lock)
    end
    return true
end
```
-/
def tryUnlinkFrom (c : GenericCondition Queue Lock) (w : Entry) : M E W Bool := do
  if !(← r.trylock c.lock) then return false
  finallyDo (r.deleteFirst (waitqueue c) w) (r.unlock c.lock)
  pure true

/--
Julia source: base/condition.jl:93-113 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function try_unlink_claimed!(w::WaitEntry)
    ok = true
    for slot in slots(w)
        q = slot.owner
        q === nothing && continue
        # Manual split for --trim (every waitq's identity is its
        # condition - see waitqueue)
        if q isa GenericCondition{Threads.SpinLock}
            _try_unlink_from!(q, w) || (ok = false)
        elseif q isa GenericCondition{ReentrantLock}
            _try_unlink_from!(q, w) || (ok = false)
        elseif q isa GenericCondition{AlwaysLockedST}
            _try_unlink_from!(q, w) || (ok = false)
        elseif q isa CancellationTokenSource
            # sticky source registrations stay in place
        else
            ok = false
        end
    end
    return ok
end
```
-/
def tryUnlinkClaimed (w : Entry) : M E W Bool := do
  let mut ok := true
  for slot in ← r.slots w do
    match ← r.owner slot with
    | none => pure ()
    | some (.spin c) | some (.reentrant c) | some (.always c) =>
      if !(← tryUnlinkFrom r c w) then ok := false
    | some (.cancellation _) => pure ()
    | some .other => ok := false
  pure ok

/--
Julia source: base/condition.jl:125-125 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, c::GenericCondition) = print(io, GenericCondition, "(", c.lock, ")")
```
-/
def showGenericCondition {IO : Type} (print : IO → List (PrintArg Lock) → M E W Unit)
    (io : IO) (c : GenericCondition Queue Lock) : M E W Unit :=
  print io [.genericConditionType, .text "(", .lock c.lock, .text ")"]

/--
Julia source: base/condition.jl:127-127 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
assert_havelock(c::GenericCondition) = assert_havelock(c.lock)
```
-/
def assertCondition (c : GenericCondition Queue Lock) : M E W Unit := r.assertHaveLock c.lock

/--
Julia source: base/condition.jl:128-128 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lock(c::GenericCondition) = lock(c.lock)
```
-/
def lockCondition (c : GenericCondition Queue Lock) : M E W Unit := r.lock c.lock

/--
Julia source: base/condition.jl:131-131 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unlock(c::GenericCondition) = unlock(c.lock)
```
-/
def unlockCondition (c : GenericCondition Queue Lock) : M E W Unit := r.unlock c.lock

/--
Julia source: base/condition.jl:132-132 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
trylock(c::GenericCondition) = trylock(c.lock)
```
-/
def trylockCondition (c : GenericCondition Queue Lock) : M E W Bool := r.trylock c.lock

/--
Julia source: base/condition.jl:133-133 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
islocked(c::GenericCondition) = islocked(c.lock)
```
-/
def islockedCondition (c : GenericCondition Queue Lock) : M E W Bool := r.isLocked c.lock

/--
Julia source: base/condition.jl:135-135 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lock(f, c::GenericCondition) = lock(f, c.lock)
```
-/
def lockBodyCondition {A : Type} (lockBody : M E W A → Lock → M E W A)
    (body : M E W A) (c : GenericCondition Queue Lock) : M E W A := lockBody body c.lock

/--
Julia source: base/condition.jl:140-147 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function wait_enqueue!(c::GenericCondition, w::WaitEntry, first::Bool)
    if first
        pushfirst!(waitqueue(c), w)
    else
        push!(waitqueue(c), w)
    end
    return true
end
```
-/
def waitEnqueue (c : GenericCondition Queue Lock) (w : Entry) (first : Bool) : M E W Bool := do
  if first then r.pushFirst (waitqueue c) w else r.pushLast (waitqueue c) w
  pure true

/--
Julia source: base/condition.jl:148-165 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function wait_dequeue!(c::GenericCondition, w::WaitEntry, why::UInt8)
    # a no-op when a notify already popped the entry. WAKE_VALUE/WAKE_FIRED
    # run under the caller's held lock (the settle after a wake; the fired
    # branch); the cleanup/withdraw whys take it themselves - shielded, a
    # cleanup may be unwinding the very request a cancellable acquire would
    # rethrow
    if why == WAKE_INTERRUPTED || why == WAKE_WITHDRAWN
        _uncancellable_lock(c.lock)
        try
            list_deletefirst!(waitqueue(c), w)
        finally
            unlock(c.lock)
        end
    else
        list_deletefirst!(waitqueue(c), w)
    end
    return nothing
end
```
-/
def waitDequeue (c : GenericCondition Queue Lock) (w : Entry) (why : UInt8) : M E W Unit := do
  if why == r.wakeInterrupted || why == r.wakeWithdrawn then
    r.uncancellableLock c.lock
    finallyDo (r.deleteFirst (waitqueue c) w) (r.unlock c.lock)
  else
    r.deleteFirst (waitqueue c) w

/--
Julia source: base/condition.jl:167-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline _fresh_waiter_error() =
    throw(ConcurrencyViolationError("schedule_on_notify! requires a fresh task: never started, scheduled, or armed"))
```
-/
def freshWaiterError : M E W Unit :=
  throw (r.concurrencyError "schedule_on_notify! requires a fresh task: never started, scheduled, or armed")

/--
Julia source: base/condition.jl:176-180 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_assert_fresh_waiter(waiter::Task) =
    if istaskstarted(waiter) || waiter.queue !== nothing ||
       (@atomic :monotonic waiter.waiting_on) !== nothing
        _fresh_waiter_error()
    end
```
-/
def assertFreshWaiter (waiter : Task) : M E W Unit := do
  if ← r.isTaskStarted waiter then return ← freshWaiterError r
  if (← r.taskQueue waiter).isSome then return ← freshWaiterError r
  if (← r.waitingOn .monotonic waiter).isSome then return ← freshWaiterError r

/--
Julia source: base/condition.jl:186-190 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _schedule_subscription_cancelled(waiter::Task, src::CancellationTokenSource)
    st = @atomic :acquire src.state
    schedule(waiter, CancellationRequest(st), error=true)
    return nothing
end
```
-/
def scheduleSubscriptionCancelled (waiter : Task) (source : Source) : M E W Unit := do
  let state ← r.sourceState .acquire (some source)
  r.schedule waiter (.cancellation state) true

/--
Julia source: base/condition.jl:206-249 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function schedule_on_notify!(c::GenericCondition, waiter::Task, first::Bool=false)
    assert_havelock(c)
    _assert_fresh_waiter(waiter)
    src = _birth_cancel_source(waiter)
    if src !== nothing && iscancelled(src)
        # born cancelled: never enqueue anything
        _schedule_subscription_cancelled(waiter, src)
        return nothing
    end
    w = src === nothing ? _cached_wait_entry(waiter) :
                          _cancel_wait_entry(waiter, src, 0x00)
    _arm_wait(waiter, w)
    if first
        pushfirst!(waitqueue(c), w)
    else
        push!(waitqueue(c), w)
    end
    if src !== nothing
        # the sticky source registration + the publish-then-recheck dance,
        # exactly like a park's phases 4-5 - but claiming back the *waiter's*
        # arm on refusal
        sw = SourceWait(src, 0x00)
        wait_enqueue!(sw, w, false)
        if wait_recheck(sw, w) && disarm!(waiter, w)
            list_deletefirst!(waitqueue(c), w)   # under the held lock
            _schedule_subscription_cancelled(waiter, src)
            return nothing
        end
        # a lost disarm means a concurrent walk claimed the fresh arm: its
        # delivery kills the waiter at start
    end
    # since this is similar to schedule, we should observe the sticky bit now
    if waiter.sticky && Threads.threadid(waiter) == 0 && !GC.in_finalizer()
        # Issue #41324
        # t.sticky && tid == 0 is a task that needs to be co-scheduled with
        # the parent task. If the parent (current_task) is not sticky we must
        # set it to be sticky.
        # XXX: Ideally we would be able to unset this
        current_task().sticky = true
        tid = Threads.threadid()
        ccall(:jl_set_task_tid, Cint, (Any, Cint), waiter, tid-1)
    end
    return w
end
```
-/
def scheduleOnNotify (c : GenericCondition Queue Lock) (waiter : Task)
    (first : Bool := false) : M E W (Option Entry) := do
  assertCondition r c
  assertFreshWaiter r waiter
  let source ← r.birthCancelSource waiter
  match source with
  | some source =>
    if ← r.sourceCancelled source then
      scheduleSubscriptionCancelled r waiter source
      return none
  | none => pure ()
  let w ← match source with
    | none => r.cachedWaitEntry waiter
    | some source => r.cancelWaitEntry waiter source 0
  r.armWait waiter w
  if first then r.pushFirst (waitqueue c) w else r.pushLast (waitqueue c) w
  match source with
  | some source =>
    r.sourceEnqueue source 0 w false
    if ← r.sourceRecheck source 0 w then
      if ← r.disarm waiter w then
        r.deleteFirst (waitqueue c) w
        scheduleSubscriptionCancelled r waiter source
        return none
  | none => pure ()
  if ← r.sticky waiter then
    if (← r.taskThreadId waiter).val == 0 then
      if !(← r.inFinalizer) then
        r.setSticky (← r.currentTask) true
        let tid ← JuliaLean.base.threadingconstructs.threadid r.queries
        r.setTaskThreadId waiter (tid - int 1)
  pure (some w)

/--
Julia source: base/condition.jl:328-405 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function wait(c::GenericCondition, tok::MaybeToken; first::Bool=false,
              min_severity::UInt8=0x00, cancel_value::Bool=false)
    ct = current_task()
    assert_havelock(c)
    src = cancel_source(tok)
    # Entry check (skipped for throwing teardown re-parks; a value-mode
    # wait checks against its floor). For the throwing flavor, like every
    # throw out of this internal layer, the waiting frame's own lock level
    # is released first - callers use the `locked && unlock` idiom; the
    # public kwarg method restores the lock-held contract.
    if src !== nothing && cancel_value
        st = @atomic :acquire src.state
        if st >= max(min_severity, 0x01)
            return CancellationRequest(st)
        end
    elseif src !== nothing && min_severity == 0x00 && iscancelled(src)
        unlock(c.lock)
        checkcancel(src)
        error("cancelled source did not throw")
    end
    if src === nothing
        ws = (c,)
        w = _cached_wait_entry(ct)
    elseif cancel_value
        # Watcher-mode registration: fresh single-use entry (the cache
        # contract in base/park.jl - a cache slot may only carry ordinary
        # cancellable-park registrations).
        ws = (c, WatcherWait(src, max(min_severity, 0x01)))
        w = WaitEntry2(ct)
    else
        ws = (c, SourceWait(src, min_severity))
        w = _cancel_wait_entry(ct, src, min_severity)
    end
    local parked::Bool
    try
        parked = park!(ws, w, first)
    catch
        # an arm-phase throw (contract misuse: this task already carries
        # a foreign registration) happens before any suspend. Nothing is
        # enqueued to settle, but this frame's lock level must still be
        # consumed like every other throw out of this layer - the
        # caller's `locked && unlock` idiom would otherwise leak a held
        # lock, and a leaked SpinLock wedges the process on the next
        # lock of the same object
        disarm!(ct, w)
        withdraw!(ws, w, WAKE_FIRED)
        unlock(c.lock)
        rethrow()
    end
    if !parked
        # the source refused at the registration recheck (the only
        # fireable waitable here): withdraw under the still-held lock and
        # deliver like the entry check (value mode returns lock-held)
        withdraw!(ws, w, WAKE_FIRED)
        if cancel_value
            st = @atomic :acquire src.state
            st >= max(min_severity, 0x01) || error("park fired without a cancelled source")
            return CancellationRequest(st)
        end
        unlock(c.lock)
        checkcancel(src)
        error("park fired without a cancelled source")
    end
    lockstate = unlockall(c.lock)
    r = try
        wait_safe_interrupt(ws, w)
    catch
        # the cleanup already withdrew every registration; restore the
        # enclosing frames' hold, consuming this waiting frame's level -
        # a depth-1 unwind (the common case, e.g. the cancellation being
        # delivered) touches no lock at all
        relockall_but_one(c.lock, lockstate)
        rethrow()
    end
    relockall(c.lock, lockstate)
    withdraw!(ws, w, WAKE_VALUE)   # lazy settle under the reacquired lock
    return r
end
```
-/
def waitToken (c : GenericCondition Queue Lock) (token : Option Token)
    (first : Bool := false) (minSeverity : UInt8 := 0) (cancelValue : Bool := false) :
    M E W (WakeValue Value) := do
  let current ← r.currentTask
  assertCondition r c
  let source := r.cancelSource token
  match source with
  | some source =>
    if cancelValue then
      let state ← r.sourceState .acquire (some source)
      if state ≥ max minSeverity 1 then return .cancellation state
    else if minSeverity == 0 then
      if ← r.sourceCancelled source then
        r.unlock c.lock
        r.checkCancel (some source)
        throw (r.error "cancelled source did not throw")
  | none => pure ()
  let (waitables, w) ← match source with
    | none => do pure ([Waitable.condition c], ← r.cachedWaitEntry current)
    | some source =>
      if cancelValue then do
        pure ([Waitable.condition c, .watcher source (max minSeverity 1)], ← r.newWaitEntry2 current)
      else do
        pure ([Waitable.condition c, .source source minSeverity], ← r.cancelWaitEntry current source minSeverity)
  let parked ← tryCatch (r.park waitables w first) (fun error => do
    let _ ← r.disarm current w
    r.withdraw waitables w r.wakeFired
    r.unlock c.lock
    throw error)
  if !parked then
    r.withdraw waitables w r.wakeFired
    if cancelValue then
      let state ← r.sourceState .acquire source
      if state < max minSeverity 1 then throw (r.error "park fired without a cancelled source")
      return .cancellation state
    r.unlock c.lock
    r.checkCancel source
    throw (r.error "park fired without a cancelled source")
  let lockstate ← r.unlockAll c.lock
  let result ← tryCatch (r.waitSafeInterrupt waitables w) (fun error => do
    r.relockAllButOne c.lock lockstate
    throw error)
  r.relockAll c.lock lockstate
  r.withdraw waitables w r.wakeValue
  pure result

/--
Julia source: base/condition.jl:291-309 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function wait(c::GenericCondition; first::Bool=false,
              cancel::CancelTokenArg=DEFAULT_CANCEL)
    # Check the caller contract here, not just in the internal layer: a
    # violation (not locked, or locked by another task) must propagate
    # with the lock state untouched - the restore in the catch below is
    # only correct for throws that consumed this frame's lock level.
    assert_havelock(c)
    tok = check_cancel_arg(cancel)   # an entry refusal throws lock-held
    try
        return wait(c, tok; first)
    catch
        # the internal layer throws having released this frame's lock
        # level; the public contract is rethrow-with-lock-held (callers
        # are written `lock(c); try ... finally unlock(c)`), so restore
        # one shielded level
        _uncancellable_lock(c.lock)
        rethrow()
    end
end
```
-/
def wait (c : GenericCondition Queue Lock) (first : Bool := false)
    (cancel : CancelArg Token := .default) : M E W (WakeValue Value) := do
  assertCondition r c
  let token ← r.checkCancelArg cancel
  tryCatch (waitToken r c token first) (fun error => do
    r.uncancellableLock c.lock
    throw error)

/--
Julia source: base/condition.jl:417-434 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function notify(c::GenericCondition, @nospecialize(arg), all, error)
    assert_havelock(c)
    cnt = 0
    while !isempty(c.waitq)
        w = popfirst!(waitqueue(c))
        # An entry whose wake was already claimed by an interrupter does not
        # count as woken: drop it and continue to the next waiter (the
        # interrupted task resumes via whatever its claimer scheduled and
        # will find its entry already unlinked).
        t = @atomic :monotonic w.task
        t isa Task || continue
        claim_wait(t, w) || continue
        schedule(t, arg, error=error)
        cnt += 1
        all || break
    end
    return cnt
end
```
-/
def notify (c : GenericCondition Queue Lock) (arg : WakeValue Value)
    (all error : Bool) : M E W I := do
  assertCondition r c
  loop (fun count => do
    if ← r.queueEmpty c.waitq then return .inl count
    let w ← r.popFirst (waitqueue c)
    match ← r.entryTask .monotonic w with
    | none => pure (.inr count)
    | some t =>
      if !(← r.claimWait t w) then return .inr count
      r.schedule t arg error
      let count := count + int 1
      if all then pure (.inr count) else pure (.inl count)) (int 0)

/--
Julia source: base/condition.jl:416-416 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@constprop :none notify(c::GenericCondition, @nospecialize(arg = nothing); all=true, error=false) = notify(c, arg, all, error)
```
-/
def notifyKw (c : GenericCondition Queue Lock) (arg : WakeValue Value := .nothing)
    (all : Bool := true) (error : Bool := false) : M E W I := notify r c arg all error

/--
Julia source: base/condition.jl:436-436 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
notify_error(c::GenericCondition, err) = notify(c, err, true, true)
```
-/
def notifyError (c : GenericCondition Queue Lock) (error : Value) : M E W I :=
  notify r c (.value error) true true

/--
Julia source: base/condition.jl:443-443 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isempty(c::GenericCondition) = _waitq_isempty(waitqueue(c))
```
-/
def isempty (c : GenericCondition Queue Lock) : M E W Bool := r.refEmpty (waitqueue c)

/--
Julia source: base/condition.jl:463-463 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, ::Condition) = print(io, Condition, "()")
```
-/
def showCondition {IO : Type} (print : IO → List (PrintArg Lock) → M E W Unit) (io : IO) : M E W Unit :=
  print io [.conditionType, .text "()"]

/--
Julia source: base/condition.jl:465-466 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lock(c::GenericCondition{AlwaysLockedST}) =
    throw(ArgumentError("`Condition` is not thread-safe. Please use `Threads.Condition` instead for multi-threaded code."))
```
-/
def lockSingleThreadCondition (_c : GenericCondition Queue AlwaysLockedST) : M E W Unit :=
  throw (r.argumentError "`Condition` is not thread-safe. Please use `Threads.Condition` instead for multi-threaded code.")

/--
Julia source: base/condition.jl:467-468 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unlock(c::GenericCondition{AlwaysLockedST}) =
    throw(ArgumentError("`Condition` is not thread-safe. Please use `Threads.Condition` instead for multi-threaded code."))
```
-/
def unlockSingleThreadCondition (_c : GenericCondition Queue AlwaysLockedST) : M E W Unit :=
  throw (r.argumentError "`Condition` is not thread-safe. Please use `Threads.Condition` instead for multi-threaded code.")



end

end JuliaLean.base.condition

namespace JuliaLean.Tasks



/-- A queued `WaitEntry` as observed by `notify`, `base/condition.jl:417-433`.
Entries already claimed by cancellation remain physically linked but are
skipped and do not count as waiting tasks. -/
structure Waiter where
  id : Nat
  claimable : Bool
  deriving Repr, DecidableEq
structure NotifyResult where
  count : Nat
  woken : List Nat
  remaining : List Waiter
  deriving Repr, DecidableEq
/-- `notify(c, arg, all, error)`, `base/condition.jl:417-433`: pop from the
front, skip stale registrations, schedule each claimed task, and stop after
the first successful claim when `all == false`. -/
def notifyModel (all : Bool) : List Waiter → NotifyResult
  | [] => ⟨0, [], []⟩
  | waiter :: waiters =>
      if waiter.claimable then
        if all then
          let rest := notifyModel true waiters
          ⟨rest.count + 1, waiter.id :: rest.woken, rest.remaining⟩
        else
          ⟨1, [waiter.id], waiters⟩
      else
        notifyModel all waiters

end JuliaLean.Tasks

namespace JuliaLean.Tasks



/-! ## base/condition.jl:5-135, lock abstractions and condition wrappers -/

def hasLock (locked : Bool) (owner current : Nat) : Bool := locked && owner == current

def alwaysLockedTry (owner current : Nat) : Bool := owner == current

def conditionWaitQueue (identity : Nat) : Nat := identity

/-! ## base/condition.jl:140-249, queue registration and fresh subscriptions -/

def conditionEnqueue (queue : List Nat) (waiter : Nat) (first : Bool) : List Nat :=
  if first then waiter :: queue else queue ++ [waiter]

def conditionDequeue (queue : List Nat) (waiter : Nat) : List Nat := queue.erase waiter

def freshWaiter (started queued armed : Bool) : Bool := !started && !queued && !armed

def subscribeBody (queue : List Nat) (waiter : Nat) (first cancelled : Bool) :
    List Nat × Bool :=
  if cancelled then (queue, false) else (conditionEnqueue queue waiter first, true)

/-! ## base/condition.jl:291-405, cancellable wait and lock restoration -/

inductive ConditionWaitResult where | blocked | value (value : Nat) | cancelled (severity : Nat)
  deriving Repr, DecidableEq

def conditionWaitBody (cancelled cancelAsValue notified : Bool) (payload severity : Nat) :
    ConditionWaitResult :=
  if cancelled then
    if cancelAsValue then .value severity else .cancelled severity
  else if notified then .value payload else .blocked

/-! ## base/condition.jl:416-468, notify wrappers and display -/

def conditionShow (threadSafe : Bool) : String :=
  if threadSafe then "GenericCondition(lock)" else "Condition()"

end JuliaLean.Tasks
