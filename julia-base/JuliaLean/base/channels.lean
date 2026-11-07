import JuliaLean.Proofs.base.locks_mt.common
import JuliaLean.base.io
import JuliaLean.Core
import JuliaLean.base.float
import JuliaLean.base.reduce
import JuliaLean.base.show
/-!
# Model of `base/channels.jl`

Source-mirrored channel operations with typed scheduler, condition, cancellation,
and mutable-store primitives. Actions retain the world when an exception occurs;
finally blocks therefore observe the lock state left by a throwing wait. A
non-returning wait and an infinite loop both denote nontermination. Atomic loads
and stores retain their source memory order. No scheduling or fairness laws are
assumed. Value conversion and condition wake-value type assertions are explicit.
-/
namespace JuliaLean.base.channels
open JuliaLean
open JuliaLean.base.io (CancelArg)
abbrev I := JInt .i64

def i (value : Int) : I := JInt.wrap .i64 value

inductive MemoryOrder where
  | plain | monotonic | acquire | release
  deriving Repr, DecidableEq

inductive ChannelState where
  | open | closed | other (name : String)
  deriving Repr, DecidableEq

inductive Error (E Task : Type) where
  | julia (error : JlError)
  | invalidState (message state : String)
  | taskFailed (task : Task)
  | user (error : E)
  | concurrencyViolation
  | typeError
  | errorException (message : String)
  | thrownNothing
  | assertion (message : String)

/-- An effect may block forever. Failure retains all completed world updates. -/
structure Action (E W A : Type) where
  run : W → Option (Except (E × W) (A × W))

instance {E W : Type} : Monad (Action E W) where
  pure a := ⟨fun w => some (.ok (a,w))⟩
  bind action next := ⟨fun w => match action.run w with
    | none => none
    | some (.error error) => some (.error error)
    | some (.ok (a,w)) => (next a).run w⟩

instance {E W : Type} : MonadExceptOf E (Action E W) where
  throw error := ⟨fun w => some (.error (error,w))⟩
  tryCatch action handler := ⟨fun w => match action.run w with
    | none => none
    | some (.error (error,w)) => (handler error).run w
    | some (.ok result) => some (.ok result)⟩

section

/-- The shared reduce.jl loop, with a stuck state for a non-returning effect. -/
def loop {E W S A : Type} (step : S → Action E W (Sum A S)) (initial : S) : Action E W A :=
  ⟨fun w => JuliaLean.base.reduce.whileLoop (fun state =>
    match state with
    | none => .ok (.inr none)
    | some (s,w) => match (step s).run w with
      | none => .ok (.inr none)
      | some (.error error) => .error error
      | some (.ok (.inl value,w)) => .ok (.inl (value,w))
      | some (.ok (.inr next,w)) => .ok (.inr (some (next,w)))) (some (initial,w))⟩

structure Frame where
  locked : Bool := true
  didBuffer : Bool := false

abbrev M (E Task W A : Type) := Action (Error E Task) W A
abbrev F (E Task W A : Type) := M E Task (Frame × W) A

def lift {E Task W A : Type} (action : M E Task W A) : F E Task W A :=
  ⟨fun (frame,w) => match action.run w with
    | none => none
    | some (.error (error,w)) => some (.error (error,(frame,w)))
    | some (.ok (value,w)) => some (.ok (value,(frame,w)))⟩

def getFrame {E Task W : Type} : F E Task W Frame := ⟨fun state => some (.ok (state.1,state))⟩
def setFrame {E Task W : Type} (frame : Frame) : F E Task W Unit :=
  ⟨fun (_,w) => some (.ok ((),(frame,w)))⟩
def setLocked {E Task W : Type} (locked : Bool) : F E Task W Unit := do
  setFrame { (← getFrame) with locked := locked }
def setBuffered {E Task W : Type} : F E Task W Unit := do
  setFrame { (← getFrame) with didBuffer := true }

def runFrame {E Task W A : Type} (action : F E Task W A) : M E Task W A :=
  ⟨fun w => match action.run ({},w) with
    | none => none
    | some (.error (error,(_,w))) => some (.error (error,w))
    | some (.ok (value,(_,w))) => some (.ok (value,w))⟩

def finallyDo {E W A : Type} (body : Action E W A) (cleanup : Action E W Unit) : Action E W A := do
  let value ← tryCatch body (fun error => do cleanup; throw error)
  cleanup
  pure value

inductive Notification (T : Type) where
  | nothing
  | value (value : T)

/-- Mutable channel fields and earlier-loaded synchronization/scheduler callees. -/
structure Channel (T Cond E : Type) where
  condTake : Cond
  condWait : Cond
  condPut : Cond
  state : ChannelState
  exception : Option E
  data : List T
  available : I
  sizeMax : I

structure Runtime (E W C Cond Lock Task Waiter Token T : Type) where
  newLock : M E Task W Lock
  newCondition : Lock → M E Task W Cond
  newChannel : Channel T Cond (Error E Task) → M E Task W C
  condTake : C → M E Task W Cond
  condWait : C → M E Task W Cond
  condPut : C → M E Task W Cond
  sizeMax : C → M E Task W I
  loadState : MemoryOrder → C → M E Task W ChannelState
  storeState : MemoryOrder → C → ChannelState → M E Task W Unit
  exception : C → M E Task W (Option (Error E Task))
  setException : C → Error E Task → M E Task W Unit
  data : C → M E Task W (List T)
  setData : C → List T → M E Task W Unit
  loadAvailable : MemoryOrder → C → M E Task W I
  storeAvailable : MemoryOrder → C → I → M E Task W Unit
  lockCondition : Cond → CancelArg Token → M E Task W Unit
  unlockCondition : Cond → M E Task W Unit
  trylockCondition : Cond → M E Task W Bool
  wait : Cond → Option Token → M E Task W (Notification T)
  notify : Cond → Notification T → Bool → Bool → M E Task W I
  notifyError : Cond → Error E Task → M E Task W Unit
  waitQueueEmpty : Cond → M E Task W Bool
  popWaiter : Cond → M E Task W Waiter
  waiterTask : MemoryOrder → Waiter → M E Task W (Option Task)
  claimWait : Task → Waiter → M E Task W Bool
  precheckCancel : CancelArg Token → M E Task W (CancelArg Token)
  resolveCancel : CancelArg Token → M E Task W (Option Token)
  scheduleValue : Task → T → M E Task W Unit
  yieldCurrent : M E Task W Unit

section
variable {E W C Cond Lock Task Waiter Token T : Type}


/--
Julia source: base/channels.jl:178-180 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
closed_exception() = InvalidStateException("Channel is closed.", :closed)

isbuffered(c::Channel) = c.sz_max==0 ? false : true
```
-/
def closedException : Error E Task := .invalidState "Channel is closed." "closed"

def isbuffered (r : Runtime E W C Cond Lock Task Waiter Token T) (c : C) : M E Task W Bool := do
  pure ((← r.sizeMax c).val ≠ 0)

/--
Julia source: base/channels.jl:253-259 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isopen(c::Channel)
    # Use acquire here to pair with release store in `close`, so that subsequent `isready` calls
    # are forced to see `isready == true` if they see `isopen == false`. This means users must
    # call `isopen` before `isready` if you are using the race-y APIs (or call `iterate`, which
    # does this right for you).
    return ((@atomic :acquire c.state) === :open)
end
```
-/
def isopen (r : Runtime E W C Cond Lock Task Waiter Token T) (c : C) : M E Task W Bool := do
  pure ((← r.loadState .acquire c) == .open)

/--
Julia source: base/channels.jl:182-190 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function check_channel_state(c::Channel)
    if !isopen(c)
        # if the monotonic load succeed, now do an acquire fence
        (@atomic :acquire c.state) === :open && concurrency_violation()
        excp = c.excp
        excp !== nothing && throw(excp)
        throw(closed_exception())
    end
end
```
-/
def checkChannelState (r : Runtime E W C Cond Lock Task Waiter Token T) (c : C) : M E Task W Unit := do
  if !(← isopen r c) then
    if (← r.loadState .acquire c) == .open then throw .concurrencyViolation
    match ← r.exception c with
    | some error => throw error
    | none => throw closedException

/--
Julia source: base/channels.jl:698-701 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lock(c::Channel; cancel::CancelTokenArg=DEFAULT_CANCEL) = lock(c.cond_take; cancel)
lock(f, c::Channel) = lock(f, c.cond_take)
unlock(c::Channel) = unlock(c.cond_take)
trylock(c::Channel) = trylock(c.cond_take)
```
-/
def lock (r : Runtime E W C Cond Lock Task Waiter Token T) (c : C)
    (cancel : CancelArg Token := .default) : M E Task W Unit := do r.lockCondition (← r.condTake c) cancel

def lockFunction {A : Type} (r : Runtime E W C Cond Lock Task Waiter Token T)
    (callee : (Unit → M E Task W A) → Cond → M E Task W A)
    (function : Unit → M E Task W A) (c : C) : M E Task W A := do callee function (← r.condTake c)

def unlock (r : Runtime E W C Cond Lock Task Waiter Token T) (c : C) : M E Task W Unit := do
  r.unlockCondition (← r.condTake c)

def trylock (r : Runtime E W C Cond Lock Task Waiter Token T) (c : C) : M E Task W Bool := do
  r.trylockCondition (← r.condTake c)

/--
Julia source: base/channels.jl:408-415 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _increment_n_avail(c, inc)
    # We hold the channel lock so it's safe to non-atomically read and
    # increment c.n_avail_items
    newlen = c.n_avail_items + inc
    # Atomically store c.n_avail_items to prevent data races with other threads
    # reading this outside the lock.
    @atomic :monotonic c.n_avail_items = newlen
end
```
-/
def incrementAvailable (r : Runtime E W C Cond Lock Task Waiter Token T) (c : C) (inc : I) : M E Task W Unit := do
  let old ← r.loadAvailable .plain c
  let value := JInt.wrap .i64 (old.val + inc.val)
  r.storeAvailable .monotonic c value

/--
Julia source: base/channels.jl:199-212 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
close(c::Channel) = close(c, closed_exception()) # nospecialize on default arg seems to confuse makedocs
function close(c::Channel, @nospecialize(excp::Exception))
    lock(c)
    try
        c.excp = excp
        @atomic :release c.state = :closed
        notify_error(c.cond_take, excp)
        notify_error(c.cond_wait, excp)
        notify_error(c.cond_put, excp)
    finally
        unlock(c)
    end
    nothing
end
```
-/
def close (r : Runtime E W C Cond Lock Task Waiter Token T) (c : C)
    (error : Error E Task) : M E Task W Unit := do
  lock r c .default
  finallyDo (do
    r.setException c error
    r.storeState .release c .closed
    r.notifyError (← r.condTake c) error
    r.notifyError (← r.condWait c) error
    r.notifyError (← r.condPut c) error) (unlock r c)

def closeDefault (r : Runtime E W C Cond Lock Task Waiter Token T) (c : C) : M E Task W Unit :=
  close r c closedException

/--
Julia source: base/channels.jl:267-275 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.empty!(c::Channel)
    @lock c begin
        ndrop = length(c.data)
        empty!(c.data)
        _increment_n_avail(c, -ndrop)
        notify(c.cond_put)
    end
    return c
end
```
-/
def empty (r : Runtime E W C Cond Lock Task Waiter Token T) (c : C) : M E Task W C := do
  lock r c .default
  finallyDo (do
    let data ← r.data c
    let ndrop := i data.length
    r.setData c []
    incrementAvailable r c (i (-ndrop.val))
    let _ ← r.notify (← r.condPut c) .nothing true false
    pure ()) (unlock r c)
  pure c

/--
Julia source: base/channels.jl:647-652 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isready(c::Channel) = n_avail(c) > 0
isempty(c::Channel) = n_avail(c) == 0
function n_avail(c::Channel)
    # Lock-free equivalent to `length(c.data) + length(c.cond_put.waitq)`
    @atomic :monotonic c.n_avail_items
end
```
-/
def nAvail (r : Runtime E W C Cond Lock Task Waiter Token T) (c : C) : M E Task W I :=
  r.loadAvailable .monotonic c

def isready (r : Runtime E W C Cond Lock Task Waiter Token T) (c : C) : M E Task W Bool := do
  pure ((← nAvail r c).val > 0)

def isempty (r : Runtime E W C Cond Lock Task Waiter Token T) (c : C) : M E Task W Bool := do
  pure ((← nAvail r c).val = 0)

/--
Julia source: base/channels.jl:693-693 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isfull(c::Channel) = n_avail(c) ≥ c.sz_max
```
-/
def isfull (r : Runtime E W C Cond Lock Task Waiter Token T) (c : C) : M E Task W Bool := do
  pure ((← nAvail r c).val ≥ (← r.sizeMax c).val)

/--
Julia source: base/channels.jl:417-449 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function put_buffered(c::Channel, v, cancel::CancelTokenArg=DEFAULT_CANCEL)
    lock(c; cancel)
    locked = true
    did_buffer = false
    try
        # Increment channel n_avail eagerly (before push!) to count data in the
        # buffer as well as offers from tasks which are blocked in wait().
        _increment_n_avail(c, 1)
        if length(c.data) == c.sz_max
            tok = resolve_cancel_token(cancel)
            while length(c.data) == c.sz_max
                check_channel_state(c)
                locked = false
                wait(c.cond_put, tok)
                locked = true
            end
        end
        check_channel_state(c)
        push!(c.data, v)
        did_buffer = true
        # notify all, since some of the waiters may be on a "fetch" call.
        notify(c.cond_take, nothing, true, false)
    finally
        # Decrement the available items if this task had an exception before
        # pushing the item to the buffer (e.g., during `wait(c.cond_put)`).
        # The fixup needs the lock: reacquire (shielded) when a wait-throw
        # released this frame's level.
        locked || lock(c; cancel=nothing)
        did_buffer || _increment_n_avail(c, -1)
        unlock(c)
    end
    return v
end
```
-/
def putBuffered (r : Runtime E W C Cond Lock Task Waiter Token T) (c : C) (value : T)
    (cancel : CancelArg Token := .default) : M E Task W T := do
  lock r c cancel
  runFrame (finallyDo (do
    lift (incrementAvailable r c (i 1))
    if (i (← lift (r.data c)).length).val = (← lift (r.sizeMax c)).val then
      let token ← lift (r.resolveCancel cancel)
      loop (fun (_ : Unit) => do
        if (i (← lift (r.data c)).length).val ≠ (← lift (r.sizeMax c)).val then
          return .inl ()
        lift (checkChannelState r c)
        setLocked false
        let _ ← lift (r.wait (← lift (r.condPut c)) token)
        setLocked true
        return .inr ()) ()
    lift (checkChannelState r c)
    let data ← lift (r.data c)
    lift (r.setData c (data ++ [value]))
    setBuffered
    let _ ← lift (r.notify (← lift (r.condTake c)) .nothing true false)
    pure value) (do
      let frame ← getFrame
      if !frame.locked then lift (lock r c (.explicit none))
      if !frame.didBuffer then lift (incrementAvailable r c (i (-1)))
      lift (unlock r c)))

/--
Julia source: base/channels.jl:451-487 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function put_unbuffered(c::Channel, v, cancel::CancelTokenArg=DEFAULT_CANCEL)
    lock(c; cancel)
    locked = true
    taker = try
        _increment_n_avail(c, 1)
        tok = resolve_cancel_token(cancel)
        local taker
        while true
            while isempty(c.cond_take.waitq)
                check_channel_state(c)
                notify(c.cond_wait)
                locked = false
                wait(c.cond_put, tok)
                locked = true
            end
            check_channel_state(c)
            # unfair scheduled version of: notify(c.cond_take, v, false, false); yield()
            w = popfirst!(waitqueue(c.cond_take))
            t = @atomic :monotonic w.task
            if t isa Task && claim_wait(t, w)
                taker = t
                break
            end
            # stale registration: this waiter's wake was already claimed
            # by an interrupter - drop it and look for the next taker
        end
        taker
    finally
        # the decrement needs the lock (see put_buffered's finally)
        locked || lock(c; cancel=nothing)
        _increment_n_avail(c, -1)
        unlock(c)
    end
    schedule(taker, v)
    yield()  # immediately give taker a chance to run, but don't block the current task
    return v
end
```
-/
def putUnbuffered (r : Runtime E W C Cond Lock Task Waiter Token T) (c : C) (value : T)
    (cancel : CancelArg Token := .default) : M E Task W T := do
  lock r c cancel
  let taker ← runFrame (finallyDo (do
    lift (incrementAvailable r c (i 1))
    let token ← lift (r.resolveCancel cancel)
    loop (fun (_ : Unit) => do
      loop (fun (_ : Unit) => do
        if !(← lift (r.waitQueueEmpty (← lift (r.condTake c)))) then return .inl ()
        lift (checkChannelState r c)
        let _ ← lift (r.notify (← lift (r.condWait c)) .nothing true false)
        setLocked false
        let _ ← lift (r.wait (← lift (r.condPut c)) token)
        setLocked true
        return .inr ()) ()
      lift (checkChannelState r c)
      let waiter ← lift (r.popWaiter (← lift (r.condTake c)))
      match ← lift (r.waiterTask .monotonic waiter) with
      | some task =>
        if ← lift (r.claimWait task waiter) then return .inl task
        else return .inr ()
      | none => return .inr ()) ()) (do
    if !(← getFrame).locked then lift (lock r c (.explicit none))
    lift (incrementAvailable r c (i (-1)))
    lift (unlock r c)))
  r.scheduleValue taker value
  r.yieldCurrent
  pure value

/--
Julia source: base/channels.jl:400-405 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function put!(c::Channel{T}, v; cancel::CancelTokenArg=DEFAULT_CANCEL) where T
    check_channel_state(c)
    v = convert(T, v)
    cancel = precheck_cancel_arg(cancel)
    return isbuffered(c) ? put_buffered(c, v, cancel) : put_unbuffered(c, v, cancel)
end
```
-/
def put {A : Type} (r : Runtime E W C Cond Lock Task Waiter Token T)
    (convert : A → M E Task W T) (c : C) (value : A) (cancel : CancelArg Token := .default) : M E Task W T := do
  checkChannelState r c
  let value ← convert value
  let cancel ← r.precheckCancel cancel
  if ← isbuffered r c then putBuffered r c value cancel else putUnbuffered r c value cancel

/--
Julia source: base/channels.jl:517-535 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function fetch_buffered(c::Channel, cancel::CancelTokenArg=DEFAULT_CANCEL)
    lock(c; cancel)
    locked = true
    try
        if isempty(c.data)
            tok = resolve_cancel_token(cancel)
            while isempty(c.data)
                check_channel_state(c)
                locked = false
                wait(c.cond_take, tok)
                locked = true
            end
        end
        return c.data[1]
    finally
        locked && unlock(c)
    end
end
fetch_unbuffered(c::Channel) = throw(ErrorException("`fetch` is not supported on an unbuffered Channel."))
```
-/
def fetchBuffered (r : Runtime E W C Cond Lock Task Waiter Token T) (c : C)
    (cancel : CancelArg Token := .default) : M E Task W T := do
  lock r c cancel
  runFrame (finallyDo (do
    if (← lift (r.data c)).isEmpty then
      let token ← lift (r.resolveCancel cancel)
      loop (fun (_ : Unit) => do
        if !(← lift (r.data c)).isEmpty then return .inl ()
        lift (checkChannelState r c)
        setLocked false
        let _ ← lift (r.wait (← lift (r.condTake c)) token)
        setLocked true
        return .inr ()) ()
    match (← lift (r.data c)).head? with
    | some value => pure value
    | none => throw (.julia .boundsError)) (do
      if (← getFrame).locked then lift (unlock r c)))

def fetchUnbuffered (_c : C) : M E Task W T :=
  throw (.errorException "`fetch` is not supported on an unbuffered Channel.")

/--
Julia source: base/channels.jl:513-516 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function fetch(c::Channel; cancel::CancelTokenArg=DEFAULT_CANCEL)
    cancel = precheck_cancel_arg(cancel)
    return isbuffered(c) ? fetch_buffered(c, cancel) : fetch_unbuffered(c)
end
```
-/
def fetch (r : Runtime E W C Cond Lock Task Waiter Token T) (c : C)
    (cancel : CancelArg Token := .default) : M E Task W T := do
  let cancel ← r.precheckCancel cancel
  if ← isbuffered r c then fetchBuffered r c cancel else fetchUnbuffered c

/--
Julia source: base/channels.jl:571-591 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function take_buffered(c::Channel, cancel::CancelTokenArg=DEFAULT_CANCEL)
    lock(c; cancel)
    locked = true
    try
        if isempty(c.data)
            tok = resolve_cancel_token(cancel)
            while isempty(c.data)
                check_channel_state(c)
                locked = false
                wait(c.cond_take, tok)
                locked = true
            end
        end
        v = popfirst!(c.data)
        _increment_n_avail(c, -1)
        notify(c.cond_put, nothing, false, false) # notify only one, since only one slot has become available for a put!.
        return v
    finally
        locked && unlock(c)
    end
end
```
-/
def takeBuffered (r : Runtime E W C Cond Lock Task Waiter Token T) (c : C)
    (cancel : CancelArg Token := .default) : M E Task W T := do
  lock r c cancel
  runFrame (finallyDo (do
    if (← lift (r.data c)).isEmpty then
      let token ← lift (r.resolveCancel cancel)
      loop (fun (_ : Unit) => do
        if !(← lift (r.data c)).isEmpty then return .inl ()
        lift (checkChannelState r c)
        setLocked false
        let _ ← lift (r.wait (← lift (r.condTake c)) token)
        setLocked true
        return .inr ()) ()
    let data ← lift (r.data c)
    let value ← match data with
      | [] => throw (.julia (.argumentError "array must be non-empty"))
      | value :: rest => do lift (r.setData c rest); pure value
    lift (incrementAvailable r c (i (-1)))
    let _ ← lift (r.notify (← lift (r.condPut c)) .nothing false false)
    pure value) (do
      if (← getFrame).locked then lift (unlock r c)))

/--
Julia source: base/channels.jl:594-607 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function take_unbuffered(c::Channel{T}, cancel::CancelTokenArg=DEFAULT_CANCEL) where T
    lock(c; cancel)
    locked = true
    try
        check_channel_state(c)
        notify(c.cond_put, nothing, false, false)
        locked = false
        v = wait(c.cond_take, resolve_cancel_token(cancel))::T
        locked = true
        return v
    finally
        locked && unlock(c)
    end
end
```
-/
def takeUnbuffered (r : Runtime E W C Cond Lock Task Waiter Token T) (c : C)
    (cancel : CancelArg Token := .default) : M E Task W T := do
  lock r c cancel
  runFrame (finallyDo (do
    lift (checkChannelState r c)
    let _ ← lift (r.notify (← lift (r.condPut c)) .nothing false false)
    setLocked false
    let token ← lift (r.resolveCancel cancel)
    let notification ← lift (r.wait (← lift (r.condTake c)) token)
    let value ← match notification with
      | .value value => pure value
      | .nothing => throw .typeError
    setLocked true
    pure value) (do
      if (← getFrame).locked then lift (unlock r c)))

/--
Julia source: base/channels.jl:567-570 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function take!(c::Channel; cancel::CancelTokenArg=DEFAULT_CANCEL)
    cancel = precheck_cancel_arg(cancel)
    return isbuffered(c) ? take_buffered(c, cancel) : take_unbuffered(c, cancel)
end
```
-/
def take (r : Runtime E W C Cond Lock Task Waiter Token T) (c : C)
    (cancel : CancelArg Token := .default) : M E Task W T := do
  let cancel ← r.precheckCancel cancel
  if ← isbuffered r c then takeBuffered r c cancel else takeUnbuffered r c cancel

/--
Julia source: base/channels.jl:727-746 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function wait(c::Channel; cancel::CancelTokenArg=DEFAULT_CANCEL)
    cancel = precheck_cancel_arg(cancel)
    isready(c) && return
    lock(c; cancel)
    locked = true
    try
        if !isready(c)
            tok = resolve_cancel_token(cancel)
            while !isready(c)
                check_channel_state(c)
                locked = false
                wait(c.cond_wait, tok)
                locked = true
            end
        end
    finally
        locked && unlock(c)
    end
    nothing
end
```
-/
def wait (r : Runtime E W C Cond Lock Task Waiter Token T) (c : C)
    (cancel : CancelArg Token := .default) : M E Task W Unit := do
  let cancel ← r.precheckCancel cancel
  if ← isready r c then return ()
  lock r c cancel
  runFrame (finallyDo (do
    if !(← lift (isready r c)) then
      let token ← lift (r.resolveCancel cancel)
      loop (fun (_ : Unit) => do
        if ← lift (isready r c) then return .inl ()
        lift (checkChannelState r c)
        setLocked false
        let _ ← lift (r.wait (← lift (r.condWait c)) token)
        setLocked true
        return .inr ()) ()) (do
    if (← getFrame).locked then lift (unlock r c)))

/--
Julia source: base/channels.jl:769-792 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(c::Channel, state=nothing)
    if isopen(c) || isready(c)
        try
            return (take!(c), nothing)
        catch e
            if isa(e, InvalidStateException) && e.state === :closed
                return nothing
            else
                rethrow()
            end
        end
    else
        # If the channel was closed with an exception, it needs to be thrown
        if (@atomic :acquire c.state) === :closed
            e = c.excp
            if isa(e, InvalidStateException) && e.state === :closed
                nothing
            else
                throw(e)
            end
        end
        return nothing
    end
end
```
-/
def iterateState {State : Type} (r : Runtime E W C Cond Lock Task Waiter Token T) (c : C)
    (_state : State) : M E Task W (Option (T × Unit)) := do
  if (← isopen r c) || (← isready r c) then
    tryCatch (do return some ((← take r c .default),())) (fun error =>
      match error with
      | .invalidState _ "closed" => pure none
      | _ => throw error)
  else
    if (← r.loadState .acquire c) == .closed then
      match ← r.exception c with
      | some (.invalidState _ "closed") => pure ()
      | some error => throw error
      | none => throw .thrownNothing
    pure none

def iterate (r : Runtime E W C Cond Lock Task Waiter Token T) (c : C) : M E Task W (Option (T × Unit)) :=
  iterateState r c ()

/--
Julia source: base/channels.jl:748-748 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{Channel{T}}) where {T} = T
```
-/
def eltype (T : Type) : Type := T

/--
Julia source: base/channels.jl:794-794 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorSize(::Type{<:Channel}) = SizeUnknown()
```
-/
inductive IteratorSize where
  | sizeUnknown
  deriving Repr, DecidableEq

def iteratorSize : IteratorSize := .sizeUnknown

/--
Julia source: base/channels.jl:32-52 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mutable struct Channel{T} <: AbstractChannel{T}
    cond_take::Threads.Condition                 # waiting for data to become available
    cond_wait::Threads.Condition                 # waiting for data to become maybe available
    cond_put::Threads.Condition                  # waiting for a writeable slot
    @atomic state::Symbol
    excp::Union{Exception, Nothing}      # exception to be thrown when state !== :open

    data::Vector{T}
    @atomic n_avail_items::Int           # Available items for taking, can be read without lock
    sz_max::Int                          # maximum size of channel

    function Channel{T}(sz::Integer = 0) where T
        if sz < 0
            throw(ArgumentError("Channel size must be either 0, a positive integer or Inf"))
        end
        lock = ReentrantLock()
        cond_put, cond_take = Threads.Condition(lock), Threads.Condition(lock)
        cond_wait = (sz == 0 ? Threads.Condition(lock) : cond_take) # wait is distinct from take iff unbuffered
        return new(cond_take, cond_wait, cond_put, :open, nothing, Vector{T}(), 0, sz)
    end
end
```
-/
def constructInteger {A : Type} (r : Runtime E W C Cond Lock Task Waiter Token T)
    (negative zero : A → Bool) (toInt : A → M E Task W I) (size : A) : M E Task W C := do
  if negative size then
    throw (.julia (.argumentError "Channel size must be either 0, a positive integer or Inf"))
  let mutex ← r.newLock
  let putCondition ← r.newCondition mutex
  let takeCondition ← r.newCondition mutex
  let waitCondition ← if zero size then r.newCondition mutex else pure takeCondition
  let size ← toInt size
  r.newChannel ⟨takeCondition,waitCondition,putCondition,.open,none,[],i 0,size⟩

def construct (r : Runtime E W C Cond Lock Task Waiter Token T) (size : I := i 0) : M E Task W C :=
  constructInteger r (fun n => n.val < 0) (fun n => n.val = 0) pure size

/--
Julia source: base/channels.jl:54-58 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Channel{T}(sz::Float64) where T
    sz = (sz == Inf ? typemax(Int) : convert(Int, sz))
    return Channel{T}(sz)
end
Channel(sz=0) = Channel{Any}(sz)
```
-/
def constructFloat64 (r : Runtime E W C Cond Lock Task Waiter Token T)
    (size : JuliaLean.base.float.FV .f64) : M E Task W C := do
  let size ← if JuliaLean.base.float.eq_IEEEFloat size JuliaLean.base.float.Inf64 then
    pure (i (2^63-1))
  else match JuliaLean.base.float.intOfFloat .i64 size with
    | .ok value => pure value
    | .error error => throw (.julia error)
  construct r size

def constructDefault (r : Runtime E W C Cond Lock Task Waiter Token T) (size : I := i 0) : M E Task W C :=
  construct r size

def constructAny {Size : Type} (constructType : Size → M E Task W C) (size : Size) : M E Task W C :=
  constructType size

structure TaskRuntime (Ref Pool : Type) where
  newTask : {A : Type} → (Unit → M E Task W A) → M E Task W Task
  withCancellationShield : (Unit → M E Task W Task) → M E Task W Task
  setSticky : Task → Bool → M E Task W Unit
  scheduleOnNotify : Task → Task → M E Task W Unit
  isFailed : Task → M E Task W Bool
  setThreadpool : Task → Pool → M E Task W Unit
  schedule : Task → M E Task W Unit
  yieldTo : Task → M E Task W Unit
  setTaskRef : Ref → Task → M E Task W Unit
  defaultPool : Pool


/--
Julia source: base/channels.jl:367-381 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function close_chnl_on_taskdone(t::Task, c::Channel)
    isopen(c) || return
    lock(c)
    try
        isopen(c) || return
        if istaskfailed(t)
            close(c, TaskFailedException(t))
            return
        end
        close(c)
    finally
        unlock(c)
    end
    nothing
end
```
-/
def closeOnTaskDone {Ref Pool : Type} (r : Runtime E W C Cond Lock Task Waiter Token T)
    (tasks : TaskRuntime (E := E) (Task := Task) (W := W) Ref Pool) (task : Task) (c : C) : M E Task W Unit := do
  if !(← isopen r c) then return ()
  lock r c .default
  finallyDo (do
    if !(← isopen r c) then return ()
    if ← tasks.isFailed task then
      close r c (.taskFailed task)
      return ()
    closeDefault r c) (unlock r c)

/--
Julia source: base/channels.jl:329-339 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function bind(c::Channel, task::Task)
    # the close hook is cleanup: shield it from the constructing scope's
    # cancellation, so a bound channel is closed (and its blocked users
    # released) even when the scope that bound it is cancelled
    T = ScopedValues.with(CANCEL_TOKEN => nothing) do
        Task(() -> close_chnl_on_taskdone(task, c))
    end
    T.sticky = false
    schedule_on_notify!(task, T)
    return c
end
```
-/
def bind {Ref Pool : Type} (r : Runtime E W C Cond Lock Task Waiter Token T)
    (tasks : TaskRuntime (E := E) (Task := Task) (W := W) Ref Pool) (c : C) (task : Task) : M E Task W C := do
  let hook ← tasks.withCancellationShield (fun _ => tasks.newTask (fun _ => closeOnTaskDone r tasks task c))
  tasks.setSticky hook false
  tasks.scheduleOnNotify task hook
  pure c

/--
Julia source: base/channels.jl:139-158 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Channel{T}(func::Function, size=0; taskref=nothing, spawn=false, threadpool=nothing) where T
    chnl = Channel{T}(size)
    task = Task(() -> func(chnl))
    if threadpool === nothing
        threadpool = :default
    else
        spawn = true
    end
    task.sticky = !spawn
    bind(chnl, task)
    if spawn
        Threads._spawn_set_thrpool(task, threadpool)
        schedule(task) # start it on (potentially) another thread
    else
        yield(task) # immediately start it, yielding the current thread
    end
    isa(taskref, Ref{Task}) && (taskref[] = task)
    return chnl
end
Channel(func::Function, args...; kwargs...) = Channel{Any}(func, args...; kwargs...)
```
-/
def constructFunction {Size Ref Pool R : Type} (r : Runtime E W C Cond Lock Task Waiter Token T)
    (tasks : TaskRuntime (E := E) (Task := Task) (W := W) Ref Pool)
    (constructSize : Size → M E Task W C)
    (function : C → M E Task W R) (size : Size) (taskref : Option Ref := none)
    (spawn : Bool := false) (threadpool : Option Pool := none) : M E Task W C := do
  let channel ← constructSize size
  let task ← tasks.newTask (fun _ => function channel)
  let (threadpool,spawn) := match threadpool with
    | none => (tasks.defaultPool,spawn)
    | some pool => (pool,true)
  tasks.setSticky task (!spawn)
  let _ ← bind r tasks channel task
  if spawn then
    tasks.setThreadpool task threadpool
    tasks.schedule task
  else tasks.yieldTo task
  match taskref with
  | some ref => tasks.setTaskRef ref task
  | none => pure ()
  pure channel

def constructFunctionDefault {Size Ref Pool R : Type} (r : Runtime E W C Cond Lock Task Waiter Token T)
    (tasks : TaskRuntime (E := E) (Task := Task) (W := W) Ref Pool)
    (constructSize : Size → M E Task W C)
    (function : C → M E Task W R) (size : Size) (taskref : Option Ref := none)
    (spawn : Bool := false) (threadpool : Option Pool := none) : M E Task W C :=
  constructFunction r tasks constructSize function size taskref spawn threadpool

def constructFunctionZero {Ref Pool R : Type} (r : Runtime E W C Cond Lock Task Waiter Token T)
    (tasks : TaskRuntime (E := E) (Task := Task) (W := W) Ref Pool)
    (function : C → M E Task W R) (taskref : Option Ref := none)
    (spawn : Bool := false) (threadpool : Option Pool := none) : M E Task W C :=
  constructFunction r tasks (fun size => construct r size) function (i 0) taskref spawn threadpool

/--
Julia source: base/channels.jl:352-365 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function channeled_tasks(n::Int, funcs...; ctypes=fill(Any,n), csizes=fill(0,n))
    @assert length(csizes) == n "length(csizes) != n"
    @assert length(ctypes) == n "length(ctypes) != n"

    chnls = map(i -> Channel{ctypes[i]}(csizes[i]), 1:n)
    tasks = Task[ Task(() -> f(chnls...)) for f in funcs ]

    # bind all tasks to all channels and schedule them
    foreach(t -> foreach(c -> bind(c, t), chnls), tasks)
    foreach(schedule, tasks)
    yield() # Allow scheduled tasks to run

    return (chnls, tasks)
end
```
-/
def channeledTasks {Ty Size Ref Pool R : Type} (r : Runtime E W C Cond Lock Task Waiter Token T)
    (tasks : TaskRuntime (E := E) (Task := Task) (W := W) Ref Pool)
    (constructType : Ty → Size → M E Task W C) (n : I)
    (functions : List (List C → M E Task W R)) (types : List Ty) (sizes : List Size) : M E Task W (List C × List Task) := do
  if (i sizes.length).val ≠ n.val then throw (.assertion "length(csizes) != n")
  if (i types.length).val ≠ n.val then throw (.assertion "length(ctypes) != n")
  let mut channels := []
  for index in List.range n.val.toNat do
    let type ← match types[index]? with
      | some type => pure type
      | none => throw (.julia .boundsError)
    let size ← match sizes[index]? with
      | some size => pure size
      | none => throw (.julia .boundsError)
    channels := channels ++ [← constructType type size]
  let mut spawned := []
  for function in functions do
    spawned := spawned ++ [← tasks.newTask (fun _ => function channels)]
  for task in spawned do
    for channel in channels do
      let _ ← bind r tasks channel task
      pure ()
  for task in spawned do tasks.schedule task
  r.yieldCurrent
  pure (channels,spawned)

/--
Julia source: base/channels.jl:10-11 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
push!(c::AbstractChannel, v) = (put!(c, v); c)
popfirst!(c::AbstractChannel) = take!(c)
```
-/
def push {A : Type} (put : C → A → M E Task W T) (c : C) (value : A) : M E Task W C := do
  let _ ← put c value
  pure c

def popfirst (take : C → M E Task W T) (c : C) : M E Task W T := take c

/--
Julia source: base/channels.jl:383-387 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct InvalidStateException <: Exception
    msg::String
    state::Symbol
end
showerror(io::IO, ex::InvalidStateException) = print(io, "InvalidStateException: ", ex.msg)
```
-/
structure InvalidStateException where
  message : String
  state : String
  deriving Repr, DecidableEq

def showInvalidStateException {m : Type → Type} [Monad m]
    [MonadExceptOf JuliaLean.base.show.ShowError m] {Io V : Type}
    (p : JuliaLean.base.show.IOPrims m Io V) (io : JuliaLean.base.show.JIO Io V)
    (error : InvalidStateException) : m Unit :=
  JuliaLean.base.show.printAll p io [JuliaLean.base.show.printStr p io "InvalidStateException: ",
    JuliaLean.base.show.printStr p io error.message]

/--
Julia source: base/channels.jl:750-767 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, c::Channel) = print(io, typeof(c), "(", c.sz_max, ")")

function show(io::IO, ::MIME"text/plain", c::Channel)
    show(io, c)
    if !(get(io, :compact, false)::Bool)
        if !isopen(c)
            print(io, " (closed)")
        else
            n = n_avail(c)
            if n == 0
                print(io, " (empty)")
            else
                s = n == 1 ? "" : "s"
                print(io, " (", n, " item$s available)")
            end
        end
    end
end
```
-/
def showChannel {m : Type → Type} [Monad m] [MonadExceptOf JuliaLean.base.show.ShowError m] {Io V Ty : Type}
    (p : JuliaLean.base.show.IOPrims m Io V)
    (printType : JuliaLean.base.show.JIO Io V → Ty → m Unit)
    (printInt : JuliaLean.base.show.JIO Io V → I → m Unit)
    (io : JuliaLean.base.show.JIO Io V) (type : Ty) (size : I) : m Unit :=
  JuliaLean.base.show.printAll p io [printType io type,JuliaLean.base.show.printStr p io "(",
    printInt io size,JuliaLean.base.show.printStr p io ")"]

def showPlain {m : Type → Type} [Monad m] [MonadExceptOf JuliaLean.base.show.ShowError m] {Io V Ty : Type}
    (p : JuliaLean.base.show.IOPrims m Io V) (a : JuliaLean.base.show.AnyOps V Ty)
    (showChannel : JuliaLean.base.show.JIO Io V → C → m Unit)
    (printInt : JuliaLean.base.show.JIO Io V → I → m Unit)
    (isOpen : C → m Bool) (available : C → m I)
    (io : JuliaLean.base.show.JIO Io V) (c : C) : m Unit := do
  showChannel io c
  if !(← JuliaLean.base.show.assertBool a (JuliaLean.base.show.getIO p io "compact" false)) then
    if !(← isOpen c) then JuliaLean.base.show.printStr p io " (closed)"
    else
      let n ← available c
      if n.val = 0 then JuliaLean.base.show.printStr p io " (empty)"
      else
        let suffix := if n.val = 1 then "" else "s"
        JuliaLean.base.show.printAll p io [JuliaLean.base.show.printStr p io " (",printInt io n,
          JuliaLean.base.show.printStr p io (" item" ++ suffix ++ " available)")]

/--
Julia source: base/channels.jl:165-176 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Channel(func::Function; ctype=nothing, csize=nothing, taskref=nothing, spawn=nothing, threadpool=nothing)
    # The spawn= keyword argument was added in Julia v1.3, and cannot be used with the
    # deprecated keyword arguments `ctype=` or `csize=`.
    if (ctype !== nothing || csize !== nothing) && (spawn !== nothing || threadpool !== nothing)
        throw(ArgumentError("Cannot set `spawn=` or `threadpool=` in the deprecated constructor `Channel(f; ctype=Any, csize=0)`. Please use `Channel{T=Any}(f, size=0; taskref=nothing, spawn=false, threadpool=nothing)` instead!"))
    end
    # Set the actual default values for the arguments.
    ctype === nothing && (ctype = Any)
    csize === nothing && (csize = 0)
    spawn === nothing && (spawn = false)
    return Channel{ctype}(func, csize; taskref=taskref, spawn=spawn, threadpool=threadpool)
end
```
-/
def constructDeprecated {Ty Size Ref Pool Func : Type}
    (anyType : Ty) (zeroSize : Size)
    (specialize : Ty → Func → Size → Option Ref → Bool → Option Pool → M E Task W C)
    (function : Func) (ctype : Option Ty := none) (csize : Option Size := none)
    (taskref : Option Ref := none) (spawn : Option Bool := none) (threadpool : Option Pool := none) : M E Task W C := do
  if (ctype.isSome || csize.isSome) && (spawn.isSome || threadpool.isSome) then
    throw (.julia (.argumentError "Cannot set `spawn=` or `threadpool=` in the deprecated constructor `Channel(f; ctype=Any, csize=0)`. Please use `Channel{T=Any}(f, size=0; taskref=nothing, spawn=false, threadpool=nothing)` instead!"))
  let ctype := ctype.getD anyType
  let csize := csize.getD zeroSize
  let spawn := spawn.getD false
  specialize ctype function csize taskref spawn threadpool

-- Untranslated: type declarations, documentation, or deprecated dynamically typed constructors.
-- UNTRANSLATED
-- Source: base/channels.jl:1-9 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- """
--     AbstractChannel{T}
-- 
-- Representation of a channel passing objects of type `T`.
-- """
-- abstract type AbstractChannel{T} end
-- 
-- /Source

-- Untranslated: type declarations, documentation, or deprecated dynamically typed constructors.
-- UNTRANSLATED
-- Source: base/channels.jl:12-31 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Channel{T=Any}(size::Int=0)
-- 
-- Construct a `Channel` with an internal buffer that can hold a maximum of `size` objects
-- of type `T`.
-- [`put!`](@ref) calls on a full channel block until an object is removed with [`take!`](@ref).
-- 
-- `Channel(0)` constructs an unbuffered channel. `put!` blocks until a matching `take!` is called.
-- And vice-versa.
-- 
-- Other constructors:
-- 
-- * `Channel()`: default constructor, equivalent to `Channel{Any}(0)`
-- * `Channel(Inf)`: equivalent to `Channel{Any}(typemax(Int))`
-- * `Channel(sz)`: equivalent to `Channel{Any}(sz)`
-- 
-- !!! compat "Julia 1.3"
--     The default constructor `Channel()` and default `size=0` were added in Julia 1.3.
-- """
-- /Source

-- Untranslated: type declarations, documentation, or deprecated dynamically typed constructors.
-- UNTRANSLATED
-- Source: base/channels.jl:53-53 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: type declarations, documentation, or deprecated dynamically typed constructors.
-- UNTRANSLATED
-- Source: base/channels.jl:59-138 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # special constructors
-- """
--     Channel{T=Any}(func::Function, size=0; taskref=nothing, spawn=false, threadpool=nothing)
-- 
-- Create a new task from `func`, [`bind`](@ref) it to a new channel of type
-- `T` and size `size`, and schedule the task, all in a single call.
-- The channel is automatically closed when the task terminates.
-- 
-- `func` must accept the bound channel as its only argument.
-- 
-- If you need a reference to the created task, pass a `Ref{Task}` object via
-- the keyword argument `taskref`.
-- 
-- If `spawn=true`, the `Task` created for `func` may be scheduled on another thread
-- in parallel, equivalent to creating a task via [`Threads.@spawn`](@ref).
-- 
-- If `spawn=true` and the `threadpool` argument is not set, it defaults to `:default`.
-- 
-- If the `threadpool` argument is set (to `:default` or `:interactive`), this implies
-- that `spawn=true` and the new Task is spawned to the specified threadpool.
-- 
-- Return a `Channel`.
-- 
-- # Examples
-- ```jldoctest
-- julia> chnl = Channel() do ch
--            foreach(i -> put!(ch, i), 1:4)
--        end;
-- 
-- julia> typeof(chnl)
-- Channel{Any}
-- 
-- julia> for i in chnl
--            @show i
--        end;
-- i = 1
-- i = 2
-- i = 3
-- i = 4
-- ```
-- 
-- Referencing the created task:
-- 
-- ```jldoctest
-- julia> taskref = Ref{Task}();
-- 
-- julia> chnl = Channel(taskref=taskref) do ch
--            println(take!(ch))
--        end;
-- 
-- julia> istaskdone(taskref[])
-- false
-- 
-- julia> put!(chnl, "Hello");
-- Hello
-- 
-- julia> istaskdone(taskref[])
-- true
-- ```
-- 
-- !!! compat "Julia 1.3"
--     The `spawn=` parameter was added in Julia 1.3. This constructor was added in Julia 1.3.
--     In earlier versions of Julia, Channel used keyword arguments to set `size` and `T`, but
--     those constructors are deprecated.
-- 
-- !!! compat "Julia 1.9"
--     The `threadpool=` argument was added in Julia 1.9.
-- 
-- ```jldoctest
-- julia> chnl = Channel{Char}(1, spawn=true) do ch
--            for c in "hello world"
--                put!(ch, c)
--            end
--        end;
-- 
-- julia> String(collect(chnl))
-- "hello world"
-- ```
-- """
-- /Source

-- Untranslated: type declarations, documentation, or deprecated dynamically typed constructors.
-- UNTRANSLATED
-- Source: base/channels.jl:159-164 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # This constructor is deprecated as of Julia v1.3, and should not be used.
-- # (Note that this constructor also matches `Channel(::Function)` w/out any kwargs, which is
-- # of course not deprecated.)
-- # We use `nothing` default values to check which arguments were set in order to throw the
-- # deprecation warning if users try to use `spawn=` with `ctype=` or `csize=`.
-- /Source

-- Untranslated: type declarations, documentation, or deprecated dynamically typed constructors.
-- UNTRANSLATED
-- Source: base/channels.jl:177-177 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: type declarations, documentation, or deprecated dynamically typed constructors.
-- UNTRANSLATED
-- Source: base/channels.jl:181-181 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: type declarations, documentation, or deprecated dynamically typed constructors.
-- UNTRANSLATED
-- Source: base/channels.jl:191-198 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     close(c::Channel[, excp::Exception])
-- 
-- Close a channel. An exception (optionally given by `excp`), is thrown by:
-- 
-- * [`put!`](@ref) on a closed channel.
-- * [`take!`](@ref) and [`fetch`](@ref) on an empty, closed channel.
-- """
-- /Source

-- Untranslated: type declarations, documentation, or deprecated dynamically typed constructors.
-- UNTRANSLATED
-- Source: base/channels.jl:213-252 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     isopen(c::Channel)
-- 
-- Determine whether a [`Channel`](@ref) is open for new [`put!`](@ref) operations.
-- Notice that a `Channel` can be closed and still have buffered elements which can be
-- consumed with [`take!`](@ref).
-- 
-- # Examples
-- 
-- ## Buffered channel with task
-- ```jldoctest
-- julia> c = Channel(ch -> put!(ch, 1), 1);
-- 
-- julia> isopen(c) # The channel is closed to new `put!`s
-- false
-- 
-- julia> isready(c) # The channel is closed but still contains elements
-- true
-- 
-- julia> take!(c)
-- 1
-- 
-- julia> isready(c)
-- false
-- ```
-- 
-- ## Unbuffered channel
-- ```jldoctest
-- julia> c = Channel{Int}();
-- 
-- julia> isopen(c)
-- true
-- 
-- julia> close(c)
-- 
-- julia> isopen(c)
-- false
-- ```
-- """
-- /Source

-- Untranslated: type declarations, documentation, or deprecated dynamically typed constructors.
-- UNTRANSLATED
-- Source: base/channels.jl:260-266 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     empty!(c::Channel)
-- 
-- Empty a Channel `c` by calling `empty!` on the internal buffer.
-- Return the empty channel.
-- """
-- /Source

-- Untranslated: type declarations, documentation, or deprecated dynamically typed constructors.
-- UNTRANSLATED
-- Source: base/channels.jl:276-328 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     bind(chnl::Channel, task::Task)
-- 
-- Associate the lifetime of `chnl` with a task.
-- `Channel` `chnl` is automatically closed when the task terminates.
-- Any uncaught exception in the task is propagated to all waiters on `chnl`.
-- 
-- The `chnl` object can be explicitly closed independent of task termination.
-- Terminating tasks have no effect on already closed `Channel` objects.
-- 
-- When a channel is bound to multiple tasks, the first task to terminate will
-- close the channel. When multiple channels are bound to the same task,
-- termination of the task will close all of the bound channels.
-- 
-- # Examples
-- ```jldoctest
-- julia> c = Channel(0);
-- 
-- julia> task = @async foreach(i->put!(c, i), 1:4);
-- 
-- julia> bind(c,task);
-- 
-- julia> for i in c
--            @show i
--        end;
-- i = 1
-- i = 2
-- i = 3
-- i = 4
-- 
-- julia> isopen(c)
-- false
-- ```
-- 
-- ```jldoctest
-- julia> c = Channel(0);
-- 
-- julia> task = @async (put!(c, 1); error("foo"));
-- 
-- julia> bind(c, task);
-- 
-- julia> take!(c)
-- 1
-- 
-- julia> put!(c, 1);
-- ERROR: TaskFailedException
-- Stacktrace:
-- [...]
--     nested task error: foo
-- [...]
-- ```
-- """
-- /Source

-- Untranslated: type declarations, documentation, or deprecated dynamically typed constructors.
-- UNTRANSLATED
-- Source: base/channels.jl:340-351 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     channeled_tasks(n::Int, funcs...; ctypes=fill(Any,n), csizes=fill(0,n))
-- 
-- A convenience method to create `n` channels and bind them to tasks started
-- from the provided functions in a single call. Each `func` must accept `n` arguments
-- which are the created channels. Channel types and sizes may be specified via
-- keyword arguments `ctypes` and `csizes` respectively. If unspecified, all channels are
-- of type `Channel{Any}(0)`.
-- 
-- Returns a tuple, `(Array{Channel}, Array{Task})`, of the created channels and tasks.
-- """
-- /Source

-- Untranslated: type declarations, documentation, or deprecated dynamically typed constructors.
-- UNTRANSLATED
-- Source: base/channels.jl:366-366 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: type declarations, documentation, or deprecated dynamically typed constructors.
-- UNTRANSLATED
-- Source: base/channels.jl:382-382 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: type declarations, documentation, or deprecated dynamically typed constructors.
-- UNTRANSLATED
-- Source: base/channels.jl:388-399 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     put!(c::Channel, v)
-- 
-- Append an item `v` to the channel `c`. Blocks if the channel is full.
-- 
-- For unbuffered channels, blocks until a [`take!`](@ref) is performed by a different
-- task.
-- 
-- !!! compat "Julia 1.1"
--     `v` now gets converted to the channel's type with [`convert`](@ref) as `put!` is called.
-- """
-- /Source

-- Untranslated: type declarations, documentation, or deprecated dynamically typed constructors.
-- UNTRANSLATED
-- Source: base/channels.jl:406-407 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Atomically update channel n_avail, *assuming* we hold the channel lock.
-- /Source

-- Untranslated: type declarations, documentation, or deprecated dynamically typed constructors.
-- UNTRANSLATED
-- Source: base/channels.jl:416-416 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: type declarations, documentation, or deprecated dynamically typed constructors.
-- UNTRANSLATED
-- Source: base/channels.jl:450-450 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: type declarations, documentation, or deprecated dynamically typed constructors.
-- UNTRANSLATED
-- Source: base/channels.jl:488-512 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     fetch(c::Channel)
-- 
-- Waits for and returns (without removing) the first available item from the `Channel`.
-- Note: `fetch` is unsupported on an unbuffered (0-size) `Channel`.
-- 
-- # Examples
-- 
-- ## Buffered channel
-- ```jldoctest
-- julia> c = Channel(3) do ch
--            foreach(i -> put!(ch, i), 1:3)
--        end;
-- 
-- julia> fetch(c)
-- 1
-- 
-- julia> collect(c)  # item is not removed
-- 3-element Vector{Any}:
--  1
--  2
--  3
-- ```
-- """
-- /Source

-- Untranslated: type declarations, documentation, or deprecated dynamically typed constructors.
-- UNTRANSLATED
-- Source: base/channels.jl:536-566 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     take!(c::Channel)
-- 
-- Removes and returns a value from a [`Channel`](@ref) in order. Blocks until data is available.
-- For unbuffered channels, blocks until a [`put!`](@ref) is performed by a different task.
-- 
-- # Examples
-- 
-- ## Buffered channel
-- ```jldoctest
-- julia> c = Channel(1);
-- 
-- julia> put!(c, 1);
-- 
-- julia> take!(c)
-- 1
-- ```
-- 
-- ## Unbuffered channel
-- ```jldoctest
-- julia> c = Channel(0);
-- 
-- julia> task = Task(() -> put!(c, 1));
-- 
-- julia> schedule(task);
-- 
-- julia> take!(c)
-- 1
-- ```
-- """
-- /Source

-- Untranslated: type declarations, documentation, or deprecated dynamically typed constructors.
-- UNTRANSLATED
-- Source: base/channels.jl:592-593 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # 0-size channel
-- /Source

-- Untranslated: type declarations, documentation, or deprecated dynamically typed constructors.
-- UNTRANSLATED
-- Source: base/channels.jl:608-646 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     isready(c::Channel)
-- 
-- Determine whether a [`Channel`](@ref) has a value stored in it.
-- Returns immediately, does not block.
-- 
-- For unbuffered channels, return `true` if there are tasks waiting on a [`put!`](@ref).
-- 
-- # Examples
-- 
-- ## Buffered channel
-- ```jldoctest
-- julia> c = Channel(1);
-- 
-- julia> isready(c)
-- false
-- 
-- julia> put!(c, 1);
-- 
-- julia> isready(c)
-- true
-- ```
-- 
-- ## Unbuffered channel
-- ```jldoctest
-- julia> c = Channel();
-- 
-- julia> isready(c)  # no tasks waiting to put!
-- false
-- 
-- julia> task = Task(() -> put!(c, 1));
-- 
-- julia> schedule(task);  # schedule a put! task
-- 
-- julia> isready(c)
-- true
-- ```
-- """
-- /Source

-- Untranslated: type declarations, documentation, or deprecated dynamically typed constructors.
-- UNTRANSLATED
-- Source: base/channels.jl:653-692 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     isfull(c::Channel)
-- 
-- Determine if a [`Channel`](@ref) is full, in the sense
-- that calling `put!(c, some_value)` would have blocked.
-- Returns immediately, does not block.
-- 
-- Note that it may frequently be the case that `put!` will
-- not block after this returns `true`. Users must take
-- precautions not to accidentally create live-lock bugs
-- in their code by calling this method, as these are
-- generally harder to debug than deadlocks. It is also
-- possible that `put!` will block after this call
-- returns `false`, if there are multiple producer
-- tasks calling `put!` in parallel.
-- 
-- # Examples
-- 
-- ## Buffered channel
-- ```jldoctest
-- julia> c = Channel(1); # capacity = 1
-- 
-- julia> isfull(c)
-- false
-- 
-- julia> put!(c, 1);
-- 
-- julia> isfull(c)
-- true
-- ```
-- 
-- ## Unbuffered channel
-- ```jldoctest
-- julia> c = Channel(); # capacity = 0
-- 
-- julia> isfull(c) # unbuffered channel is always full
-- true
-- ```
-- """
-- /Source

-- Untranslated: type declarations, documentation, or deprecated dynamically typed constructors.
-- UNTRANSLATED
-- Source: base/channels.jl:694-697 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # the `cancel` forward makes the channel operations' preliminary lock
-- # acquisitions honor their resolved token (or explicit shield); see
-- # lock(::GenericCondition{ReentrantLock})
-- /Source

-- Untranslated: type declarations, documentation, or deprecated dynamically typed constructors.
-- UNTRANSLATED
-- Source: base/channels.jl:702-726 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     wait(c::Channel)
-- 
-- Block until the `Channel` [`isready`](@ref).
-- 
-- ```jldoctest
-- julia> c = Channel(1);
-- 
-- julia> isready(c)
-- false
-- 
-- julia> task = Task(() -> wait(c));
-- 
-- julia> schedule(task);
-- 
-- julia> istaskdone(task)  # task is blocked because channel is not ready
-- false
-- 
-- julia> put!(c, 1);
-- 
-- julia> istaskdone(task)  # task is now unblocked
-- true
-- ```
-- """
-- /Source

-- Untranslated: type declarations, documentation, or deprecated dynamically typed constructors.
-- UNTRANSLATED
-- Source: base/channels.jl:747-747 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: type declarations, documentation, or deprecated dynamically typed constructors.
-- UNTRANSLATED
-- Source: base/channels.jl:749-749 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: type declarations, documentation, or deprecated dynamically typed constructors.
-- UNTRANSLATED
-- Source: base/channels.jl:768-768 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: type declarations, documentation, or deprecated dynamically typed constructors.
-- UNTRANSLATED
-- Source: base/channels.jl:793-793 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

end
end
end JuliaLean.base.channels

namespace JuliaLean.Channels

/-- Channel items: opaque Julia objects. Equal numbers stand for `===` objects. -/
abbrev Val := Nat

/-- Exceptions thrown by channel operations. -/
inductive Exc where
  /-- `InvalidStateException(msg, :closed)`, e.g. `closed_exception()`
  (base/channels.jl:178); `iterate` treats every such exception as the end. -/
  | closed
  /-- Any other exception passed to `close(c, excp)`. -/
  | user (n : Nat)
  /-- `ErrorException("`fetch` is not supported on an unbuffered Channel.")`
  (base/channels.jl:535). -/
  | fetchUnbuffered
  deriving DecidableEq, Repr, Inhabited

/-- The value a parked task is woken with: `notify(c, nothing)`,
`schedule(t, v)`, or `notify(c, e; error=true)`. -/
inductive Wake where
  | none
  | val (v : Val)
  | err (e : Exc)
  deriving DecidableEq, Repr

/-- The channel operation a task performs. `iter` is one call
`iterate(c)` (base/channels.jl:769-792). -/
inductive Op where
  | put (v : Val)
  | take
  | iter
  | fetch
  | wait
  | close (e : Exc)
  | empty
  deriving DecidableEq, Repr

/-- Where a parked task resumes, i.e. which `wait(cond)` call it is in.
`it` records that the `take!` was called by `iterate`. -/
inductive Park where
  /-- `wait(c.cond_put)` in `put_buffered` (base/channels.jl:430). -/
  | putBuf (v : Val)
  /-- `wait(c.cond_put)` in `put_unbuffered` (base/channels.jl:463). -/
  | putUnb (v : Val)
  /-- `wait(c.cond_take)` in `take_buffered` (base/channels.jl:580). -/
  | take (it : Bool)
  /-- `wait(c.cond_take)` in `take_unbuffered` (base/channels.jl:601). -/
  | takeUnb (it : Bool)
  /-- `wait(c.cond_take)` in `fetch_buffered` (base/channels.jl:526). -/
  | fetch
  /-- `wait(c.cond_wait)` in `wait(::Channel)` (base/channels.jl:738). -/
  | wait
  deriving DecidableEq, Repr

/-- Result of an operation: the returned value (`put!` returns `v`, `take!`
and `fetch` the item, `iterate` the item or `nothing`) or the thrown exception. -/
inductive Res where
  | ok (v : Option Val)
  | err (e : Exc)
  deriving DecidableEq, Repr

/-- A task's program counter. -/
inductive Pc where
  /-- Not started. -/
  | start
  /-- `put!` passed its lock-free `check_channel_state` (base/channels.jl:401)
  and is about to lock in `put_buffered`/`put_unbuffered`. -/
  | putLocked (v : Val)
  /-- `iterate` passed `isopen(c) || isready(c)` (base/channels.jl:770) and is
  about to call `take!`. -/
  | takeLocked (it : Bool)
  /-- `wait(c)` passed its lock-free `isready(c)` fast path
  (base/channels.jl:729) and is about to lock. -/
  | waitLocked
  /-- Blocked in a condition wait. -/
  | parked (k : Park)
  /-- Woken from a condition wait, runnable, about to re-acquire the lock. -/
  | woken (k : Park) (w : Wake)
  /-- `put_unbuffered` popped `taker` and released the lock; next it runs
  `schedule(taker, v); yield()` (base/channels.jl:484-485). -/
  | handoff (v : Val) (taker : Nat)
  /-- Finished. -/
  | done (r : Res)
  deriving DecidableEq, Repr

structure Task where
  op : Op
  pc : Pc
  deriving DecidableEq, Repr

/-- The fields of `Channel{T}` (base/channels.jl:32-52). The three conditions
share one lock; for a buffered channel `cond_wait` is `cond_take`
(base/channels.jl:49), so `wait(c)` parks on `qTake` and `qWait` stays empty. -/
structure Chan where
  /-- `sz_max`. -/
  sz : Nat
  /-- `data`. -/
  data : List Val
  /-- `state === :open`. -/
  isOpen : Bool
  /-- `excp`, meaningful once closed (`close` always sets it). -/
  excp : Exc
  /-- `n_avail_items`. -/
  nAvail : Int
  /-- `cond_take.waitq`. -/
  qTake : List Nat
  /-- `cond_put.waitq`. -/
  qPut : List Nat
  /-- `cond_wait.waitq` (unbuffered channels only). -/
  qWait : List Nat
  deriving DecidableEq, Repr

structure St where
  ch : Chan
  tasks : List Task
  /-- Ghost: items discarded by `empty!`. -/
  dropped : List Val
  deriving DecidableEq, Repr

/-! ## Task-list updates -/

/-- Set the program counter of task `i`. -/
def setPc : List Task → Nat → Pc → List Task
  | [], _, _ => []
  | t :: ts, 0, pc => { t with pc := pc } :: ts
  | t :: ts, n + 1, pc => t :: setPc ts n pc

/-- `schedule(t, w)` on a parked task `t`: it becomes runnable with wake value
`w`. A task that is not parked is left alone. -/
def wake : List Task → Nat → Wake → List Task
  | [], _, _ => []
  | t :: ts, 0, w =>
    (match t.pc with
     | .parked k => { t with pc := .woken k w }
     | _ => t) :: ts
  | t :: ts, n + 1, w => t :: wake ts n w

/-- Wake every task of a queue, in FIFO order. -/
def wakeAll (ts : List Task) (q : List Nat) (w : Wake) : List Task :=
  q.foldl (fun ts j => wake ts j w) ts

/-! ## Atomic sections -/
namespace St


def finish (s : St) (i : Nat) (r : Res) : St := { s with tasks := setPc s.tasks i (.done r) }

def goto (s : St) (i : Nat) (pc : Pc) : St := { s with tasks := setPc s.tasks i pc }

def addAvail (s : St) (d : Int) : St := { s with ch := { s.ch with nAvail := s.ch.nAvail + d } }

/-- Park task `i` on `cond_take`. -/
def parkTake (s : St) (i : Nat) (k : Park) : St :=
  { s with ch := { s.ch with qTake := s.ch.qTake ++ [i] }, tasks := setPc s.tasks i (.parked k) }

/-- Park task `i` on `cond_put`. -/
def parkPut (s : St) (i : Nat) (k : Park) : St :=
  { s with ch := { s.ch with qPut := s.ch.qPut ++ [i] }, tasks := setPc s.tasks i (.parked k) }

/-- Park task `i` on `cond_wait` (unbuffered channels). -/
def parkWait (s : St) (i : Nat) (k : Park) : St :=
  { s with ch := { s.ch with qWait := s.ch.qWait ++ [i] }, tasks := setPc s.tasks i (.parked k) }

/-- `notify(c.cond_take, w, true, false)`. -/
def notifyTakeAll (s : St) (w : Wake) : St :=
  { s with ch := { s.ch with qTake := [] }, tasks := wakeAll s.tasks s.ch.qTake w }

/-- `notify(c.cond_put, w, true, false)`. -/
def notifyPutAll (s : St) (w : Wake) : St :=
  { s with ch := { s.ch with qPut := [] }, tasks := wakeAll s.tasks s.ch.qPut w }

/-- `notify(c.cond_wait, w, true, false)`. -/
def notifyWaitAll (s : St) (w : Wake) : St :=
  { s with ch := { s.ch with qWait := [] }, tasks := wakeAll s.tasks s.ch.qWait w }

/-- `notify(c.cond_put, nothing, false, false)`: wake the first waiter, if any. -/
def notifyPutOne (s : St) : St :=
  match s.ch.qPut with
  | [] => s
  | j :: q => { s with ch := { s.ch with qPut := q }, tasks := wake s.tasks j .none }

end St

/-- What `iterate` makes of the result of its `take!`: an
`InvalidStateException` with state `:closed` ends the iteration
(base/channels.jl:773-778). -/
def finishTake (it : Bool) (r : Res) : Res :=
  if it then (match r with | .err .closed => .ok none | r => r) else r

open St

/-- The locked part of `put_buffered` from the `if length(c.data) == c.sz_max`
test on, with `n_avail_items` already incremented (base/channels.jl:425-436),
also run after each wake-up from `wait(c.cond_put)`: if the channel is closed,
`check_channel_state` throws (inside the loop when full, after it otherwise)
and the `finally` block undoes the increment (line 445); if it is full, wait;
otherwise push and `notify(c.cond_take, nothing, true, false)`. -/
def putBufBody (s : St) (i : Nat) (v : Val) : St :=
  if !s.ch.isOpen then (s.addAvail (-1)).finish i (.err s.ch.excp)
  else if s.ch.data.length = s.ch.sz then s.parkPut i (.putBuf v)
  else
    let s := { s with ch := { s.ch with data := s.ch.data ++ [v] } }
    (s.notifyTakeAll .none).finish i (.ok (some v))

/-- The locked loop of `put_unbuffered` (base/channels.jl:458-478) with
`n_avail_items` already incremented: while no taker waits, check the state,
`notify(c.cond_wait)` and wait on `cond_put`; then check the state again, pop
the first taker (whose `claim_wait` succeeds without cancellation), and in the
`finally` block decrement `n_avail_items` and unlock (lines 481-482). -/
def putUnbBody (s : St) (i : Nat) (v : Val) : St :=
  if !s.ch.isOpen then (s.addAvail (-1)).finish i (.err s.ch.excp)
  else match s.ch.qTake with
    | [] => (s.notifyWaitAll .none).parkPut i (.putUnb v)
    | t :: q => ({ s with ch := { s.ch with qTake := q } }.addAvail (-1)).goto i (.handoff v t)

/-- `take_buffered` (base/channels.jl:571-591), also run after each wake-up:
while the buffer is empty, `check_channel_state` then wait on `cond_take`;
then `popfirst!`, decrement `n_avail_items`, and
`notify(c.cond_put, nothing, false, false)`. -/
def takeBufBody (s : St) (i : Nat) (it : Bool) : St :=
  match s.ch.data with
  | [] => if !s.ch.isOpen then s.finish i (finishTake it (.err s.ch.excp)) else s.parkTake i (.take it)
  | v :: d =>
    let s := ({ s with ch := { s.ch with data := d } }.addAvail (-1)).notifyPutOne
    s.finish i (finishTake it (.ok (some v)))

/-- `take_unbuffered` up to its wait (base/channels.jl:594-601):
`check_channel_state`, `notify(c.cond_put, nothing, false, false)`, wait on
`cond_take` for the value a `put!` schedules it with. -/
def takeUnbStart (s : St) (i : Nat) (it : Bool) : St :=
  if !s.ch.isOpen then s.finish i (finishTake it (.err s.ch.excp))
  else s.notifyPutOne.parkTake i (.takeUnb it)

/-- `take!(c)` (base/channels.jl:567-570). -/
def takeBody (s : St) (i : Nat) (it : Bool) : St :=
  if s.ch.sz = 0 then takeUnbStart s i it else takeBufBody s i it

/-- `fetch_buffered` (base/channels.jl:517-534), also run after each wake-up. -/
def fetchBody (s : St) (i : Nat) : St :=
  match s.ch.data with
  | [] => if !s.ch.isOpen then s.finish i (.err s.ch.excp) else s.parkTake i .fetch
  | v :: _ => s.finish i (.ok (some v))

/-- The locked part of `wait(c::Channel)` (base/channels.jl:730-743), also run
after each wake-up: while `!isready(c)`, `check_channel_state` then wait on
`cond_wait` (which is `cond_take` for a buffered channel). -/
def waitBody (s : St) (i : Nat) : St :=
  if s.ch.nAvail > 0 then s.finish i (.ok none)
  else if !s.ch.isOpen then s.finish i (.err s.ch.excp)
  else if s.ch.sz = 0 then s.parkWait i .wait else s.parkTake i .wait

/-- `close(c, excp)` (base/channels.jl:200-212): set `excp` and the state, then
`notify_error` on `cond_take`, `cond_wait`, `cond_put`. -/
def closeBody (s : St) (i : Nat) (e : Exc) : St :=
  let s := { s with ch := { s.ch with excp := e, isOpen := false } }
  let s := s.notifyTakeAll (.err e)
  let s := s.notifyWaitAll (.err e)
  let s := s.notifyPutAll (.err e)
  s.finish i (.ok none)

/-- `empty!(c)` (base/channels.jl:267-275). -/
def emptyBody (s : St) (i : Nat) : St :=
  let n := s.ch.data.length
  let s := { s with ch := { s.ch with data := [] }, dropped := s.dropped ++ s.ch.data }
  ((s.addAvail (-(n : Int))).notifyPutAll .none).finish i (.ok none)

/-- One atomic step of task `i`, or `none` if task `i` does not exist or is not
runnable (parked or done). -/
def stepTask (s : St) (i : Nat) : Option St :=
  match s.tasks[i]? with
  | none => none
  | some t =>
    match t.op, t.pc with
    -- put!: lock-free `check_channel_state(c)` (base/channels.jl:401)
    | .put v, .start => some (if !s.ch.isOpen then s.finish i (.err s.ch.excp) else s.goto i (.putLocked v))
    -- `lock(c)`, `_increment_n_avail(c, 1)` (base/channels.jl:418, 424, 452, 455)
    | _, .putLocked v =>
      some (if s.ch.sz = 0 then putUnbBody (s.addAvail 1) i v else putBufBody (s.addAvail 1) i v)
    | _, .woken (.putBuf v) w =>
      some (match w with
        | .err e => (s.addAvail (-1)).finish i (.err e)
        | _ => putBufBody s i v)
    | _, .woken (.putUnb v) w =>
      some (match w with
        | .err e => (s.addAvail (-1)).finish i (.err e)
        | _ => putUnbBody s i v)
    -- `schedule(taker, v); yield()` (base/channels.jl:484-485)
    | _, .handoff v t => some ({ s with tasks := wake s.tasks t (.val v) }.finish i (.ok (some v)))
    | .take, .start => some (takeBody s i false)
    -- iterate: `isopen(c) || isready(c)`, else the closed branch (base/channels.jl:770-790)
    | .iter, .start =>
      some (if s.ch.isOpen || s.ch.nAvail > 0 then s.goto i (.takeLocked true)
        else s.finish i (if s.ch.excp = .closed then .ok none else .err s.ch.excp))
    | _, .takeLocked it => some (takeBody s i it)
    | _, .woken (.take it) w =>
      some (match w with
        | .err e => s.finish i (finishTake it (.err e))
        | _ => takeBufBody s i it)
    | _, .woken (.takeUnb it) w =>
      some (s.finish i (match w with
        | .err e => finishTake it (.err e)
        | .val v => .ok (some v)
        | .none => .ok none))
    | .fetch, .start => some (if s.ch.sz = 0 then s.finish i (.err .fetchUnbuffered) else fetchBody s i)
    | _, .woken .fetch w =>
      some (match w with
        | .err e => s.finish i (.err e)
        | _ => fetchBody s i)
    -- wait(c): lock-free fast path `isready(c) && return` (base/channels.jl:729)
    | .wait, .start => some (if s.ch.nAvail > 0 then s.finish i (.ok none) else s.goto i .waitLocked)
    | _, .waitLocked => some (waitBody s i)
    | _, .woken .wait w =>
      some (match w with
        | .err e => s.finish i (.err e)
        | _ => waitBody s i)
    | .close e, .start => some (closeBody s i e)
    | .empty, .start => some (emptyBody s i)
    | _, _ => none

/-- A fresh channel of size `sz` and one task per operation, none started. -/
def init (sz : Nat) (ops : List Op) : St :=
  { ch := { sz := sz, data := [], isOpen := true, excp := .closed, nAvail := 0,
            qTake := [], qPut := [], qWait := [] }
    tasks := ops.map fun op => { op := op, pc := .start }
    dropped := [] }

/-- Run a schedule (a list of task ids); ids of non-runnable tasks are
skipped. Used for counterexamples and differential tests. -/
def runSched (s : St) : List Nat → St
  | [] => s
  | i :: is => runSched ((stepTask s i).getD s) is

end JuliaLean.Channels

namespace JuliaLean.ConcurrencyCov.ChannelsCov

open JuliaLean.ConcurrencyCov

def sizeError : String := "Channel size must be either 0, a positive integer or Inf"
/-- Julia integer arguments, distinguishing values that fit the `Int` field. -/
inductive IntegerSize where
  | value (n : Int)
  | positiveOverflow
  deriving DecidableEq, Repr
/-- Float64 classes relevant to `convert(Int, sz)`. -/
inductive FloatSize where
  | positiveInf
  | negativeInf
  | nan
  | integral (n : Int)
  | fractional
  deriving DecidableEq, Repr
structure ChannelState where
  size : Int
  isOpen : Bool := true
  available : Int := 0
  locked : Bool := false
  exception : Option Exn := none
  hooks : Nat := 0
  deriving DecidableEq, Repr
/-- `Channel{T}(sz::Integer)`, lines 43-51, including conversion to the `Int` field. -/
def channelInteger : IntegerSize → R ChannelState
  | .value n => if n < 0 then .error (.argumentError sizeError) else .ok ⟨n, true, 0, false, none, 0⟩
  | .positiveOverflow => .error .inexactError
/-- `Channel{T}(sz::Float64)`, lines 54-57: only positive infinity is handled
before `convert(Int, sz)`. -/
def channelFloat : FloatSize → R ChannelState
  | .positiveInf => channelInteger (.value (2 ^ 63 - 1))
  | .integral n => channelInteger (.value n)
  | .negativeInf | .nan | .fractional => .error .inexactError
inductive SizeArg where
  | integer (size : IntegerSize)
  | float (size : FloatSize)
  deriving DecidableEq, Repr
/-- `Channel(sz=0)` dispatches to `Channel{Any}(sz)` without changing `sz`. -/
def channelDefault : SizeArg → R ChannelState
  | .integer size => channelInteger size
  | .float size => channelFloat size
structure TaskPlan where
  channel : ChannelState
  sticky : Bool
  pool : String
  scheduled : Bool
  taskrefWritten : Bool
  deriving DecidableEq, Repr
/-- `Channel{T}(func, size; ...)`, lines 139-157. -/
def channelFunction (size : IntegerSize) (spawn : Bool) (pool : Option String)
    (taskref : Bool) : R TaskPlan := do
  let ch ← channelInteger size
  let actualPool := pool.getD "default"
  let actualSpawn := spawn || pool.isSome
  return ⟨{ ch with hooks := ch.hooks + 1 }, !actualSpawn, actualPool, actualSpawn, taskref⟩
def channelFunctionAny := channelFunction
/-- Deprecated keyword constructor, lines 165-176. -/
def channelDeprecated (ctypeSet csizeSet spawnSet poolSet : Bool) (size : IntegerSize) : R TaskPlan :=
  if (ctypeSet || csizeSet) && (spawnSet || poolSet) then
    .error (.argumentError "Cannot combine deprecated and scheduling keywords")
  else channelFunction size false none false
def closedException : Exn := .invalidState "Channel is closed." "closed"
def isbuffered (c : ChannelState) : Bool := c.size != 0
def close (c : ChannelState) (e : Exn := closedException) : ChannelState :=
  { c with isOpen := false, exception := some e }
def isopen (c : ChannelState) : Bool := c.isOpen
def bind (c : ChannelState) : ChannelState := { c with hooks := c.hooks + 1 }
inductive TaskStatus where | running | succeeded | failed (task : Nat)
  deriving DecidableEq, Repr
/-- `close_chnl_on_taskdone`, lines 367-381. -/
def closeOnTaskDone (status : TaskStatus) (c : ChannelState) : ChannelState :=
  if !c.isOpen then c else match status with
    | .failed t => close c (.taskFailed t)
    | _ => close c
def channeledTasks (n funcs types sizes : Nat) : R (Nat × Nat) :=
  if sizes != n then .error (.assertionError "length(csizes) != n")
  else if types != n then .error (.assertionError "length(ctypes) != n")
  else .ok (n, funcs)
def showInvalidState (msg : String) : String := "InvalidStateException: " ++ msg
def incrementAvailable (c : ChannelState) (inc : Int) : ChannelState :=
  { c with available := c.available + inc }
def fetchUnbuffered : R Nat := .error (.errorException "`fetch` is not supported on an unbuffered Channel.")
def isempty (c : ChannelState) : Bool := c.available = 0
def isfull (c : ChannelState) : Bool := c.size ≤ c.available
def channelLock (c : ChannelState) : ChannelState := { c with locked := true }
def channelUnlock (c : ChannelState) : ChannelState := { c with locked := false }
def channelTrylock (c : ChannelState) : Bool × ChannelState :=
  if c.locked then (false, c) else (true, channelLock c)
def channelWithLock (body : R Nat) (c : ChannelState) : R Nat × ChannelState :=
  (body, channelUnlock (channelLock c))
def channelEltype (typeName : String) : String := typeName
def channelShow (typeName : String) (c : ChannelState) : String :=
  typeName ++ "(" ++ toString c.size ++ ")"
def channelShowPlain (compact : Bool) (typeName : String) (c : ChannelState) : String :=
  let head := channelShow typeName c
  if compact then head
  else if !c.isOpen then head ++ " (closed)"
  else if c.available = 0 then head ++ " (empty)"
  else head ++ " (" ++ toString c.available ++ " item" ++ (if c.available = 1 then "" else "s") ++ " available)"
inductive IteratorSize where | sizeUnknown
  deriving DecidableEq, Repr
def channelIteratorSize : IteratorSize := .sizeUnknown
def pushWrapper (putResult value : Nat) : Nat × Nat := (putResult, value)
def popfirstWrapper (taken : Nat) : Nat := taken

end JuliaLean.ConcurrencyCov.ChannelsCov

namespace JuliaLean.ConcurrencyCov.FaithfulChannels

open JuliaLean.ConcurrencyCov

def pushAbstract (put : Nat → Nat) (channel value : Nat) := let _ := put value; channel
def popfirstAbstract (take : Nat → Nat) (channel : Nat) := take channel
def channelIntegerM := ChannelsCov.channelInteger
def channelFloatM := ChannelsCov.channelFloat
def channelDefaultM := ChannelsCov.channelDefault
def channelFunctionM := ChannelsCov.channelFunction
def channelFunctionAnyM := ChannelsCov.channelFunctionAny
def closedExceptionM := ChannelsCov.closedException
def isbufferedM := ChannelsCov.isbuffered
def checkChannelState (c : ChannelsCov.ChannelState) : R Unit :=
  if !c.isOpen then match c.exception with | some e => .error e | none => .error ChannelsCov.closedException
  else .ok ()
def closeDefaultM (c : ChannelsCov.ChannelState) := ChannelsCov.close c ChannelsCov.closedException
def closeM (c : ChannelsCov.ChannelState) (e : Exn) := ChannelsCov.close c e
def isopenM := ChannelsCov.isopen
def emptyM := JuliaLean.Channels.emptyBody
def bindM := ChannelsCov.bind
def channeledTasksM := ChannelsCov.channeledTasks
def closeOnTaskDoneM := ChannelsCov.closeOnTaskDone
def showInvalidStateM := ChannelsCov.showInvalidState
def putM (s : JuliaLean.Channels.St) (task value : Nat) :=
  if s.ch.sz = 0 then JuliaLean.Channels.putUnbBody s task value
  else JuliaLean.Channels.putBufBody s task value
def incrementAvailableM (s : JuliaLean.Channels.St) (inc : Int) := s.addAvail inc
def putBufferedM := JuliaLean.Channels.putBufBody
def putUnbufferedM := JuliaLean.Channels.putUnbBody
def fetchM (s : JuliaLean.Channels.St) (task : Nat) :=
  if s.ch.sz = 0 then s.finish task (.err .fetchUnbuffered) else JuliaLean.Channels.fetchBody s task
def fetchBufferedM := JuliaLean.Channels.fetchBody
def fetchUnbufferedM := ChannelsCov.fetchUnbuffered
def takeM := JuliaLean.Channels.takeBody
def takeBufferedM := JuliaLean.Channels.takeBufBody
def takeUnbufferedM := JuliaLean.Channels.takeUnbStart
def isreadyM (s : JuliaLean.Channels.St) : Bool := decide (s.ch.nAvail > 0)
def isemptyM (s : JuliaLean.Channels.St) : Bool := decide (s.ch.nAvail = 0)
def nAvailM (s : JuliaLean.Channels.St) := s.ch.nAvail
def isfullM (s : JuliaLean.Channels.St) : Bool := decide ((s.ch.sz : Int) ≤ s.ch.nAvail)
def lockM := ChannelsCov.channelLock
def lockDoM := ChannelsCov.channelWithLock
def unlockM := ChannelsCov.channelUnlock
def trylockM := ChannelsCov.channelTrylock
def waitM := JuliaLean.Channels.waitBody
def eltypeM := ChannelsCov.channelEltype
def showShortM := ChannelsCov.channelShow
def showPlainM := ChannelsCov.channelShowPlain
def iterateM (s : JuliaLean.Channels.St) (task : Nat) := JuliaLean.Channels.takeBody s task true
def iteratorSizeM := ChannelsCov.channelIteratorSize

end JuliaLean.ConcurrencyCov.FaithfulChannels
