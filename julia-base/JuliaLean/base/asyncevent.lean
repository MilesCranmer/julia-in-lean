import JuliaLean.Core
import JuliaLean.base.io
import JuliaLean.base.int
import JuliaLean.base.float
import JuliaLean.base.pointer

/-!
# Model of `base/asyncevent.jl`

`AsyncCondition`, `Timer`, `sleep`, `timedwait` and the `TimeoutWait` waitable of Julia
`f755f49a9e41380d7da126b3c1db9fe7f83dd027`. Timer and condition objects are references into
the mutable world; their fields are read and written through typed accessors that carry the
source's atomic ordering. libuv calls, the I/O lock, handle preservation, the
`ThreadSynchronizer` condition, task creation and scheduling, cancellation tokens and
`Real` arithmetic are typed parameters with no assumed laws. Exceptions retain mutations and
lock state; `try`/`finally` blocks run their cleanup with the source's `locked` flag and
rethrow. Fuel-free waits retain divergence.
-/

namespace JuliaLean.base.asyncevent

open JuliaLean
open JuliaLean.base.io (M Error whileLoop finallyDo)

abbrev Handle := JuliaLean.base.pointer.Ptr Unit
abbrev CInt := JInt .i32
abbrev U64 := JInt .u64
abbrev I64 := JInt .i64
abbrev F64 := JuliaLean.base.float.FV .f64

/-- `0.0`. -/
def zeroF64 : F64 := JuliaLean.base.float.zero_float .f64

/-- `C_NULL`. -/
def C_NULL : Handle := ⟨JInt.lit .u64 0⟩
def isNull (h : Handle) : Bool := h.address.val == 0

/-- The memory ordering of an atomic field access; `plain` is a field access without one. -/
inductive Ordering where
  | plain
  | monotonic
  | acquire
  | release
  deriving DecidableEq, Repr

/-- Which of `Timer` and `AsyncCondition` an object is (dispatch on `t isa Timer`). -/
inductive Kind where
  | timer
  | asyncCondition
  deriving DecidableEq, Repr

/-- The fields given to `new` for a `Timer` (`timeout_ms`, `interval_ms`) or an
`AsyncCondition` (none). -/
inductive NewFields where
  | asyncCondition
  | timer (timeoutMs intervalMs : U64)

/-- Fields of `Timer`/`AsyncCondition` objects `Obj`, with a `ThreadSynchronizer` `Cond`. -/
structure Fields (World Obj Cond : Type) where
  kind : Obj → Kind
  /-- `new(handle, cond, isopen, set, fields...)`. -/
  new : Handle → Cond → Bool → Bool → NewFields → M World Obj
  handle : Obj → Ordering → M World Handle
  setHandle : Obj → Ordering → Handle → M World Unit
  isopen : Obj → Ordering → M World Bool
  setIsopen : Obj → Ordering → Bool → M World Unit
  set : Obj → Ordering → M World Bool
  setSet : Obj → Ordering → Bool → M World Unit
  cond : Obj → M World Cond
  timeoutMs : Obj → M World U64
  intervalMs : Obj → M World U64

/-- The `ThreadSynchronizer` methods, whose `wait` returns a value of type `V`. -/
structure CondOps (World Cond Task Token V Queue : Type) where
  new : M World Cond
  lock : Cond → M World Unit
  unlock : Cond → M World Unit
  wait : Cond → Option Token → M World V
  notify : Cond → Bool → M World Unit
  scheduleOnNotify : Cond → Task → M World Unit
  waitqueue : Cond → M World Queue
  /-- `ret isa Bool`, with its value. -/
  boolValue : V → Option Bool

/-- The C runtime, libuv and I/O-loop calls. -/
structure UV (World Obj : Type) where
  malloc : U64 → M World Handle
  free : Handle → M World Unit
  sizeofUVAsync : U64
  sizeofUVTimer : U64
  iolockBegin : M World Unit
  iolockEnd : M World Unit
  associateJuliaStruct : Handle → Obj → M World Unit
  disassociateJuliaStruct : Handle → M World Unit
  /-- `ccall(:uv_async_init, ...)` with `eventloop()`, the object and `uv_asynccb`. -/
  asyncInit : Obj → M World CInt
  /-- `eventloop()`. -/
  eventloop : M World Handle
  /-- `ccall(:uv_timer_init, ...)` on the loop and object. -/
  timerInit : Handle → Obj → M World CInt
  updateTime : Handle → M World Unit
  /-- `ccall(:uv_timer_start, ...)` with `uv_timercb`, the timeout and the interval. -/
  timerStart : Handle → U64 → U64 → M World CInt
  timerGetRepeat : Handle → M World U64
  /-- `ccall(:jl_close_uv, ...)`. -/
  closeUV : Handle → M World Unit
  /-- `_UVError(prefix, err)`. -/
  uvError : String → CInt → M World Error
  /-- `finalizer(uvfinalize, this)`. -/
  registerFinalizer : Obj → M World Unit
  preserveHandle : Obj → M World Unit
  unpreserveHandle : Obj → M World Unit
  /-- `@handle_as handle T`. -/
  handleAs : Handle → Kind → M World Obj
  /-- `Core.Intrinsics.atomic_fence(:acquire_release, :system)`. -/
  atomicFence : M World Unit

/-- Tasks, scheduling and cancellation. -/
structure Tasks (World Task Token Waitable Entry : Type) where
  /-- `@task body`. -/
  newTask : M World Unit → M World Task
  /-- `ScopedValues.with(CANCEL_TOKEN => nothing) do ... end`. -/
  withoutCancelToken : {A : Type} → M World A → M World A
  schedule : Task → M World Unit
  /-- `schedule(t, :timed_out)`. -/
  scheduleTimedOut : Task → M World Unit
  currentTask : M World Task
  sticky : Task → M World Bool
  setSticky : Task → Bool → M World Unit
  /-- `Threads._spawn_set_thrpool(t, :interactive)`. -/
  setInteractivePool : Task → M World Unit
  /-- `(@atomicreplace ct.waiting_on w => nothing).success`. -/
  replaceWaitingOn : Task → Entry → M World Bool
  /-- `check_cancel_arg(cancel)`: resolves the argument and checks the token. -/
  checkCancelArg : JuliaLean.base.io.CancelArg Token → M World (Option Token)
  /-- `resolve_cancel_token(cancel)`. -/
  resolveCancelToken : JuliaLean.base.io.CancelArg Token → M World (Option Token)
  /-- `@cancel_check(tok)`. -/
  cancelCheck : Option Token → M World Unit
  /-- `e isa EOFError`. -/
  isEOFError : Error → Bool

/-- The `Real` arguments of the timer constructors, `sleep` and `timedwait`. -/
structure RealOps (World R : Type) where
  /-- `x ≥ 0`. -/
  geZero : R → M World Bool
  iszero : R → M World Bool
  /-- `ceil(UInt64, x * 1000)`. -/
  ceilMillis : R → M World U64
  /-- String interpolation of `x`. -/
  display : R → M World String
  /-- `x ≥ 1e-3`. -/
  geMillisecond : R → M World Bool
  /-- `Float64(x)`. -/
  toFloat64 : R → M World F64

/-- Printing, time and the wall clock. -/
structure Env (World IO V : Type) where
  print : IO → String → M World Unit
  stderr : IO
  /-- `showerror(stderr, err, catch_backtrace())`. -/
  showerror : IO → Error → M World Unit
  /-- String interpolation of a `Float64`. -/
  showFloat : F64 → M World String
  /-- `string(convert(UInt, pointer_from_objref(t)), base = 16, pad = Sys.WORD_SIZE>>2)`. -/
  objrefHex : V → M World String
  timeNs : M World U64

section
variable {World Obj Cond Task Token V Queue Waitable Entry R IO : Type}
variable (f : Fields World Obj Cond) (c : CondOps World Cond Task Token V Queue)
  (uv : UV World Obj)

def capture {A : Type} (action : M World A) : M World (Except Error A) :=
  tryCatch (do pure (.ok (← action))) (fun error => pure (.error error))

def rethrowResult {A : Type} : Except Error A → M World A
  | .ok value => pure value
  | .error error => throw error

/-- Run `action`; an exception carries the value of the source's `locked` flag at that point. -/
def guarded {A : Type} (locked : Bool) (action : M World A) :
    M World (Except (Bool × Error) A) := do
  match ← capture action with
  | .ok value => pure (.ok value)
  | .error error => pure (.error (locked, error))

/-- `@lock l body`: the lock is released even when the body throws. -/
def withLock {Lock A : Type} (lock unlock : Lock → M World Unit) (l : Lock)
    (action : M World A) : M World A := do
  lock l
  finallyDo action (unlock l)

/-- `finally` with a `locked` flag: unlock if locked, unpreserve, then rethrow. -/
def unlockFinally {A : Type} (obj : Obj) (cond : Cond) (result : Except (Bool × Error) A) :
    M World A := do
  let locked := match result with
    | .ok _ => true
    | .error (locked, _) => locked
  if locked then c.unlock cond
  uv.unpreserveHandle obj
  match result with
  | .ok value => pure value
  | .error (_, error) => throw error

-- Reason: The file comment heads the section; it has no method.
-- UNTRANSLATED
-- Source: base/asyncevent.jl:1-4 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- ## async event notifications
-- 
-- /Source

/--
Julia source: base/asyncevent.jl:5-39 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    AsyncCondition()

Create an async condition that wakes up tasks waiting for it
(by calling [`wait`](@ref) on the object)
when notified from C by a call to `uv_async_send`.
Waiting tasks are woken with an [`EOFError`](@ref) when the object is closed (by [`close`](@ref)).
Use [`isopen`](@ref) to check whether it is still active. A closed condition is inactive and will
not wake up tasks.

This provides an implicit acquire & release memory ordering between the sending and waiting threads.
"""
mutable struct AsyncCondition
    @atomic handle::Ptr{Cvoid}
    cond::ThreadSynchronizer
    @atomic isopen::Bool
    @atomic set::Bool

    function AsyncCondition()
        this = new(Libc.malloc(_sizeof_uv_async), ThreadSynchronizer(), true, false)
        iolock_begin()
        associate_julia_struct(this.handle, this)
        err = ccall(:uv_async_init, Cint, (Ptr{Cvoid}, Ptr{Cvoid}, Ptr{Cvoid}),
            eventloop(), this, @cfunction(uv_asynccb, Cvoid, (Ptr{Cvoid},)))
        if err != 0
            #TODO: this codepath is currently not tested
            Libc.free(this.handle)
            this.handle = C_NULL
            throw(_UVError("uv_async_init", err))
        end
        finalizer(uvfinalize, this)
        iolock_end()
        return this
    end
end
```
-/
def asyncConditionNew : M World Obj := do
  let handle ← uv.malloc uv.sizeofUVAsync
  let this ← f.new handle (← c.new) true false .asyncCondition
  uv.iolockBegin
  uv.associateJuliaStruct (← f.handle this .plain) this
  let err ← uv.asyncInit this
  if err.val != 0 then
    uv.free (← f.handle this .plain)
    f.setHandle this .plain C_NULL
    throw (← uv.uvError "uv_async_init" err)
  uv.registerFinalizer this
  uv.iolockEnd
  return this

/--
Julia source: base/asyncevent.jl:171-171 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_convert(::Type{Ptr{Cvoid}}, t::Timer) = t.handle
```
-/
def unsafeConvertTimer (t : Obj) : M World Handle := f.handle t .plain

/--
Julia source: base/asyncevent.jl:172-173 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_convert(::Type{Ptr{Cvoid}}, async::AsyncCondition) = async.handle

```
-/
def unsafeConvertAsync (async : Obj) : M World Handle := f.handle async .plain

/--
Julia source: base/asyncevent.jl:247-248 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isopen(t::Union{Timer, AsyncCondition}) = @atomic :acquire t.isopen

```
-/
def isopen (t : Obj) : M World Bool := f.isopen t .acquire

/--
Julia source: base/asyncevent.jl:249-293 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    close(t::Union{Timer, AsyncCondition})

Close an object `t` and thus mark it as inactive. Once a timer or condition is inactive, it will not produce
a new event.

See also [`isopen`](@ref).
"""
function close(t::Union{Timer, AsyncCondition})
    t.handle == C_NULL && !t.isopen && return # short-circuit path, :monotonic
    iolock_begin()
    if t.handle != C_NULL
        if t.isopen
            @atomic :release t.isopen = false
            ccall(:jl_close_uv, Cvoid, (Ptr{Cvoid},), t)
        end
        # implement _trywait here without the auto-reset function, just waiting for the final close signal
        preserve_handle(t)
        lock(t.cond)
        locked = true
        try
            while t.handle != C_NULL
                iolock_end()
                # close is the cleanup primitive: its (bounded) completion
                # wait is shielded from cancellation
                locked = false
                wait(t.cond, nothing)
                locked = true
                unlock(t.cond)
                locked = false
                iolock_begin()
                lock(t.cond)
                locked = true
            end
        finally
            locked && unlock(t.cond)
            unpreserve_handle(t)
        end
    elseif t.isopen
        @atomic :release t.isopen = false
    end
    iolock_end()
    nothing
end

```
-/
def close (t : Obj) : M World Unit := do
  if isNull (← f.handle t .plain) && !(← f.isopen t .plain) then return
  uv.iolockBegin
  if !isNull (← f.handle t .plain) then
    if ← f.isopen t .plain then
      f.setIsopen t .release false
      uv.closeUV (← unsafeConvertTimer f t)
    uv.preserveHandle t
    let cond ← f.cond t
    c.lock cond
    let result ← whileLoop (fun (_ : Unit) => do
      match ← guarded true (do pure (!isNull (← f.handle t .plain))) with
      | .error e => pure (.inl (.error e))
      | .ok false => pure (.inl (.ok ()))
      | .ok true =>
        let body : ExceptT (Bool × Error) (M World) Unit := do
          ExceptT.mk (guarded true uv.iolockEnd)
          let _ ← ExceptT.mk (guarded false (c.wait cond none))
          ExceptT.mk (guarded true (c.unlock cond))
          ExceptT.mk (guarded false uv.iolockBegin)
          ExceptT.mk (guarded false (c.lock cond))
        match ← body.run with
        | .error e => pure (.inl (.error e))
        | .ok () => pure (.inr ())) ()
    unlockFinally c uv t cond result
  else if ← f.isopen t .plain then
    f.setIsopen t .release false
  uv.iolockEnd

/--
Julia source: base/asyncevent.jl:174-178 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# if this returns true, the object has been signaled
# if this returns false, the object is closed
# a cancellation of the governing token is thrown as a CancellationRequest
_trywait(t::Union{Timer, AsyncCondition}; cancel::CancelTokenArg=DEFAULT_CANCEL) =
    _trywait(t, resolve_cancel_token(cancel))
```
-/
def trywaitDefault (tasks : Tasks World Task Token Waitable Entry)
    (trywait : Obj → Option Token → M World Bool) (t : Obj)
    (cancel : JuliaLean.base.io.CancelArg Token := .default) : M World Bool := do
  trywait t (← tasks.resolveCancelToken cancel)

/--
Julia source: base/asyncevent.jl:179-234 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _trywait(t::Union{Timer, AsyncCondition}, tok::MaybeToken)
    set = t.set
    if set
        # full barrier now for AsyncCondition
        t isa Timer || Core.Intrinsics.atomic_fence(:acquire_release, :system)
    else
        if !isopen(t)
            # the :acquire read of isopen pairs with the :release store in uv_timercb, which
            # sets `set` beforehand: a waiter observing the trigger-initiated close of a
            # one-shot timer cannot miss the trigger on this recheck
            set = t.set
            if !set
                close(t) # wait for the close to complete
                return false
            end
        end
        iolock_begin()
        set = t.set
        if !set
            preserve_handle(t)
            lock(t.cond)
            locked = true
            try
                set = t.set
                while !set && t.handle != C_NULL # wait for set or handle, but not the isopen flag
                    iolock_end()
                    locked = false
                    ret = wait(t.cond, tok)
                    locked = true
                    unlock(t.cond)
                    locked = false
                    iolock_begin()
                    lock(t.cond)
                    locked = true
                    if ret isa Bool
                        set = ret
                        break
                    end
                    # A wakeup that did not come from this object's notify:
                    # re-check the state and re-park.
                    set = t.set
                end
            finally
                locked && unlock(t.cond)
                unpreserve_handle(t)
            end
        end
        iolock_end()
    end
    if !(t isa Timer && iszero(t.interval_ms))
        # if there are multiple waiters, an unspecified number may short-circuit past here
        @atomic :monotonic t.set = false
    end
    return set
end

```
-/
def trywait (t : Obj) (tok : Option Token) : M World Bool := do
  let mut set ← f.set t .plain
  if set then
    if f.kind t != .timer then uv.atomicFence
  else
    if !(← isopen f t) then
      set ← f.set t .plain
      if !set then
        close f c uv t
        return false
    uv.iolockBegin
    set ← f.set t .plain
    if !set then
      uv.preserveHandle t
      let cond ← f.cond t
      c.lock cond
      let first ← guarded true (f.set t .plain)
      let result ← match first with
        | .error e => pure (.error e)
        | .ok s => whileLoop (fun (set : Bool) => do
          match ← guarded true (do pure (!set && !isNull (← f.handle t .plain))) with
          | .error e => pure (.inl (.error e))
          | .ok false => pure (.inl (.ok set))
          | .ok true =>
            let body : ExceptT (Bool × Error) (M World) (Sum Bool Bool) := do
              ExceptT.mk (guarded true uv.iolockEnd)
              let ret ← ExceptT.mk (guarded false (c.wait cond tok))
              ExceptT.mk (guarded true (c.unlock cond))
              ExceptT.mk (guarded false uv.iolockBegin)
              ExceptT.mk (guarded false (c.lock cond))
              match c.boolValue ret with
              | some b => pure (.inl b)
              | none => pure (.inr (← ExceptT.mk (guarded true (f.set t .plain))))
            match ← body.run with
            | .error e => pure (.inl (.error e))
            | .ok (.inl b) => pure (.inl (.ok b))
            | .ok (.inr s) => pure (.inr s)) s
      set ← unlockFinally c uv t cond result
    uv.iolockEnd
  let oneShotTimer ← match f.kind t with
    | .timer => do pure ((← f.intervalMs t).val == 0)
    | .asyncCondition => pure false
  if !oneShotTimer then f.setSet t .monotonic false
  return set

/--
Julia source: base/asyncevent.jl:40-70 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

"""
    AsyncCondition(callback::Function)

Create an async condition that calls the given `callback` function. The `callback` is passed one argument,
the async condition object itself.
"""
function AsyncCondition(cb::Function)
    async = AsyncCondition()
    # Shielded like the `Timer` callback task below: this task owns the
    # handle's lifetime and must survive a cancelled constructing scope.
    t = ScopedValues.with(CANCEL_TOKEN => nothing) do
        @task begin
            unpreserve_handle(async)
            while _trywait(async)
                cb(async)
                isopen(async) || return
            end
        end
    end
    # here we are mimicking parts of _trywait, in coordination with task `t`
    preserve_handle(async)
    @lock async.cond begin
        if async.set
            schedule(t)
        else
            schedule_on_notify!(async.cond, t)
        end
    end
    return async
end
```
-/
def asyncConditionCallback (tasks : Tasks World Task Token Waitable Entry)
    (cb : Obj → M World Unit) : M World Obj := do
  let async ← asyncConditionNew f c uv
  let t ← tasks.withoutCancelToken (tasks.newTask (do
    uv.unpreserveHandle async
    whileLoop (fun (_ : Unit) => do
      if !(← trywait f c uv async none) then return .inl ()
      cb async
      if !(← isopen f async) then return .inl ()
      return .inr ()) ()))
  uv.preserveHandle async
  let cond ← f.cond async
  withLock c.lock c.unlock cond (do
    if ← f.set async .plain then tasks.schedule t
    else c.scheduleOnNotify cond t)
  return async

/--
Julia source: base/asyncevent.jl:71-151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia

## timer-based notifications

"""
    Timer(delay; interval = 0)

Create a timer that wakes up tasks waiting for it (by calling [`wait`](@ref) on the timer object).

Waiting tasks are woken after an initial delay of at least `delay` seconds, and then repeating after
at least `interval` seconds again elapse. If `interval` is equal to `0`, the timer is only triggered
once. When closing (by [`close`](@ref)) either a repeating timer or a one-shot timer before it has
triggered, waiting tasks are woken with an [`EOFError`](@ref). After a one-shot timer triggers, all
subsequent calls to [`wait`](@ref) return immediately, even if it is closed.
`delay` and `interval` have millisecond resolution: they are rounded up to a whole number of
milliseconds, so the minimum nonzero `interval` is 1 millisecond (`interval = 0.001`).
Use [`isopen`](@ref) to check whether a timer is still active. An inactive timer will not fire.
Use `t.timeout` and `t.interval` to read the setup conditions of a `Timer` `t`.

```julia-repl
julia> t = Timer(1.0; interval=0.5)
Timer (open, timeout: 1.0 s, interval: 0.5 s) @0x000000010f4e6e90

julia> isopen(t)
true

julia> t.timeout
1.0

julia> close(t)

julia> isopen(t)
false
```

!!! note
    `interval` is subject to accumulating time skew. If you need precise events at a particular
    absolute time, create a new timer at each expiration with the difference to the next time computed.

!!! note
    A `Timer` requires yield points to update its state. For instance, `isopen(t::Timer)` cannot be
    used to timeout a non-yielding while loop.

!!! compat "Julia 1.12"
    The `timeout` and `interval` readable properties were added in Julia 1.12.

!!! compat "Julia 1.14"
    Prior to Julia 1.14, only the first call to `wait` on a triggered one-shot timer returned,
    and subsequent calls threw an `EOFError`.

"""
mutable struct Timer
    @atomic handle::Ptr{Cvoid}
    cond::ThreadSynchronizer
    @atomic isopen::Bool
    @atomic set::Bool
    timeout_ms::UInt64
    interval_ms::UInt64

    function Timer(timeout::Real; interval::Real = 0.0)
        timeout ≥ 0 || throw(ArgumentError("timer cannot have negative timeout of $timeout seconds"))
        interval ≥ 0 || throw(ArgumentError("timer cannot have negative repeat interval of $interval seconds"))
        # libuv has a tendency to timeout 1 ms early, so we need +1 on the timeout (in milliseconds), unless it is zero
        timeoutms = ceil(UInt64, timeout * 1000) + !iszero(timeout)
        intervalms = ceil(UInt64, interval * 1000)
        loop = eventloop()

        this = new(Libc.malloc(_sizeof_uv_timer), ThreadSynchronizer(), true, false, timeoutms, intervalms)
        associate_julia_struct(this.handle, this)
        iolock_begin()
        err = ccall(:uv_timer_init, Cint, (Ptr{Cvoid}, Ptr{Cvoid}), loop, this)
        @assert err == 0 "failed to initialize timer"
        finalizer(uvfinalize, this)
        ccall(:uv_update_time, Cvoid, (Ptr{Cvoid},), loop)
        err = ccall(:uv_timer_start, Cint, (Ptr{Cvoid}, Ptr{Cvoid}, UInt64, UInt64),
            this, @cfunction(uv_timercb, Cvoid, (Ptr{Cvoid},)),
            timeoutms, intervalms)
        @assert err == 0 "failed to start timer"
        iolock_end()
        return this
    end
end
````
-/
def timerNew {Ri : Type} (r : RealOps World R) (ri : RealOps World Ri) (timeout : R) (interval : Ri) :
    M World Obj := do
  if !(← r.geZero timeout) then
    throw (.jl (.argumentError
      ("timer cannot have negative timeout of " ++ (← r.display timeout) ++ " seconds")))
  if !(← ri.geZero interval) then
    throw (.jl (.argumentError
      ("timer cannot have negative repeat interval of " ++ (← ri.display interval) ++ " seconds")))
  let timeoutms := JuliaLean.base.int.add (← r.ceilMillis timeout)
    (JInt.lit .u64 (if ← r.iszero timeout then 0 else 1))
  let intervalms ← ri.ceilMillis interval
  let loop ← uv.eventloop
  let handle ← uv.malloc uv.sizeofUVTimer
  let this ← f.new handle (← c.new) true false (.timer timeoutms intervalms)
  uv.associateJuliaStruct (← f.handle this .plain) this
  uv.iolockBegin
  let err ← uv.timerInit loop this
  if err.val != 0 then throw (.foreignError "AssertionError" "failed to initialize timer")
  uv.registerFinalizer this
  uv.updateTime loop
  let err ← uv.timerStart (← unsafeConvertTimer f this) timeoutms intervalms
  if err.val != 0 then throw (.foreignError "AssertionError" "failed to start timer")
  uv.iolockEnd
  return this

/-- A property of a `Timer`: `timeout` and `interval` in seconds, or a field. -/
inductive TimerProperty (Field : Type) where
  | seconds (value : F64)
  | field (value : Field)

def millisToSeconds (ms : U64) : F64 :=
  JuliaLean.base.float.div_IEEEFloat (JuliaLean.base.float.float_BitUnsigned64 .f64 ms)
    (JuliaLean.base.float.float_BitSigned64 .f64 (JInt.lit .i64 1000))

/--
Julia source: base/asyncevent.jl:152-161 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getproperty(t::Timer, f::Symbol)
    if f == :timeout
        t.timeout_ms == 0 && return 0.0
        return (t.timeout_ms - 1) / 1000 # remove the +1ms compensation from the constructor
    elseif f == :interval
        return t.interval_ms / 1000
    else
        return getfield(t, f)
    end
end
```
-/
def getproperty {Field : Type} (getfield : Obj → String → M World Field) (t : Obj) (name : String) :
    M World (TimerProperty Field) := do
  if name == "timeout" then
    let ms ← f.timeoutMs t
    if ms.val == 0 then return .seconds (JuliaLean.base.float.zero_float .f64)
    return .seconds (millisToSeconds (JuliaLean.base.int.sub ms (JInt.lit .u64 1)))
  else if name == "interval" then
    return .seconds (millisToSeconds (← f.intervalMs t))
  else
    return .field (← getfield t name)

/--
Julia source: base/asyncevent.jl:162-163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
propertynames(::Timer) = (:handle, :cond, :isopen, :set, :timeout, :timeout_ms, :interval, :interval_ms)

```
-/
def propertynames : List String :=
  ["handle", "cond", "isopen", "set", "timeout", "timeout_ms", "interval", "interval_ms"]

/--
Julia source: base/asyncevent.jl:164-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, t::Timer)
    state = isopen(t) ? "open" : "closed"
    interval = t.interval
    interval_str = interval > 0 ? ", interval: $(t.interval) s" : ""
    print(io, "Timer ($state, timeout: $(t.timeout) s$interval_str) @0x$(string(convert(UInt, pointer_from_objref(t)), base = 16, pad = Sys.WORD_SIZE>>2))")
end

```
-/
def showTimer (env : Env World IO Obj) (io : IO) (t : Obj) : M World Unit := do
  let state := if ← isopen f t then "open" else "closed"
  let interval ← f.intervalMs t
  let intervalSeconds := millisToSeconds interval
  let intervalStr ← if JuliaLean.base.float.lt_IEEEFloat (JuliaLean.base.float.zero_float .f64)
      intervalSeconds then do
      let ms ← f.intervalMs t
      pure (", interval: " ++ (← env.showFloat (millisToSeconds ms)) ++ " s")
    else pure ""
  let timeoutMs ← f.timeoutMs t
  let timeout := if timeoutMs.val == 0 then JuliaLean.base.float.zero_float .f64
    else millisToSeconds (JuliaLean.base.int.sub timeoutMs (JInt.lit .u64 1))
  env.print io ("Timer (" ++ state ++ ", timeout: " ++ (← env.showFloat timeout) ++ " s" ++
    intervalStr ++ ") @0x" ++ (← env.objrefHex t))

/--
Julia source: base/asyncevent.jl:235-236 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
waitqueue(t::Union{Timer, AsyncCondition}) = waitqueue(t.cond)

```
-/
def waitqueue (t : Obj) : M World Queue := do c.waitqueue (← f.cond t)

/--
Julia source: base/asyncevent.jl:239-246 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function wait(t::Union{Timer, AsyncCondition}, tok::MaybeToken)
    ok = _trywait(t, tok)
    @cancel_check(tok)
    ok || throw(EOFError())
    nothing
end


```
-/
def wait (tasks : Tasks World Task Token Waitable Entry) (t : Obj) (tok : Option Token) :
    M World Unit := do
  let ok ← trywait f c uv t tok
  tasks.cancelCheck tok
  if !ok then throw .eofError

/--
Julia source: base/asyncevent.jl:237-238 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
wait(t::Union{Timer, AsyncCondition}; cancel::CancelTokenArg=DEFAULT_CANCEL) =
    wait(t, check_cancel_arg(cancel))
```
-/
def waitDefault (tasks : Tasks World Task Token Waitable Entry) (t : Obj)
    (cancel : JuliaLean.base.io.CancelArg Token := .default) : M World Unit := do
  wait f c uv tasks t (← tasks.checkCancelArg cancel)

/--
Julia source: base/asyncevent.jl:294-313 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function uvfinalize(t::Union{Timer, AsyncCondition})
    iolock_begin()
    lock(t.cond)
    try
        if t.handle != C_NULL
            disassociate_julia_struct(t.handle) # not going to call the usual close hooks anymore
            if t.isopen
                @atomic :release t.isopen = false
                ccall(:jl_close_uv, Cvoid, (Ptr{Cvoid},), t.handle) # this will call Libc.free
            end
            @atomic :monotonic t.handle = C_NULL
            notify(t.cond, false)
        end
    finally
        unlock(t.cond)
    end
    iolock_end()
    nothing
end

```
-/
def uvfinalize (t : Obj) : M World Unit := do
  uv.iolockBegin
  let cond ← f.cond t
  c.lock cond
  let result ← capture (do
    if !isNull (← f.handle t .plain) then
      uv.disassociateJuliaStruct (← f.handle t .plain)
      if ← f.isopen t .plain then
        f.setIsopen t .release false
        uv.closeUV (← f.handle t .plain)
      f.setHandle t .monotonic C_NULL
      c.notify cond false)
  c.unlock cond
  rethrowResult result
  uv.iolockEnd

/--
Julia source: base/asyncevent.jl:314-327 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _uv_hook_close(t::Union{Timer, AsyncCondition})
    lock(t.cond)
    try
        handle = t.handle
        @atomic :release t.isopen = false
        @atomic :monotonic t.handle = C_NULL
        Libc.free(handle)
        notify(t.cond, false)
    finally
        unlock(t.cond)
    end
    nothing
end

```
-/
def uvHookClose (t : Obj) : M World Unit := do
  let cond ← f.cond t
  c.lock cond
  let result ← capture (do
    let handle ← f.handle t .plain
    f.setIsopen t .release false
    f.setHandle t .monotonic C_NULL
    uv.free handle
    c.notify cond false)
  c.unlock cond
  rethrowResult result

/--
Julia source: base/asyncevent.jl:328-339 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function uv_asynccb(handle::Ptr{Cvoid})
    async = @handle_as handle AsyncCondition
    lock(async.cond) # acquire barrier
    try
        @atomic :release async.set = true
        notify(async.cond, true)
    finally
        unlock(async.cond)
    end
    nothing
end

```
-/
def uvAsynccb (handle : Handle) : M World Unit := do
  let async ← uv.handleAs handle .asyncCondition
  let cond ← f.cond async
  c.lock cond
  let result ← capture (do
    f.setSet async .release true
    c.notify cond true)
  c.unlock cond
  rethrowResult result

/--
Julia source: base/asyncevent.jl:340-360 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function uv_timercb(handle::Ptr{Cvoid})
    t = @handle_as handle Timer
    lock(t.cond)
    try
        # this store must stay ordered before the :release store of isopen below, so that
        # a waiter observing the close in _trywait is guaranteed to also observe `set`
        @atomic :monotonic t.set = true
        if ccall(:uv_timer_get_repeat, UInt64, (Ptr{Cvoid},), t) == 0
            # timer is stopped now
            if t.isopen
                @atomic :release t.isopen = false
                ccall(:jl_close_uv, Cvoid, (Ptr{Cvoid},), t)
            end
        end
        notify(t.cond, true)
    finally
        unlock(t.cond)
    end
    nothing
end

```
-/
def uvTimercb (handle : Handle) : M World Unit := do
  let t ← uv.handleAs handle .timer
  let cond ← f.cond t
  c.lock cond
  let result ← capture (do
    f.setSet t .monotonic true
    if (← uv.timerGetRepeat (← unsafeConvertTimer f t)).val == 0 then
      if ← f.isopen t .plain then
        f.setIsopen t .release false
        uv.closeUV (← unsafeConvertTimer f t)
    c.notify cond true)
  c.unlock cond
  rethrowResult result

/--
Julia source: base/asyncevent.jl:361-382 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    sleep(seconds; cancel=Base.DEFAULT_CANCEL)

Block the current task for a specified number of seconds. The minimum sleep time is 1
millisecond or input of `0.001`.

A cancellation of the governing token (by default the scoped token, see
[`CancellationToken`](@ref)) interrupts the sleep by throwing the
[`CancellationRequest`](@ref).
"""
function sleep(sec::Real; cancel::CancelTokenArg=DEFAULT_CANCEL)
    sec ≥ 0 || throw(ArgumentError("cannot sleep for $sec seconds"))
    tok = check_cancel_arg(cancel)
    t = Timer(sec)
    try
        wait(t, tok)
    finally
        close(t)
    end
    nothing
end

```
-/
def sleep (tasks : Tasks World Task Token Waitable Entry) (r : RealOps World R)
    (rf : RealOps World F64)
    (sec : R) (cancel : JuliaLean.base.io.CancelArg Token := .default) : M World Unit := do
  if !(← r.geZero sec) then
    throw (.jl (.argumentError ("cannot sleep for " ++ (← r.display sec) ++ " seconds")))
  let tok ← tasks.checkCancelArg cancel
  let t ← timerNew f c uv r rf sec (zeroF64)
  finallyDo (wait f c uv tasks t tok) (close f c uv t)

/--
Julia source: base/asyncevent.jl:383-455 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
# timer with repeated callback
"""
    Timer(callback::Function, delay; interval = 0, spawn::Union{Nothing,Bool}=nothing)

Create a timer that runs the function `callback` at each timer expiration.

Waiting tasks are woken and the function `callback` is called after an initial delay of `delay`
seconds, and then repeating with the given `interval` in seconds. If `interval` is equal to `0`, the
callback is only run once. The function `callback` is called with a single argument, the timer
itself. Stop a timer by calling `close`. The `callback` may still be run one final time, if the timer
has already expired. `delay` and `interval` are rounded up to a whole number of milliseconds.

If `spawn` is `true`, the created task will be spawned, meaning that it will be allowed
to move thread, which avoids the side-effect of forcing the parent task to get stuck to the thread
it is on. If `spawn` is `nothing` (default), the task will be spawned if the parent task isn't sticky.

!!! compat "Julia 1.12"
    The `spawn` argument was introduced in Julia 1.12.

# Examples

Here the first number is printed after a delay of two seconds, then the following numbers are
printed quickly.

```julia-repl
julia> begin
           i = 0
           cb(timer) = (global i += 1; println(i))
           t = Timer(cb, 2, interval=0.2)
           wait(t)
           sleep(0.5)
           close(t)
       end
1
2
3
```
"""
function Timer(cb::Function, timeout; spawn::Union{Nothing,Bool}=nothing, kwargs...)
    sticky = spawn === nothing ? current_task().sticky : !spawn
    timer = Timer(timeout; kwargs...)
    # The callback task carries the timer's lifetime (its preserve is
    # balanced in the body): shield it from the constructing scope's
    # cancellation token, so a cancelled scope can neither leak the preserve
    # nor stop the timer - `close(timer)` is what ends it.
    t = ScopedValues.with(CANCEL_TOKEN => nothing) do
        @task begin
            unpreserve_handle(timer)
            while _trywait(timer)
                try
                    cb(timer)
                catch err
                    write(stderr, "Error in Timer:\n")
                    showerror(stderr, err, catch_backtrace())
                    return
                end
                isopen(timer) || return
            end
        end
    end
    t.sticky = sticky
    # here we are mimicking parts of _trywait, in coordination with task `t`
    preserve_handle(timer)
    @lock timer.cond begin
        if timer.set
            schedule(t)
        else
            schedule_on_notify!(timer.cond, t)
        end
    end
    return timer
end

````
-/
def timerCallback (tasks : Tasks World Task Token Waitable Entry) (r : RealOps World R)
    (rf : RealOps World F64) (env : Env World IO Obj) (cb : Obj → M World Unit) (timeout : R)
    (spawn : Option Bool := none) (interval : Option R := none) : M World Obj := do
  let sticky ← match spawn with
    | none => do tasks.sticky (← tasks.currentTask)
    | some spawn => pure !spawn
  let timer ← match interval with
    | none => timerNew f c uv r rf timeout zeroF64
    | some interval => timerNew f c uv r r timeout interval
  let t ← tasks.withoutCancelToken (tasks.newTask (do
    uv.unpreserveHandle timer
    whileLoop (fun (_ : Unit) => do
      if !(← trywait f c uv timer none) then return .inl ()
      match ← capture (cb timer) with
      | .error err =>
        env.print env.stderr "Error in Timer:\n"
        env.showerror env.stderr err
        return .inl ()
      | .ok () => pure ()
      if !(← isopen f timer) then return .inl ()
      return .inr ()) ()))
  tasks.setSticky t sticky
  uv.preserveHandle timer
  let cond ← f.cond timer
  withLock c.lock c.unlock cond (do
    if ← f.set timer .plain then tasks.schedule t
    else c.scheduleOnNotify cond t)
  return timer

/-- `1e9 * timeout` and the comparison of a nanosecond count with it. -/
structure TimeoutOps (World R NS : Type) where
  scaleNs : R → M World NS
  exceeds : U64 → NS → M World Bool

/-- `:ok` or `:timed_out`. -/
inductive TimedWaitResult where
  | ok
  | timedOut
  deriving DecidableEq, Repr

/--
Julia source: base/asyncevent.jl:456-497 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    timedwait(testcb, timeout::Real; pollint::Real=0.1)

Wait until `testcb()` returns `true` or `timeout` seconds have passed, whichever is earlier.
The test function is polled every `pollint` seconds. The minimum value for `pollint` is 0.001 seconds,
that is, 1 millisecond.

Return `:ok` or `:timed_out`.

# Examples
```jldoctest
julia> cb() = (sleep(5); return);

julia> t = @async cb();

julia> timedwait(()->istaskdone(t), 1)
:timed_out

julia> timedwait(()->istaskdone(t), 6.5)
:ok
```
"""
function timedwait(testcb, timeout::Real; pollint::Real=0.1)
    pollint >= 1e-3 || throw(ArgumentError("pollint must be ≥ 1 millisecond"))
    start = time_ns()
    ns_timeout = 1e9 * timeout

    testcb() && return :ok

    t = Timer(pollint, interval=pollint)
    while _trywait(t) # stop if we ever get closed
        if testcb()
            close(t)
            return :ok
        elseif (time_ns() -% start) > ns_timeout
            close(t)
            break
        end
    end
    return :timed_out
end

````
-/
def timedwait {NS : Type} (r : RealOps World R) (ns : TimeoutOps World R NS)
    (env : Env World IO Obj) (testcb : M World Bool) (timeout : R) (pollint : R) :
    M World TimedWaitResult := do
  if !(← r.geMillisecond pollint) then
    throw (.jl (.argumentError "pollint must be ≥ 1 millisecond"))
  let start ← env.timeNs
  let nsTimeout ← ns.scaleNs timeout
  if ← testcb then return .ok
  let t ← timerNew f c uv r r pollint pollint
  whileLoop (fun (_ : Unit) => do
    if !(← trywait f c uv t none) then return .inl .timedOut
    if ← testcb then
      close f c uv t
      return .inl .ok
    else if ← ns.exceeds (JuliaLean.base.int.sub (← env.timeNs) start) nsTimeout then
      close f c uv t
      return .inl .timedOut
    return .inr ()) ()

/-- The mutable fields of a `TimeoutWait` reference `TW`. -/
structure TimeoutWaitFields (World TW Obj : Type) where
  new : F64 → Option Obj → M World TW
  timeout : TW → M World F64
  timer : TW → M World (Option Obj)
  setTimer : TW → Option Obj → M World Unit

/--
Julia source: base/asyncevent.jl:498-514 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
## A deadline as a waitable (see base/park.jl): `TimeoutWait(dt)` in a
## park's waitables wakes the wait with `:timed_out` after `dt` seconds.
## Its enqueue - running inside `park!`, after the arm - starts the timer
## and spawns the claimer task, which wakes the parked task through the
## standard expected-entry claim CAS. That CAS is a *specific-wait* waker:
## it is only sound against a fresh, single-use entry (which the entry
## cache contract supplies automatically - any non-canonical waitable
## shape gets a fresh entry), since entry identity is what scopes the
## claim to this wait and not a later one of the same task. The claimed
## waitq registration is left for the driver's lazy settle; the dequeue
## closes the timer on every exit path.
mutable struct TimeoutWait
    const timeout::Float64
    timer::Union{Timer, Nothing}
    TimeoutWait(timeout::Real) = new(Float64(timeout), nothing)
end

```
-/
def timeoutWaitNew {TW : Type} (tw : TimeoutWaitFields World TW Obj) (r : RealOps World R)
    (timeout : R) : M World TW := do
  tw.new (← r.toFloat64 timeout) none

/--
Julia source: base/asyncevent.jl:515-538 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function wait_enqueue!(x::TimeoutWait, w::WaitEntry, first::Bool)
    ct = current_task()
    timer = Timer(x.timeout)
    x.timer = timer
    t = Task() do
        try
            # not cancellable: internal mechanism; closing the timer wakes
            # this task on every exit path of the governed wait
            wait(timer; cancel=nothing)
        catch e
            # a closed timer means the wait ended first; do nothing
            e isa EOFError && return
            rethrow()
        end
        if (@atomicreplace ct.waiting_on w => nothing).success
            schedule(ct, :timed_out)
        end
    end
    t.sticky = false
    Threads._spawn_set_thrpool(t, :interactive)
    schedule(t)
    return true
end

```
-/
def waitEnqueue {TW : Type} (tasks : Tasks World Task Token Waitable Entry)
    (rf : RealOps World F64) (tw : TimeoutWaitFields World TW Obj) (x : TW) (w : Entry)
    (_first : Bool) : M World Bool := do
  let ct ← tasks.currentTask
  let timer ← timerNew f c uv rf rf (← tw.timeout x) zeroF64
  tw.setTimer x (some timer)
  let t ← tasks.newTask (do
    match ← capture (wait f c uv tasks timer none) with
    | .error e => if tasks.isEOFError e then return else throw e
    | .ok () => pure ()
    if ← tasks.replaceWaitingOn ct w then tasks.scheduleTimedOut ct)
  tasks.setSticky t false
  tasks.setInteractivePool t
  tasks.schedule t
  return true

/--
Julia source: base/asyncevent.jl:539-544 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function wait_dequeue!(x::TimeoutWait, w::WaitEntry, why::UInt8)
    timer = x.timer
    timer === nothing || close(timer)
    x.timer = nothing
    return nothing
end
```
-/
def waitDequeue {TW : Type} (tw : TimeoutWaitFields World TW Obj) (x : TW) (_w : Entry)
    (_why : UInt8) : M World Unit := do
  match ← tw.timer x with
  | none => pure ()
  | some timer => close f c uv timer
  tw.setTimer x none

end

end JuliaLean.base.asyncevent


namespace JuliaLean.Streams

/-! ## Timer and AsyncCondition -/

inductive EventKind where
  | oneShotTimer
  | repeatingTimer
  | asyncCondition
  deriving Repr, DecidableEq

structure EventM where
  kind : EventKind
  isopen : Bool
  set : Bool
  deriving Repr, DecidableEq

def freshEvent (kind : EventKind) : EventM := ⟨kind, true, false⟩

/-- `close(::Union{Timer,AsyncCondition})`, `base/asyncevent.jl:257-292`. -/
def closeEvent (e : EventM) : EventM := { e with isopen := false }

/-- libuv notification callbacks, `base/asyncevent.jl:328-358`. A one-shot
timer becomes inactive while preserving its triggered bit. -/
def signalEvent (e : EventM) : EventM :=
  if !e.isopen then e
  else match e.kind with
    | .oneShotTimer => { e with isopen := false, set := true }
    | .repeatingTimer | .asyncCondition => { e with set := true }

/-- `_trywait` followed by `wait`, `base/asyncevent.jl:177-243`. Master keeps
the set bit on a one-shot timer, so later waits also return. -/
def waitEvent (e : EventM) : SR EventM :=
  if e.set then
    .ok (if e.kind == .oneShotTimer then e else { e with set := false })
  else if !e.isopen then .error .eofError
  else .error .ioError

end JuliaLean.Streams

namespace JuliaLean.Streams

/-! ## `base/asyncevent.jl` -/

structure TimerSetup where
  timeoutMs : Nat
  intervalMs : Nat
  deriving Repr, DecidableEq

def ceilMillis (microseconds : Nat) : Nat := (microseconds + 999) / 1000

def timerSetup (timeoutUs intervalUs : Nat) : TimerSetup :=
  let timeout := ceilMillis timeoutUs
  { timeoutMs := timeout + if timeoutUs = 0 then 0 else 1,
    intervalMs := ceilMillis intervalUs }

def timerTimeout (t : TimerSetup) : Nat :=
  if t.timeoutMs = 0 then 0 else t.timeoutMs - 1

def timerProperties (t : TimerSetup) : Nat × Nat := (timerTimeout t, t.intervalMs)
def timerShowState (e : EventM) : String := if e.isopen then "open" else "closed"
def callbackShouldContinue (e : EventM) : Bool := e.set && e.isopen
def sleepFinalState (e : EventM) : EventM := closeEvent e

def timedwaitResult (tests : List Bool) (polls : Nat) : Bool :=
  (tests.take (polls + 1)).any id

structure TimeoutWaitM where
  timeoutMs : Nat
  armed : Bool
  deriving Repr, DecidableEq

def timeoutEnqueue (t : TimeoutWaitM) : TimeoutWaitM := { t with armed := true }
def timeoutDequeue (t : TimeoutWaitM) : TimeoutWaitM := { t with armed := false }


end JuliaLean.Streams

namespace JuliaLean.Streams.Methods.AsyncEvent

open JuliaLean.Streams

structure AsyncM where
  event : EventM
  hasHandle : Bool
  timeoutMs : Nat
  intervalMs : Nat
  deriving Repr, DecidableEq

def freshAsync (kind : EventKind) (timeout interval : Nat := 0) : AsyncM :=
  ⟨freshEvent kind, true, timeout, interval⟩

inductive TimerField where
  | timeout | interval | handle | isopen | set
  deriving Repr, DecidableEq

inductive TimerValue where
  | natural (value : Nat)
  | boolean (value : Bool)
  deriving Repr, DecidableEq

inductive TimedWaitResult where | ok | timedOut
  deriving Repr, DecidableEq

/-- `AsyncCondition()`, `base/asyncevent.jl:23-38`. -/
def m23 (initCode : Int) : Except StreamErr AsyncM :=
  let state := freshAsync .asyncCondition
  if initCode != 0 then .error .ioError else .ok state

/-- `AsyncCondition(cb)`, `base/asyncevent.jl:47-70`. -/
def m47 (state : AsyncM) : AsyncM × Bool :=
  (state, state.event.set)

/-- `Timer(timeout; interval)`, `base/asyncevent.jl:129-150`. -/
def m129 (timeoutUs intervalUs : Int) (initOk startOk : Bool) : Except StreamErr AsyncM :=
  if timeoutUs < 0 || intervalUs < 0 then .error .argumentError
  else if !initOk || !startOk then .error .ioError
  else
    let setup := timerSetup timeoutUs.toNat intervalUs.toNat
    let kind := if intervalUs = 0 then EventKind.oneShotTimer else .repeatingTimer
    .ok (freshAsync kind setup.timeoutMs setup.intervalMs)

/-- `getproperty(t::Timer, f)`, `base/asyncevent.jl:152-161`. -/
def m152 (state : AsyncM) (field : TimerField) : TimerValue :=
  match field with
  | .timeout => .natural (if state.timeoutMs = 0 then 0 else state.timeoutMs - 1)
  | .interval => .natural state.intervalMs
  | .handle => .boolean state.hasHandle
  | .isopen => .boolean state.event.isopen
  | .set => .boolean state.event.set

/-- `propertynames(::Timer)`, `base/asyncevent.jl:162`. -/
def m162 : List String :=
  ["handle", "cond", "isopen", "set", "timeout", "timeout_ms", "interval", "interval_ms"]

/-- `show(io, t::Timer)`, `base/asyncevent.jl:164-169`. -/
def m164 (state : AsyncM) : String :=
  let openness := if state.event.isopen then "open" else "closed"
  let interval := if state.intervalMs > 0 then ", interval: " ++ toString state.intervalMs ++ " ms" else ""
  "Timer (" ++ openness ++ ", timeout: " ++ toString (timerTimeout ⟨state.timeoutMs, state.intervalMs⟩) ++ " ms" ++ interval ++ ")"

/-- Timer pointer conversion, `base/asyncevent.jl:171`. -/
def m171 (state : AsyncM) : Bool := state.hasHandle

/-- AsyncCondition pointer conversion, `base/asyncevent.jl:172`. -/
def m172 (state : AsyncM) : Bool := state.hasHandle

/-- Keyword `_trywait`, `base/asyncevent.jl:177-178`. -/
def m177 (state : AsyncM) : Except StreamErr EventM := waitEvent state.event

/-- Token `_trywait`, `base/asyncevent.jl:179-233`. -/
def m179 (state : AsyncM) : Except StreamErr EventM := waitEvent state.event

/-- `waitqueue(t)`, `base/asyncevent.jl:235`. -/
def m235 (queueLength : Nat) : Nat := queueLength

/-- Keyword `wait`, `base/asyncevent.jl:237-238`. -/
def m237 (state : AsyncM) : Except StreamErr Unit :=
  match m177 state with | .ok _ => .ok () | .error e => .error e

/-- Token `wait`, `base/asyncevent.jl:239-244`. -/
def m239 (state : AsyncM) (cancelled : Bool) : Except StreamErr Unit :=
  match m179 state with
  | .error e => .error e
  | .ok _ => if cancelled then .error .ioError else .ok ()

/-- `isopen`, `base/asyncevent.jl:247`. -/
def m247 (state : AsyncM) : Bool := state.event.isopen

/-- `close`, `base/asyncevent.jl:257-292`. -/
def m257 (state : AsyncM) : AsyncM :=
  if !state.hasHandle && !state.event.isopen then state
  else { state with event := closeEvent state.event, hasHandle := false }

/-- `uvfinalize`, `base/asyncevent.jl:294-312`. -/
def m294 (state : AsyncM) : AsyncM :=
  if state.hasHandle then { state with event := closeEvent state.event, hasHandle := false } else state

/-- `_uv_hook_close`, `base/asyncevent.jl:314-326`. -/
def m314 (state : AsyncM) : AsyncM :=
  { state with event := closeEvent state.event, hasHandle := false }

/-- `uv_asynccb`, `base/asyncevent.jl:328-338`. -/
def m328 (state : AsyncM) : AsyncM :=
  { state with event := { state.event with set := true } }

/-- `uv_timercb`, `base/asyncevent.jl:340-359`. -/
def m340 (state : AsyncM) : AsyncM :=
  let signaled := signalEvent state.event
  { state with event := signaled, hasHandle := state.hasHandle && signaled.isopen }

/-- `sleep(sec)`, `base/asyncevent.jl:371-381`. -/
def m371 (secondsNonnegative waitSucceeded : Bool) : Except StreamErr Bool :=
  if !secondsNonnegative then .error .argumentError
  else if !waitSucceeded then .error .ioError
  else .ok false

/-- Callback `Timer`, `base/asyncevent.jl:421-454`. -/
def m421 (state : AsyncM) (spawn : Option Bool) : AsyncM × Bool × Bool :=
  let sticky := match spawn with | none => true | some value => !value
  (state, sticky, state.event.set)

/-- `timedwait`, `base/asyncevent.jl:478-496`. -/
def m478 (pollIntervalValid : Bool) (tests : List Bool) (polls : Nat) : Except StreamErr TimedWaitResult :=
  if !pollIntervalValid then .error .argumentError
  else if timedwaitResult tests polls then .ok .ok else .ok .timedOut

/-- `TimeoutWait(timeout)`, `base/asyncevent.jl:512`. -/
def m512 (timeoutMs : Nat) : TimeoutWaitM := ⟨timeoutMs, false⟩

/-- `wait_enqueue!`, `base/asyncevent.jl:515-537`. -/
def m515 (state : TimeoutWaitM) : TimeoutWaitM × Bool := (timeoutEnqueue state, true)

/-- `wait_dequeue!`, `base/asyncevent.jl:539-544`. -/
def m539 (state : TimeoutWaitM) : TimeoutWaitM := timeoutDequeue state


end JuliaLean.Streams.Methods.AsyncEvent
