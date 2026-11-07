import JuliaLean.Proofs.base.locks_mt.common
import JuliaLean.base.task
import JuliaLean.base.condition
import JuliaLean.base.locks_mt

/-!
# Typed model of `base/lock.jl`

Lock ownership, recursive counts, atomic state bits, condition waiters, and
cancellation are stored in the caller's world. Atomic operations expose both
success and failure orders. A blocked spin or park retains nontermination;
cleanup observes mutations made before an exception.
-/
namespace JuliaLean.base.lock
open JuliaLean
open JuliaLean.base.locks_mt (M MemoryOrder loop finallyDo liftFrame runFrame getFrame setFrame)
open JuliaLean.base.condition (CancelArg GenericCondition WakeValue Waitable)
abbrev I := JInt .i64
def int (n : Int) : I := JInt.wrap .i64 n

structure Runtime (E W RL Task Queue Lock Entry Slot Source Token LockState Value : Type) where
  task : JuliaLean.base.task.Runtime E W Task Queue Lock Entry Slot Source Token LockState Value
  allocate : Option Task → UInt32 → UInt8 → GenericCondition Queue Lock → M E W RL
  loadOwner : MemoryOrder → RL → M E W (Option Task)
  storeOwner : MemoryOrder → RL → Option Task → M E W Unit
  loadCount : RL → M E W UInt32
  storeCount : RL → UInt32 → M E W Unit
  swapCount : MemoryOrder → RL → UInt32 → M E W UInt32
  loadState : MemoryOrder → RL → M E W UInt8
  storeState : MemoryOrder → RL → UInt8 → M E W Unit
  replaceState : MemoryOrder → MemoryOrder → RL → UInt8 → UInt8 → M E W (UInt8 × Bool)
  conditionOf : RL → M E W (GenericCondition Queue Lock)
  disableFinalizers : M E W Unit
  enableFinalizers : M E W Unit
  lockProfiling : M E W Bool
  incLockConflictCount : M E W Unit

structure Lockable (V L : Type) where
  value : V
  lock : L

structure ConditionOps (E W Queue Lock Token Value : Type) where
  newCondition : M E W (GenericCondition Queue Lock)
  precheckCancel : CancelArg Token → M E W (CancelArg Token)
  resolveCancel : CancelArg Token → M E W (Option Token)
  lock : GenericCondition Queue Lock → CancelArg Token → M E W Unit
  unlock : GenericCondition Queue Lock → M E W Unit
  wait : GenericCondition Queue Lock → Option Token → M E W (WakeValue Value)
  notify : GenericCondition Queue Lock → Bool → M E W I

structure SemaphoreOps (E W S Queue Lock Token Value : Type) where
  condition : ConditionOps E W Queue Lock Token Value
  allocate : I → I → GenericCondition Queue Lock → M E W S
  conditionOf : S → M E W (GenericCondition Queue Lock)
  size : S → M E W I
  count : S → M E W I
  setCount : S → I → M E W Unit
  argumentError : String → E
  error : String → E

structure EventOps (E W Event Queue Lock Token Value : Type) where
  condition : ConditionOps E W Queue Lock Token Value
  allocate : GenericCondition Queue Lock → Bool → Bool → M E W Event
  conditionOf : Event → M E W (GenericCondition Queue Lock)
  autoReset : Event → Bool
  loadSet : MemoryOrder → Event → M E W Bool
  swapSet : MemoryOrder → Event → Bool → M E W Bool
  storeSet : MemoryOrder → Event → Bool → M E W Unit

structure ProcessOnceOps (E W Once F V RL : Type) where
  allocate : Option V → UInt8 → Bool → F → RL → M E W Once
  lockOf : Once → M E W RL
  loadState : MemoryOrder → Once → M E W UInt8
  storeState : MemoryOrder → Once → UInt8 → M E W Unit
  allowCompileTime : Once → M E W Bool
  precompile : Bool → M E W Unit
  replaceValueOnPrecompile : Once → Option V → M E W Unit
  replaceStateOnPrecompile : Once → UInt8 → M E W Unit
  initializer : Once → F
  call : F → M E W V
  setValue : Once → V → M E W Unit
  valueAsTarget : Once → M E W V
  error : String → E

structure AtomicMemoryOps (E W Memory V : Type) where
  newEmpty : M E W Memory
  allocate : I → M E W Memory
  length : Memory → M E W I
  nextIndex : Memory → Option I → M E W (Option (I × I))
  isAssigned : Memory → I → M E W Bool
  load : MemoryOrder → Memory → I → M E W V
  store : MemoryOrder → Memory → I → V → M E W Unit

structure ThreadOnceOps (E W Once F V Values States : Type) where
  values : AtomicMemoryOps E W Values V
  states : AtomicMemoryOps E W States UInt8
  allocate : Values → States → F → M E W Once
  loadValues : MemoryOrder → Once → M E W Values
  loadStates : MemoryOrder → Once → M E W States
  storeValues : MemoryOrder → Once → Values → M E W Unit
  storeStates : MemoryOrder → Once → States → M E W Unit
  replaceValuesOnPrecompile : Once → Values → M E W Unit
  replaceStatesOnPrecompile : Once → States → M E W Unit
  initializer : Once → F
  call : F → M E W V
  maxThreadId : M E W I
  lock : M E W Unit
  unlock : M E W Unit
  gcSafepoint : M E W Unit
  argumentError : String → E
  assertionError : String → E
  error : String → E

/-- Julia type objects remain typed metadata passed to constructor specializations. -/
structure OnceTypeOps (E W Ty F Once : Type) where
  promoteOp : F → M E W Ty
  typeofInitializer : F → Ty
  typeOfType : Ty → Ty
  construct : Ty → Ty → F → M E W Once
  allocate : Ty → Ty → F → M E W Once

inductive LockPrintPart (Task : Type) where
  | reentrantLockType | text (value : String) | task (value : Task)

structure LockDisplayOps (E W IO Task V : Type) where
  print : IO → List (LockPrintPart Task) → M E W Unit
  getCompact : IO → Bool → M E W V
  assertBool : V → M E W Bool

section
variable {E W RL Task Queue Lock Entry Slot Source Token LockState Value : Type}
variable (r : Runtime E W RL Task Queue Lock Entry Slot Source Token LockState Value)

-- Source: base/lock.jl:1-9 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- const ThreadSynchronizer = GenericCondition{Threads.SpinLock}
-- 
-- """
--     current_task()
-- 
-- Get the currently running [`Task`](@ref).
-- """
-- /Source

-- Source: base/lock.jl:11-84 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # This bit is set in the `havelock` of a `ReentrantLock` when that lock is locked by some task.
-- const LOCKED_BIT = 0b01
-- # This bit is set in the `havelock` of a `ReentrantLock` just before parking a task. A task is being
-- # parked if it wants to lock the lock, but it is currently being held by some other task.
-- const PARKED_BIT = 0b10
-- 
-- const MAX_SPIN_ITERS = 40
-- 
-- # Advisory reentrant lock
-- """
--     ReentrantLock()
-- 
-- Create a re-entrant lock for synchronizing [`Task`](@ref)s. The same task can
-- acquire the lock as many times as required (this is what the "Reentrant" part
-- of the name means). Each [`lock`](@ref) must be matched with an [`unlock`](@ref).
-- 
-- Calling `lock` will also inhibit running of finalizers on that thread until the
-- corresponding `unlock`. Use of the standard lock pattern illustrated below
-- should naturally be supported, but beware of inverting the try/lock order or
-- missing the try block entirely (e.g. attempting to return with the lock still
-- held):
-- 
-- This provides an acquire/release memory ordering on lock/unlock calls.
-- 
-- ```
-- lock(l)
-- try
--     <atomic work>
-- finally
--     unlock(l)
-- end
-- ```
-- 
-- If [`!islocked(lck::ReentrantLock)`](@ref islocked) holds, [`trylock(lck)`](@ref trylock)
-- succeeds unless there are other tasks attempting to hold the lock "at the same time."
-- """
-- mutable struct ReentrantLock <: AbstractLock
--     # offset = 16
--     @atomic locked_by::Union{Task, Nothing}
--     # offset32 = 20, offset64 = 24
--     reentrancy_cnt::UInt32
--     # offset32 = 24, offset64 = 28
--     #
--     # This atomic integer holds the current state of the lock instance. Only the two lowest bits
--     # are used. See `LOCKED_BIT` and `PARKED_BIT` for the bitmask for these bits.
--     #
--     # # State table:
--     #
--     # PARKED_BIT | LOCKED_BIT | Description
--     #     0      |     0      | The lock is not locked, nor is anyone waiting for it.
--     # -----------+------------+------------------------------------------------------------------
--     #     0      |     1      | The lock is locked by exactly one task. No other task is
--     #            |            | waiting for it.
--     # -----------+------------+------------------------------------------------------------------
--     #     1      |     0      | The lock is not locked. One or more tasks are parked.
--     # -----------+------------+------------------------------------------------------------------
--     #     1      |     1      | The lock is locked by exactly one task. One or more tasks are
--     #            |            | parked waiting for the lock to become available.
--     #            |            | In this state, PARKED_BIT is only ever cleared when the cond_wait lock
--     #            |            | is held (i.e. on unlock). This ensures that
--     #            |            | we never end up in a situation where there are parked tasks but
--     #            |            | PARKED_BIT is not set (which would result in those tasks
--     #            |            | potentially never getting woken up).
--     @atomic havelock::UInt8
--     # offset32 = 28, offset64 = 32
--     cond_wait::ThreadSynchronizer # 1 word (mutable, held by reference)
--     # offset32 = 32, offset64 = 40
--     # sizeof32 = 16, sizeof64 = 24
--     # now add padding to make this a full cache line to minimize false sharing between objects
--     _::NTuple{Int === Int32 ? 3 : 4, Int}
--     # offset32 = 44, offset64 = 72 == sizeof+offset
--     # sizeof32 = 28, sizeof64 = 56
-- 
-- /Source

-- Source: base/lock.jl:86-87 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- end
-- 
-- /Source

-- Source: base/lock.jl:89-89 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/lock.jl:91-91 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/lock.jl:103-142 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     islocked(lock) -> Status (Boolean)
-- 
-- Check whether the `lock` is held by any task/thread.
-- This function alone should not be used for synchronization. However, `islocked` combined
-- with [`trylock`](@ref) can be used for writing the test-and-test-and-set or exponential
-- backoff algorithms *if it is supported by the `typeof(lock)`* (read its documentation).
-- 
-- # Extended help
-- 
-- For example, an exponential backoff can be implemented as follows if the `lock`
-- implementation satisfied the properties documented below.
-- 
-- ```julia
-- nspins = 0
-- while true
--     while islocked(lock)
--         GC.safepoint()
--         nspins += 1
--         nspins > LIMIT && error("timeout")
--     end
--     trylock(lock) && break
--     backoff()
-- end
-- ```
-- 
-- ## Implementation
-- 
-- A lock implementation is advised to define `islocked` with the following properties and note
-- it in its docstring.
-- 
-- * `islocked(lock)` is data-race-free.
-- * If `islocked(lock)` returns `false`, an immediate invocation of `trylock(lock)` must
--   succeed (returns `true`) if there is no interference from other tasks.
-- """
-- function islocked end
-- # Above docstring is a documentation for the abstract interface and not the one specific to
-- # `ReentrantLock`.
-- 
-- /Source

-- Source: base/lock.jl:146-164 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     trylock(lock) -> Success (Boolean)
-- 
-- Acquire the lock if it is available,
-- and return `true` if successful.
-- If the lock is already locked by a different task/thread,
-- return `false`.
-- 
-- Each successful `trylock` must be matched by an [`unlock`](@ref).
-- 
-- Function `trylock` combined with [`islocked`](@ref) can be used for writing the
-- test-and-test-and-set or exponential backoff algorithms *if it is supported by the
-- `typeof(lock)`* (read its documentation).
-- """
-- function trylock end
-- # Above docstring is a documentation for the abstract interface and not the one specific to
-- # `ReentrantLock`.
-- 
-- /Source

-- Source: base/lock.jl:184-193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     lock(lock)
-- 
-- Acquire the `lock` when it becomes available.
-- If the lock is already locked by a different task/thread,
-- wait for it to become available.
-- 
-- Each `lock` must be matched by an [`unlock`](@ref).
-- """
-- /Source

-- Source: base/lock.jl:258-262 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # ReentrantLock-backed conditions (Threads.Condition) forward `cancel` into
-- # the lock acquisition, so operations that resolved a token (or an explicit
-- # `nothing` shield) can make their preliminary lock honor it instead of the
-- # ambient scope - see e.g. the Channel operations.
-- /Source

-- Source: base/lock.jl:265-265 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/lock.jl:297-298 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- 
-- /Source

-- Source: base/lock.jl:300-300 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/lock.jl:306-314 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     unlock(lock)
-- 
-- Releases ownership of the `lock`.
-- 
-- If this is a recursive lock which has been acquired before, decrement an
-- internal counter and return immediately.
-- """
-- /Source

-- Source: base/lock.jl:349-349 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/lock.jl:355-355 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/lock.jl:366-381 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     lock(f::Function, lock)
-- 
-- Acquire the `lock`, execute `f` with the `lock` held, and release the `lock` when `f`
-- returns. If the lock is already locked by a different task/thread, wait for it to become
-- available.
-- 
-- When this function returns, the `lock` has been released, so the caller should
-- not attempt to `unlock` it.
-- 
-- !!! compat "Julia 1.7"
--     Using a [`Channel`](@ref) as the second argument requires Julia 1.7 or later.
-- 
-- See also [`@lock`](@ref).
-- """
-- /Source

-- Source: base/lock.jl:390-391 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # `@inline` keeps an uncontended `lock(f, l)` free of the call into its keyword body.
-- /Source

-- Source: base/lock.jl:400-400 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/lock.jl:411-430 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     @lock l expr
-- 
-- Macro version of `lock(f, l::AbstractLock)` but with `expr` instead of `f` function.
-- Expands to:
-- ```julia
-- lock(l)
-- try
--     expr
-- finally
--     unlock(l)
-- end
-- ```
-- This is similar to using [`lock`](@ref) with a `do` block, but avoids creating a closure
-- and thus can improve the performance.
-- 
-- !!! compat
--     `@lock` was added in Julia 1.3, and exported in Julia 1.7.
-- """
-- /Source

-- Source: base/lock.jl:442-449 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     @lock_nofail l expr
-- 
-- Equivalent to `@lock l expr` for cases in which we can guarantee that the function
-- will not throw any error. In this case, avoiding try-catch can improve the performance.
-- See [`@lock`](@ref).
-- """
-- /Source

-- Source: base/lock.jl:459-489 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Lockable(value, lock = ReentrantLock())
-- 
-- Create a `Lockable` object that wraps `value` and
-- associates it with the provided `lock`. This object
-- supports [`@lock`](@ref), [`lock`](@ref), [`trylock`](@ref),
-- [`unlock`](@ref). To access the value, index the lockable object while
-- holding the lock.
-- 
-- !!! compat "Julia 1.11"
--     Requires at least Julia 1.11.
-- 
-- # Examples
-- 
-- ```jldoctest
-- julia> locked_list = Base.Lockable(Int[]);
-- 
-- julia> @lock(locked_list, push!(locked_list[], 1)) # must hold the lock to access the value
-- 1-element Vector{Int64}:
--  1
-- 
-- julia> lock(summary, locked_list)
-- "1-element Vector{Int64}"
-- ```
-- """
-- struct Lockable{T, L <: AbstractLock}
--     value::T
--     lock::L
-- end
-- 
-- /Source

-- Source: base/lock.jl:492-505 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     lock(f::Function, l::Lockable)
-- 
-- Acquire the lock associated with `l`, execute `f` with the lock held,
-- and release the lock when `f` returns. `f` will receive one positional
-- argument: the value wrapped by `l`. If the lock is already locked by a
-- different task/thread, wait for it to become available.
-- When this function returns, the `lock` has been released, so the caller should
-- not attempt to `unlock` it.
-- 
-- !!! compat "Julia 1.11"
--     Requires at least Julia 1.11.
-- """
-- /Source

-- Source: base/lock.jl:511-512 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # implement the rest of the Lock interface on Lockable
-- /Source

-- Source: base/lock.jl:516-568 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- @eval Threads begin
--     """
--         Threads.Condition([lock])
-- 
--     A thread-safe version of [`Base.Condition`](@ref).
-- 
--     To call [`wait`](@ref) or [`notify`](@ref) on a `Threads.Condition`, you must first call
--     [`lock`](@ref) on it. When `wait` is called, the lock is atomically released during
--     blocking, and will be reacquired before `wait` returns. Therefore idiomatic use
--     of a `Threads.Condition` `c` looks like the following:
-- 
--     ```
--     lock(c)
--     try
--         while !thing_we_are_waiting_for
--             wait(c)
--         end
--     finally
--         unlock(c)
--     end
--     ```
-- 
--     !!! compat "Julia 1.2"
--         This functionality requires at least Julia 1.2.
--     """
--     const Condition = Base.GenericCondition{Base.ReentrantLock}
-- 
--     """
--     Special note for [`Threads.Condition`](@ref):
-- 
--     The caller must be holding the [`lock`](@ref) that owns a `Threads.Condition` before calling this method.
--     The calling task will be blocked until some other task wakes it,
--     usually by calling [`notify`](@ref) on the same `Threads.Condition` object.
--     The lock will be atomically released when blocking (even if it was locked recursively),
--     and will be reacquired before returning.
--     """
--     wait(c::Condition)
-- end
-- 
-- """
--     Semaphore(sem_size)
-- 
-- Create a counting semaphore that allows at most `sem_size`
-- acquires to be in use at any time.
-- Each acquire must be matched with a release.
-- 
-- This provides an acquire & release memory ordering on acquire/release calls.
-- """
-- mutable struct Semaphore
--     sem_size::Int
--     curr_cnt::Int
--     cond_wait::Threads.Condition
-- /Source

-- Source: base/lock.jl:570-577 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- end
-- 
-- """
--     acquire(s::Semaphore)
-- 
-- Wait for one of the `sem_size` permits to be available,
-- blocking until one can be acquired.
-- """
-- /Source

-- Source: base/lock.jl:598-622 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     acquire(f, s::Semaphore)
-- 
-- Execute `f` after acquiring from Semaphore `s`,
-- and `release` on completion or error.
-- 
-- For example, a do-block form that ensures only 2
-- calls of `foo` will be active at the same time:
-- 
-- ```julia
-- s = Base.Semaphore(2)
-- @sync for _ in 1:100
--     Threads.@spawn begin
--         Base.acquire(s) do
--             foo()
--         end
--     end
-- end
-- ```
-- 
-- !!! compat "Julia 1.8"
--     This method requires at least Julia 1.8.
-- 
-- """
-- /Source

-- Source: base/lock.jl:631-649 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Base.@acquire s::Semaphore expr
-- 
-- Macro version of `Base.acquire(f, s::Semaphore)` but with `expr` instead of `f` function.
-- Expands to:
-- ```julia
-- Base.acquire(s)
-- try
--     expr
-- finally
--     Base.release(s)
-- end
-- ```
-- This is similar to using [`acquire`](@ref) with a `do` block, but avoids creating a closure.
-- 
-- !!! compat "Julia 1.13"
--     `Base.@acquire` was added in Julia 1.13
-- """
-- /Source

-- Source: base/lock.jl:661-668 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     release(s::Semaphore)
-- 
-- Return one permit to the pool,
-- possibly allowing another task to acquire it
-- and resume execution.
-- """
-- /Source

-- Source: base/lock.jl:680-704 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- 
-- """
--     Event([autoreset=false])
-- 
-- Create a level-triggered event source. Tasks that call [`wait`](@ref) on an
-- `Event` are suspended and queued until [`notify`](@ref) is called on the `Event`.
-- After `notify` is called, the `Event` remains in a signaled state and
-- tasks will no longer block when waiting for it, until `reset` is called.
-- 
-- If `autoreset` is true, at most one task will be released from `wait` for
-- each call to `notify`.
-- 
-- This provides an acquire & release memory ordering on notify/wait.
-- 
-- !!! compat "Julia 1.1"
--     This functionality requires at least Julia 1.1.
-- 
-- !!! compat "Julia 1.8"
--     The `autoreset` functionality and memory ordering guarantee requires at least Julia 1.8.
-- """
-- mutable struct Event
--     const notify::Threads.Condition
--     const autoreset::Bool
--     @atomic set::Bool
-- /Source

-- Source: base/lock.jl:706-707 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- end
-- 
-- /Source

-- Source: base/lock.jl:731-731 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/lock.jl:748-754 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     reset(::Event)
-- 
-- Reset an [`Event`](@ref) back into an un-set state. Then any future calls to `wait` will
-- block until [`notify`](@ref) is called again.
-- """
-- /Source

-- Source: base/lock.jl:759-807 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- @eval Threads begin
--     import .Base: Event
--     export Event
-- end
-- 
-- const PerStateInitial       = 0x00
-- const PerStateHasrun        = 0x01
-- const PerStateErrored       = 0x02
-- const PerStateConcurrent    = 0x03
-- 
-- """
--     OncePerProcess{T}(init::Function)() -> T
-- 
-- Calling a `OncePerProcess` object returns a value of type `T` by running the
-- function `initializer` exactly once per process. All concurrent and future
-- calls in the same process will return exactly the same value. This is useful in
-- code that will be precompiled, as it allows setting up caches or other state
-- which won't get serialized.
-- 
-- !!! compat "Julia 1.12"
--     This type requires Julia 1.12 or later.
-- 
-- # Examples
-- 
-- ```jldoctest
-- julia> const global_state = Base.OncePerProcess{Vector{UInt32}}() do
--            println("Making lazy global value...done.")
--            return [Libc.rand()]
--        end;
-- 
-- julia> (procstate = global_state()) |> typeof
-- Making lazy global value...done.
-- Vector{UInt32} (alias for Array{UInt32, 1})
-- 
-- julia> procstate === global_state()
-- true
-- 
-- julia> procstate === fetch(@async global_state())
-- true
-- ```
-- """
-- mutable struct OncePerProcess{T, F} <: Function
--     value::Union{Nothing,T}
--     @atomic state::UInt8 # 0=initial, 1=hasrun, 2=error
--     @atomic allow_compile_time::Bool
--     const initializer::F
--     const lock::ReentrantLock
-- 
-- /Source

-- Source: base/lock.jl:812-812 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- end
-- /Source

-- Source: base/lock.jl:849-849 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/lock.jl:862-862 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/lock.jl:869-918 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- 
-- # share a lock/condition, since we just need it briefly, so some contention is okay
-- const PerThreadLock = Threads.SpinLock()
-- """
--     OncePerThread{T}(init::Function)() -> T
-- 
-- Calling a `OncePerThread` object returns a value of type `T` by running the function
-- `initializer` exactly once per thread. All future calls in the same thread, and
-- concurrent or future calls with the same thread id, will return exactly the
-- same value. The object can also be indexed by the threadid for any existing
-- thread, to get (or initialize *on this thread*) the value stored for that
-- thread. Incorrect usage can lead to data-races or memory corruption so use only
-- if that behavior is correct within your library's threading-safety design.
-- 
-- !!! warning
--     It is not necessarily true that a Task only runs on one thread, therefore the value
--     returned here may alias other values or change in the middle of your program. This function
--     may get deprecated in the future. If initializer yields, the thread running the current
--     task after the call might not be the same as the one at the start of the call.
-- 
-- !!! compat "Julia 1.12"
--     This type requires Julia 1.12 or later.
-- 
-- See also [`OncePerTask`](@ref).
-- 
-- # Examples
-- 
-- ```jldoctest
-- julia> const thread_state = Base.OncePerThread{Vector{UInt32}}() do
--            println("Making lazy thread value...done.")
--            return [Libc.rand()]
--        end;
-- 
-- julia> (threadvec = thread_state()) |> typeof
-- Making lazy thread value...done.
-- Vector{UInt32} (alias for Array{UInt32, 1})
-- 
-- julia> threadvec === fetch(@async thread_state())
-- true
-- 
-- julia> threadvec === thread_state[Threads.threadid()]
-- true
-- ```
-- """
-- mutable struct OncePerThread{T, F} <: Function
--     @atomic xs::AtomicMemory{T} # values
--     @atomic ss::AtomicMemory{UInt8} # states: 0=initial, 1=hasrun, 2=error, 3==concurrent
--     const initializer::F
-- 
-- /Source

-- Source: base/lock.jl:924-924 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- end
-- /Source

-- Source: base/lock.jl:1020-1054 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     OncePerTask{T}(init::Function)() -> T
-- 
-- Calling a `OncePerTask` object returns a value of type `T` by running the function `initializer`
-- exactly once per Task. All future calls in the same Task will return exactly the same value.
-- 
-- !!! compat "Julia 1.12"
--     This type requires Julia 1.12 or later.
-- 
-- See also [`task_local_storage`](@ref).
-- 
-- # Examples
-- 
-- ```jldoctest
-- julia> const task_state = Base.OncePerTask{Vector{UInt32}}() do
--            println("Making lazy task value...done.")
--            return [Libc.rand()]
--        end;
-- 
-- julia> (taskvec = task_state()) |> typeof
-- Making lazy task value...done.
-- Vector{UInt32} (alias for Array{UInt32, 1})
-- 
-- julia> taskvec === task_state()
-- true
-- 
-- julia> taskvec === fetch(@async task_state())
-- Making lazy task value...done.
-- false
-- ```
-- """
-- mutable struct OncePerTask{T, F} <: Function
--     const initializer::F
-- 
-- /Source

-- Source: base/lock.jl:1060-1060 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- end
-- /Source

/--
Julia source: base/lock.jl:10-10 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
current_task() = ccall(:jl_get_current_task, Ref{Task}, ())
```
-/
def currentTask : M E W Task := r.task.condition.currentTask

/--
Julia source: base/lock.jl:85-85 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    ReentrantLock() = new(nothing, 0x0000_0000, 0x00, ThreadSynchronizer())
```
-/
def newReentrantLock : M E W RL := do
  r.allocate none 0 0 (← JuliaLean.base.condition.newGenericCondition r.task.condition)

/--
Julia source: base/lock.jl:143-145 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function islocked(rl::ReentrantLock)
    return (@atomic :monotonic rl.havelock) & LOCKED_BIT != 0
end
```
-/
def islocked (lock : RL) : M E W Bool := do
  pure (((← r.loadState .monotonic lock) &&& 1) != 0)

/--
Julia source: base/lock.jl:88-88 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
assert_havelock(l::ReentrantLock) = assert_havelock(l, l.locked_by)
```
-/
def assertHaveLock (lock : RL) : M E W Unit := do
  match ← r.loadOwner .plain lock with
  | none => JuliaLean.base.condition.concurrencyViolation r.task.condition
  | some owner => JuliaLean.base.condition.assertHaveLockTask r.task.condition (islocked r) r.task.sameTask lock owner

/--
Julia source: base/lock.jl:173-183 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function _trylock(rl::ReentrantLock, ct::Task)
    GC.disable_finalizers()
    state = (@atomic :monotonic rl.havelock) & PARKED_BIT
    if (@atomicreplace :acquire rl.havelock state => (state | LOCKED_BIT)).success
        rl.reentrancy_cnt = 0x0000_0001
        @atomic :release rl.locked_by = ct
        return true
    end
    GC.enable_finalizers()
    return false
end
```
-/
def trylockInternal (lock : RL) (current : Task) : M E W Bool := do
  r.disableFinalizers
  let state := (← r.loadState .monotonic lock) &&& 2
  let replaced ← r.replaceState .acquire .acquire lock state (state ||| 1)
  if replaced.2 then
    r.storeCount lock 1
    r.storeOwner .release lock (some current)
    return true
  r.enableFinalizers
  pure false

/--
Julia source: base/lock.jl:165-172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function trylock(rl::ReentrantLock)
    ct = current_task()
    if rl.locked_by === ct
        rl.reentrancy_cnt += 0x0000_0001
        return true
    end
    return _trylock(rl, ct)
end
```
-/
def trylock (lock : RL) : M E W Bool := do
  let current ← currentTask r
  let owner ← r.loadOwner .plain lock
  if owner.any (r.task.sameTask · current) then
    r.storeCount lock ((← r.loadCount lock) + 1)
    return true
  trylockInternal r lock current

/--
Julia source: base/lock.jl:327-341 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
                (@noinline function notifywaiters(rl)
                    cond_wait = rl.cond_wait
                    lock(cond_wait)

                    notify(cond_wait, all=false)
                    if !isempty(cond_wait.waitq)
                        @atomic :release rl.havelock = PARKED_BIT
                    else
                        # We may have won the race to the `cond_wait` lock as a task was about to park
                        # but we unlock anyway as any parking task will retry
                        @atomic :release rl.havelock = 0x00
                    end

                    unlock(cond_wait)
                end)(rl)
```
-/
def notifyWaiters (lock : RL) : M E W Unit := do
  let condition ← r.conditionOf lock
  JuliaLean.base.condition.lockCondition r.task.condition condition
  let _ ← JuliaLean.base.condition.notifyKw r.task.condition condition .nothing false
  if !(← r.task.condition.refEmpty (JuliaLean.base.condition.waitqueue condition)) then
    r.storeState .release lock 2
  else r.storeState .release lock 0
  JuliaLean.base.condition.unlockCondition r.task.condition condition

/--
Julia source: base/lock.jl:318-346 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    (@noinline function _unlock(rl::ReentrantLock)
        n = rl.reentrancy_cnt - 0x0000_0001
        rl.reentrancy_cnt = n
        if n == 0x0000_00000
            @atomic :monotonic rl.locked_by = nothing
            result = (@atomicreplace :release :monotonic rl.havelock LOCKED_BIT => 0x00)
            if result.success
                return true
            else
                (@noinline function notifywaiters(rl)
                    cond_wait = rl.cond_wait
                    lock(cond_wait)

                    notify(cond_wait, all=false)
                    if !isempty(cond_wait.waitq)
                        @atomic :release rl.havelock = PARKED_BIT
                    else
                        # We may have won the race to the `cond_wait` lock as a task was about to park
                        # but we unlock anyway as any parking task will retry
                        @atomic :release rl.havelock = 0x00
                    end

                    unlock(cond_wait)
                end)(rl)
                return true
            end
        end
        return false
    end)(rl) && GC.enable_finalizers()
```
-/
def unlockInternal (lock : RL) : M E W Bool := do
  let count := (← r.loadCount lock) - 1
  r.storeCount lock count
  if count == 0 then
    r.storeOwner .monotonic lock none
    if (← r.replaceState .release .monotonic lock 1 0).2 then return true
    notifyWaiters r lock
    return true
  pure false

/--
Julia source: base/lock.jl:315-348 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function unlock(rl::ReentrantLock)
    rl.locked_by === current_task() ||
        error(rl.reentrancy_cnt == 0x0000_0000 ? "unlock count must match lock count" : "unlock from wrong thread")
    (@noinline function _unlock(rl::ReentrantLock)
        n = rl.reentrancy_cnt - 0x0000_0001
        rl.reentrancy_cnt = n
        if n == 0x0000_00000
            @atomic :monotonic rl.locked_by = nothing
            result = (@atomicreplace :release :monotonic rl.havelock LOCKED_BIT => 0x00)
            if result.success
                return true
            else
                (@noinline function notifywaiters(rl)
                    cond_wait = rl.cond_wait
                    lock(cond_wait)

                    notify(cond_wait, all=false)
                    if !isempty(cond_wait.waitq)
                        @atomic :release rl.havelock = PARKED_BIT
                    else
                        # We may have won the race to the `cond_wait` lock as a task was about to park
                        # but we unlock anyway as any parking task will retry
                        @atomic :release rl.havelock = 0x00
                    end

                    unlock(cond_wait)
                end)(rl)
                return true
            end
        end
        return false
    end)(rl) && GC.enable_finalizers()
    nothing
end
```
-/
def unlock (lock : RL) : M E W Unit := do
  let owner ← r.loadOwner .plain lock
  let current ← currentTask r
  if !(owner.any (r.task.sameTask · current)) then
    let message := if (← r.loadCount lock) == 0 then "unlock count must match lock count" else "unlock from wrong thread"
    throw (r.task.condition.error message)
  if ← unlockInternal r lock then r.enableFinalizers

/--
Julia source: base/lock.jl:350-354 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unlockall(rl::ReentrantLock)
    n = @atomicswap :not_atomic rl.reentrancy_cnt = 0x0000_0001
    unlock(rl)
    return n
end
```
-/
def unlockAll (lock : RL) : M E W UInt32 := do
  let count ← r.swapCount .plain lock 1
  unlock r lock
  pure count

/--
Julia source: base/lock.jl:266-296 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function wait_no_relock(c::GenericCondition, tok::MaybeToken)
    # relock=false: a normal wake returns without retaking the lock (the
    # notifier's handoff popped our entry), the refusal releases before
    # throwing (e.g. a token cancelled while we were still spinning and
    # thus not interruptibly waiting), and the interrupted cleanup retakes
    # the lock only for its unlink
    ct = current_task()
    src = cancel_source(tok)
    if src === nothing
        ws = (c,)
        w = _cached_wait_entry(ct)
    else
        ws = (c, SourceWait(src, 0x00))
        w = _cancel_wait_entry(ct, src, 0x00)
    end
    if !park!(ws, w, false)
        # refused at the registration recheck (e.g. a token cancelled
        # while we were still spinning and thus not interruptibly
        # waiting): withdraw under the held lock, release, deliver
        withdraw!(ws, w, WAKE_FIRED)
        unlock(c.lock)
        checkcancel(src)
        error("park fired without a cancelled source")
    end
    unlockall(c.lock)
    # no relock on any path: a normal wake was handed the lock's baton by
    # the notifying unlock, and an exceptional unwind - possibly the
    # delivered cancellation itself - must not sleep on locks it does not
    # need (the cleanup's unlink takes the lock transiently itself)
    return wait_safe_interrupt(ws, w)
end
```
-/
def waitNoRelock (condition : GenericCondition Queue Lock) (token : Option Token) : M E W (WakeValue Value) := do
  let current ← currentTask r
  let source := r.task.condition.cancelSource token
  let (waitables, entry) ← match source with
    | none => do
      let entry ← r.task.condition.cachedWaitEntry current
      pure ([Waitable.condition condition], entry)
    | some source => do
      let entry ← r.task.condition.cancelWaitEntry current source 0
      pure ([Waitable.condition condition, Waitable.source source 0], entry)
  if !(← r.task.condition.park waitables entry false) then
    r.task.condition.withdraw waitables entry r.task.condition.wakeFired
    r.task.condition.unlock condition.lock
    r.task.condition.checkCancel source
    throw (r.task.condition.error "park fired without a cancelled source")
  let _ ← r.task.condition.unlockAll condition.lock
  r.task.condition.waitSafeInterrupt waitables entry

/--
Julia source: base/lock.jl:196-255 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    trylock(rl) || (@noinline function slowlock(rl::ReentrantLock, cancel::CancelTokenArg)
        Threads.lock_profiling() && Threads.inc_lock_conflict_count()
        # resolve the scoped default once; a cancelled acquisition throws the
        # CancellationRequest without the lock held
        tok = resolve_cancel_token(cancel)
        c = rl.cond_wait
        ct = current_task()
        iteration = 1
        while true
            state = @atomic :monotonic rl.havelock
            # Grab the lock if it isn't locked, even if there is a queue on it
            if state & LOCKED_BIT == 0
                GC.disable_finalizers()
                result = (@atomicreplace :acquire :monotonic rl.havelock state => (state | LOCKED_BIT))
                if result.success
                    rl.reentrancy_cnt = 0x0000_0001
                    @atomic :release rl.locked_by = ct
                    # Mirror the park path's refusal (see wait_no_relock): a
                    # token that got cancelled while we were spinning must
                    # not hand out the lock - release it and deliver.
                    if tok !== nothing && iscancelled(tok.source)
                        unlock(rl)
                        checkcancel(tok.source)
                    end
                    return
                end
                GC.enable_finalizers()
                continue
            end

            if state & PARKED_BIT == 0
                # If there is no queue, try spinning a few times
                if iteration <= MAX_SPIN_ITERS
                    Base.yield()
                    iteration += 1
                    continue
                end

                # If still not locked, try setting the parked bit
                @atomicreplace :monotonic :monotonic rl.havelock state => (state | PARKED_BIT)
            end

            # lock the `cond_wait`
            lock(c.lock)

            # Last check before we wait to make sure `unlock` did not win the race
            # to the `cond_wait` lock and cleared the parked bit
            state = @atomic :acquire rl.havelock
            if state != LOCKED_BIT | PARKED_BIT
                unlock(c.lock)
                continue
            end

            # It was locked, so now wait for the unlock to notify us
            wait_no_relock(c, tok)

            # Loop back and try locking again
            iteration = 1
        end
    end)(rl, cancel)
```
-/
def slowlock (lock : RL) (cancel : CancelArg Token) : M E W Unit := do
  if ← r.lockProfiling then r.incLockConflictCount
  let token ← r.task.resolveCancelToken cancel
  let condition ← r.conditionOf lock
  let current ← currentTask r
  loop (fun (iteration : I) => do
    let state ← r.loadState .monotonic lock
    if state &&& 1 == 0 then
      r.disableFinalizers
      let replaced ← r.replaceState .acquire .monotonic lock state (state ||| 1)
      if replaced.2 then
        r.storeCount lock 1
        r.storeOwner .release lock (some current)
        match r.task.condition.cancelSource token with
        | some source =>
          if ← r.task.condition.sourceCancelled source then
            unlock r lock
            r.task.condition.checkCancel (some source)
        | none => pure ()
        return .inl ()
      r.enableFinalizers
      return .inr iteration
    if state &&& 2 == 0 then
      if iteration.val ≤ 40 then
        let _ ← JuliaLean.base.task.yield r.task
        return .inr (iteration + int 1)
      let _ ← r.replaceState .monotonic .monotonic lock state (state ||| 2)
    r.task.condition.lock condition.lock
    let state ← r.loadState .acquire lock
    if state != (1 ||| 2) then
      r.task.condition.unlock condition.lock
      return .inr iteration
    let _ ← waitNoRelock r condition token
    pure (.inr (int 1))) (int 1)

/--
Julia source: base/lock.jl:194-257 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function lock(rl::ReentrantLock; cancel::CancelTokenArg=DEFAULT_CANCEL)
    cancel = precheck_cancel_arg(cancel)
    trylock(rl) || (@noinline function slowlock(rl::ReentrantLock, cancel::CancelTokenArg)
        Threads.lock_profiling() && Threads.inc_lock_conflict_count()
        # resolve the scoped default once; a cancelled acquisition throws the
        # CancellationRequest without the lock held
        tok = resolve_cancel_token(cancel)
        c = rl.cond_wait
        ct = current_task()
        iteration = 1
        while true
            state = @atomic :monotonic rl.havelock
            # Grab the lock if it isn't locked, even if there is a queue on it
            if state & LOCKED_BIT == 0
                GC.disable_finalizers()
                result = (@atomicreplace :acquire :monotonic rl.havelock state => (state | LOCKED_BIT))
                if result.success
                    rl.reentrancy_cnt = 0x0000_0001
                    @atomic :release rl.locked_by = ct
                    # Mirror the park path's refusal (see wait_no_relock): a
                    # token that got cancelled while we were spinning must
                    # not hand out the lock - release it and deliver.
                    if tok !== nothing && iscancelled(tok.source)
                        unlock(rl)
                        checkcancel(tok.source)
                    end
                    return
                end
                GC.enable_finalizers()
                continue
            end

            if state & PARKED_BIT == 0
                # If there is no queue, try spinning a few times
                if iteration <= MAX_SPIN_ITERS
                    Base.yield()
                    iteration += 1
                    continue
                end

                # If still not locked, try setting the parked bit
                @atomicreplace :monotonic :monotonic rl.havelock state => (state | PARKED_BIT)
            end

            # lock the `cond_wait`
            lock(c.lock)

            # Last check before we wait to make sure `unlock` did not win the race
            # to the `cond_wait` lock and cleared the parked bit
            state = @atomic :acquire rl.havelock
            if state != LOCKED_BIT | PARKED_BIT
                unlock(c.lock)
                continue
            end

            # It was locked, so now wait for the unlock to notify us
            wait_no_relock(c, tok)

            # Loop back and try locking again
            iteration = 1
        end
    end)(rl, cancel)
    return
end
```
-/
def lock (lock : RL) (cancel : CancelArg Token := .default) : M E W Unit := do
  let cancel ← r.task.precheckCancelArg cancel
  if !(← trylock r lock) then slowlock r lock cancel

/--
Julia source: base/lock.jl:263-264 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lock(c::GenericCondition{ReentrantLock}; cancel::CancelTokenArg=DEFAULT_CANCEL) =
    lock(c.lock; cancel)
```
-/
def lockCondition (condition : GenericCondition Queue RL) (cancel : CancelArg Token := .default) : M E W Unit :=
  lock r condition.lock cancel

/--
Julia source: base/lock.jl:299-299 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_uncancellable_lock(l::ReentrantLock) = lock(l; cancel=nothing)
```
-/
def uncancellableLock (l : RL) : M E W Unit := lock r l .shielded

/--
Julia source: base/lock.jl:356-365 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function relockall(rl::ReentrantLock, n::UInt32)
    # The reacquire is the cleanup half of a wait whose outcome (including a
    # cancellation) has already been delivered: it must not itself be
    # cancellable, or a cancelled scope would throw out of here without the
    # lock and the caller's queue cleanup would run unlocked.
    lock(rl; cancel=nothing)
    old = @atomicswap :not_atomic rl.reentrancy_cnt = n
    old == 0x0000_0001 || concurrency_violation()
    return
end
```
-/
def relockAll (l : RL) (count : UInt32) : M E W Unit := do
  lock r l .shielded
  let old ← r.swapCount .plain l count
  if old != 1 then JuliaLean.base.condition.concurrencyViolation r.task.condition

/--
Julia source: base/lock.jl:301-305 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function relockall_but_one(rl::ReentrantLock, state::UInt32)
    state == 0x0000_0001 && return nothing
    relockall(rl, state - 0x0000_0001)
    return nothing
end
```
-/
def relockAllButOne (lock : RL) (count : UInt32) : M E W Unit := do
  if count == 1 then return ()
  relockAll r lock (count - 1)

/--
Julia source: base/lock.jl:382-389 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function lock(f, l::AbstractLock)
    lock(l)
    try
        return f()
    finally
        unlock(l)
    end
end
```
-/
def lockBody {L A LR UR : Type} (lock : L → M E W LR) (unlock : L → M E W UR)
    (body : M E W A) (l : L) : M E W A := do
  let _ ← lock l
  finallyDo body (do let _ ← unlock l; pure ())

/--
Julia source: base/lock.jl:392-399 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function lock(f, l::ReentrantLock; cancel::CancelTokenArg=DEFAULT_CANCEL)
    lock(l; cancel)
    try
        return f()
    finally
        unlock(l)
    end
end
```
-/
def lockReentrantBody {A : Type} (body : M E W A) (l : RL)
    (cancel : CancelArg Token := .default) : M E W A := do
  lock r l cancel
  finallyDo body (unlock r l)

/--
Julia source: base/lock.jl:401-410 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function trylock(f, l::AbstractLock)
    if trylock(l)
        try
            return f()
        finally
            unlock(l)
        end
    end
    return false
end
```
-/
def trylockBody {L A UR : Type} (trylock : L → M E W Bool) (unlock : L → M E W UR)
    (body : M E W A) (l : L) : M E W (Sum A Bool) := do
  if ← trylock l then
    return .inl (← finallyDo body (do let _ ← unlock l; pure ()))
  pure (.inr false)

/--
Julia source: base/lock.jl:490-490 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Lockable(value) = Lockable(value, ReentrantLock())
```
-/
def newLockable {V : Type} (value : V) : M E W (Lockable V RL) := do
  pure ⟨value, ← newReentrantLock r⟩

/--
Julia source: base/lock.jl:491-491 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(l::Lockable) = (assert_havelock(l.lock); l.value)
```
-/
def lockableGetindex {V L A : Type} (assertHaveLock : L → M E W A) (l : Lockable V L) : M E W V := do
  let _ ← assertHaveLock l.lock
  pure l.value

/--
Julia source: base/lock.jl:506-510 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function lock(f, l::Lockable)
    lock(l.lock) do
        f(l.value)
    end
end
```
-/
def lockableBody {V L A LR UR : Type} (lock : L → M E W LR) (unlock : L → M E W UR)
    (body : V → M E W A) (l : Lockable V L) : M E W A :=
  lockBody lock unlock (body l.value) l.lock

/--
Julia source: base/lock.jl:513-513 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lock(l::Lockable) = lock(l.lock)
```
-/
def lockableLock {V L A : Type} (lock : L → M E W A) (l : Lockable V L) : M E W A := lock l.lock

/--
Julia source: base/lock.jl:514-514 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
trylock(l::Lockable) = trylock(l.lock)
```
-/
def lockableTrylock {V L A : Type} (trylock : L → M E W A) (l : Lockable V L) : M E W A := trylock l.lock

/--
Julia source: base/lock.jl:515-515 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unlock(l::Lockable) = unlock(l.lock)
```
-/
def lockableUnlock {V L A : Type} (unlock : L → M E W A) (l : Lockable V L) : M E W A := unlock l.lock

/--
Julia source: base/lock.jl:569-569 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Semaphore(sem_size) = sem_size > 0 ? new(sem_size, 0, Threads.Condition()) : throw(ArgumentError("Semaphore size must be > 0"))
```
-/
def newSemaphore {S Q L Tok V : Type} (p : SemaphoreOps E W S Q L Tok V) (size : I) : M E W S := do
  if size.val > 0 then p.allocate size (int 0) (← p.condition.newCondition)
  else throw (p.argumentError "Semaphore size must be > 0")

/--
Julia source: base/lock.jl:578-597 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function acquire(s::Semaphore; cancel::CancelTokenArg=DEFAULT_CANCEL)
    cancel = precheck_cancel_arg(cancel)
    lock(s.cond_wait; cancel)
    locked = true
    try
        if s.curr_cnt >= s.sem_size
            tok = resolve_cancel_token(cancel)
            while s.curr_cnt >= s.sem_size
                # a cancelled wait throws before the permit is taken
                locked = false
                wait(s.cond_wait, tok)
                locked = true
            end
        end
        s.curr_cnt = s.curr_cnt + 1
    finally
        locked && unlock(s.cond_wait)
    end
    return
end
```
-/
def acquireSemaphore {S Q L Tok V : Type} (p : SemaphoreOps E W S Q L Tok V)
    (semaphore : S) (cancel : CancelArg Tok := .default) : M E W Unit := do
  let cancel ← p.condition.precheckCancel cancel
  let condition ← p.conditionOf semaphore
  p.condition.lock condition cancel
  runFrame true (finallyDo (do
    if (← liftFrame (p.count semaphore)).val ≥ (← liftFrame (p.size semaphore)).val then
      let token ← liftFrame (p.condition.resolveCancel cancel)
      loop (fun (_ : Unit) => do
        if (← liftFrame (p.count semaphore)).val < (← liftFrame (p.size semaphore)).val then return .inl ()
        setFrame false
        let _ ← liftFrame (p.condition.wait condition token)
        setFrame true
        pure (.inr ())) ()
    let count ← liftFrame (p.count semaphore)
    liftFrame (p.setCount semaphore (count + int 1)))
    (do if ← getFrame then liftFrame (p.condition.unlock condition)))

/--
Julia source: base/lock.jl:669-679 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function release(s::Semaphore)
    lock(s.cond_wait)
    try
        s.curr_cnt > 0 || error("release count must match acquire count")
        s.curr_cnt -= 1
        notify(s.cond_wait; all=false)
    finally
        unlock(s.cond_wait)
    end
    return
end
```
-/
def releaseSemaphore {S Q L Tok V : Type} (p : SemaphoreOps E W S Q L Tok V) (semaphore : S) : M E W Unit := do
  let condition ← p.conditionOf semaphore
  p.condition.lock condition .default
  finallyDo (do
    if (← p.count semaphore).val ≤ 0 then throw (p.error "release count must match acquire count")
    p.setCount semaphore ((← p.count semaphore) - int 1)
    let _ ← p.condition.notify condition false
    pure ()) (p.condition.unlock condition)

/--
Julia source: base/lock.jl:623-630 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function acquire(f, s::Semaphore; cancel::CancelTokenArg=DEFAULT_CANCEL)
    acquire(s; cancel)
    try
        return f()
    finally
        release(s)
    end
end
```
-/
def acquireSemaphoreBody {S Q L Tok V A : Type} (p : SemaphoreOps E W S Q L Tok V)
    (body : M E W A) (semaphore : S) (cancel : CancelArg Tok := .default) : M E W A := do
  acquireSemaphore p semaphore cancel
  finallyDo body (releaseSemaphore p semaphore)

/--
Julia source: base/lock.jl:705-705 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Event(autoreset::Bool=false) = new(Threads.Condition(), autoreset, false)
```
-/
def newEvent {Event Q L Tok V : Type} (p : EventOps E W Event Q L Tok V)
    (autoreset : Bool := false) : M E W Event := do
  p.allocate (← p.condition.newCondition) autoreset false

/--
Julia source: base/lock.jl:708-730 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function wait(e::Event; cancel::CancelTokenArg=DEFAULT_CANCEL)
    cancel = precheck_cancel_arg(cancel)
    if e.autoreset
        (@atomicswap :acquire_release e.set = false) && return
    else
        (@atomic e.set) && return # full barrier also
    end
    lock(e.notify; cancel) # acquire barrier
    locked = true
    try
        if e.autoreset
            (@atomicswap :acquire_release e.set = false) && return
        else
            e.set && return
        end
        locked = false
        wait(e.notify, resolve_cancel_token(cancel))
        locked = true
    finally
        locked && unlock(e.notify) # release barrier
    end
    nothing
end
```
-/
def waitEvent {Event Q L Tok V : Type} (p : EventOps E W Event Q L Tok V)
    (event : Event) (cancel : CancelArg Tok := .default) : M E W Unit := do
  let cancel ← p.condition.precheckCancel cancel
  if p.autoReset event then
    if ← p.swapSet .acquireRelease event false then return ()
  else if ← p.loadSet .sequentiallyConsistent event then return ()
  let condition ← p.conditionOf event
  p.condition.lock condition cancel
  runFrame true (finallyDo (do
    if p.autoReset event then
      if ← liftFrame (p.swapSet .acquireRelease event false) then return ()
    else if ← liftFrame (p.loadSet .plain event) then return ()
    setFrame false
    let _ ← liftFrame (p.condition.wait condition (← liftFrame (p.condition.resolveCancel cancel)))
    setFrame true)
    (do if ← getFrame then liftFrame (p.condition.unlock condition)))

/--
Julia source: base/lock.jl:732-747 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function notify(e::Event)
    lock(e.notify) # acquire barrier
    try
        if e.autoreset
            if notify(e.notify, all=false) == 0
                @atomic :release e.set = true
            end
        elseif !e.set
            @atomic :release e.set = true
            notify(e.notify)
        end
    finally
        unlock(e.notify)
    end
    nothing
end
```
-/
def notifyEvent {Event Q L Tok V : Type} (p : EventOps E W Event Q L Tok V) (event : Event) : M E W Unit := do
  let condition ← p.conditionOf event
  p.condition.lock condition .default
  finallyDo (do
    if p.autoReset event then
      if (← p.condition.notify condition false).val == 0 then p.storeSet .release event true
    else if !(← p.loadSet .plain event) then
      p.storeSet .release event true
      let _ ← p.condition.notify condition true
      pure ()) (p.condition.unlock condition)

/--
Julia source: base/lock.jl:755-758 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function reset(e::Event)
    @atomic e.set = false # full barrier
    nothing
end
```
-/
def resetEvent {Event Q L Tok V : Type} (p : EventOps E W Event Q L Tok V) (event : Event) : M E W Unit :=
  p.storeSet .sequentiallyConsistent event false

/--
Julia source: base/lock.jl:808-811 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function OncePerProcess{T,F}(initializer::F) where {T, F}
        once = new{T,F}(nothing, PerStateInitial, true, initializer, ReentrantLock())
        return once
    end
```
-/
def newOncePerProcess {Once F V : Type} (p : ProcessOnceOps E W Once F V RL) (initializer : F) : M E W Once := do
  p.allocate none 0 true initializer (← newReentrantLock r)

/--
Julia source: base/lock.jl:820-845 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        (@noinline function init_perprocesss(once::OncePerProcess{T,F}, state::UInt8) where {T,F}
            state == PerStateErrored && error("OncePerProcess initializer failed previously")
            once.allow_compile_time || __precompile__(false)
            lock(once.lock)
            try
                state = @atomic :monotonic once.state
                if state == PerStateInitial
                    ccall(:jl_set_precompile_field_replace, Cvoid, (Any, Any, Any),
                        once, :value, nothing)
                    ccall(:jl_set_precompile_field_replace, Cvoid, (Any, Any, Any),
                        once, :state, PerStateInitial)
                    once.value = once.initializer()
                elseif state == PerStateErrored
                    error("OncePerProcess initializer failed previously")
                elseif state != PerStateHasrun
                    error("invalid state for OncePerProcess")
                end
            catch
                state == PerStateErrored || @atomic :release once.state = PerStateErrored
                unlock(once.lock)
                rethrow()
            end
            state == PerStateHasrun || @atomic :release once.state = PerStateHasrun
            unlock(once.lock)
            nothing
        end)(once, state)
```
-/
def initPerProcess {Once F V : Type} (p : ProcessOnceOps E W Once F V RL)
    (once : Once) (state : UInt8) : M E W Unit := do
  if state == 2 then throw (p.error "OncePerProcess initializer failed previously")
  if !(← p.allowCompileTime once) then p.precompile false
  let l ← p.lockOf once
  lock r l
  runFrame state (do
    tryCatch (do
      let state ← liftFrame (p.loadState .monotonic once)
      setFrame state
      if state == 0 then
        liftFrame (p.replaceValueOnPrecompile once none)
        liftFrame (p.replaceStateOnPrecompile once 0)
        liftFrame (p.setValue once (← liftFrame (p.call (p.initializer once))))
      else if state == 2 then throw (p.error "OncePerProcess initializer failed previously")
      else if state != 1 then throw (p.error "invalid state for OncePerProcess")) (fun error => do
        if (← getFrame) != 2 then liftFrame (p.storeState .release once 2)
        liftFrame (unlock r l)
        throw error)
    if (← getFrame) != 1 then liftFrame (p.storeState .release once 1)
    liftFrame (unlock r l))

/--
Julia source: base/lock.jl:817-848 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function (once::OncePerProcess{T,F})() where {T,F}
    state = (@atomic :acquire once.state)
    if state != PerStateHasrun
        (@noinline function init_perprocesss(once::OncePerProcess{T,F}, state::UInt8) where {T,F}
            state == PerStateErrored && error("OncePerProcess initializer failed previously")
            once.allow_compile_time || __precompile__(false)
            lock(once.lock)
            try
                state = @atomic :monotonic once.state
                if state == PerStateInitial
                    ccall(:jl_set_precompile_field_replace, Cvoid, (Any, Any, Any),
                        once, :value, nothing)
                    ccall(:jl_set_precompile_field_replace, Cvoid, (Any, Any, Any),
                        once, :state, PerStateInitial)
                    once.value = once.initializer()
                elseif state == PerStateErrored
                    error("OncePerProcess initializer failed previously")
                elseif state != PerStateHasrun
                    error("invalid state for OncePerProcess")
                end
            catch
                state == PerStateErrored || @atomic :release once.state = PerStateErrored
                unlock(once.lock)
                rethrow()
            end
            state == PerStateHasrun || @atomic :release once.state = PerStateHasrun
            unlock(once.lock)
            nothing
        end)(once, state)
    end
    return once.value::T
end
```
-/
def oncePerProcess {Once F V : Type} (p : ProcessOnceOps E W Once F V RL) (once : Once) : M E W V := do
  let state ← p.loadState .acquire once
  if state != 1 then initPerProcess r p once state
  p.valueAsTarget once

/--
Julia source: base/lock.jl:850-861 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copyto_monotonic!(dest::AtomicMemory, src)
    i = 1
    for j in eachindex(src)
        if isassigned(src, j)
            @atomic :monotonic dest[i] = src[j]
        #else
        #    _unsetindex_atomic!(dest, i, src[j], :monotonic)
        end
        i += 1
    end
    dest
end
```
-/
def copytoMonotonic {Dest Src Index Iter V : Type}
    (next : Src → Option Iter → M E W (Option (Index × Iter)))
    (assigned : Src → Index → M E W Bool) (get : Src → Index → M E W V)
    (store : MemoryOrder → Dest → I → V → M E W Unit) (dest : Dest) (src : Src) : M E W Dest :=
  loop (fun (state : Option Iter × I) => do
    match ← next src state.1 with
    | none => pure (.inl dest)
    | some (index, iter) =>
      if ← assigned src index then store .monotonic dest state.2 (← get src index)
      pure (.inr (some iter, state.2 + int 1))) (none, int 1)

/--
Julia source: base/lock.jl:863-868 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function fill_monotonic!(dest::AtomicMemory, x)
    for i = 1:length(dest)
        @atomic :monotonic dest[i] = x
    end
    dest
end
```
-/
def fillMonotonic {Memory V : Type} (p : AtomicMemoryOps E W Memory V) (dest : Memory) (value : V) : M E W Memory := do
  let count ← p.length dest
  loop (fun (state : Nat × I) => do
    match state.1 with
    | 0 => pure (.inl dest)
    | n + 1 =>
      p.store .monotonic dest state.2 value
      pure (.inr (n, state.2 + int 1))) (count.val.toNat, int 1)

/--
Julia source: base/lock.jl:919-923 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function OncePerThread{T,F}(initializer::F) where {T, F}
        xs, ss = AtomicMemory{T}(), AtomicMemory{UInt8}()
        once = new{T,F}(xs, ss, initializer)
        return once
    end
```
-/
def newOncePerThread {Once F V Values States : Type} (p : ThreadOnceOps E W Once F V Values States)
    (initializer : F) : M E W Once := do
  let values ← p.values.newEmpty
  let states ← p.states.newEmpty
  p.allocate values states initializer

/--
Julia source: base/lock.jl:936-1015 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        (@noinline function init_perthread(once::OncePerThread{T,F}, tid::Int) where {T,F}
            local ss = @atomic :acquire once.ss
            local xs = @atomic :monotonic once.xs
            local len = length(ss)
            # slow path to allocate it
            nt = Threads.maxthreadid()
            0 < tid <= nt || throw(ArgumentError("thread id outside of allocated range"))
            if tid <= length(ss) && (@atomic :acquire ss[tid]) == PerStateErrored
                error("OncePerThread initializer failed previously")
            end
            newxs = xs
            newss = ss
            if tid > len
                # attempt to do all allocations outside of PerThreadLock for better scaling
                @assert length(xs) >= length(ss) "logical constraint violation"
                newxs = typeof(xs)(undef, len + nt)
                newss = typeof(ss)(undef, len + nt)
            end
            # uses state and locks to ensure this runs exactly once per tid argument
            lock(PerThreadLock)
            try
                ss = @atomic :monotonic once.ss
                xs = @atomic :monotonic once.xs
                if tid > length(ss)
                    if length(ss) == 0 # We are the first to initialize
                        ccall(:jl_set_precompile_field_replace, Cvoid, (Any, Any, Any),
                            once, :xs, xs)
                        ccall(:jl_set_precompile_field_replace, Cvoid, (Any, Any, Any),
                            once, :ss, ss)
                    end
                    @assert len <= length(ss) <= length(newss) "logical constraint violation"
                    fill_monotonic!(newss, PerStateInitial)
                    xs = copyto_monotonic!(newxs, xs)
                    ss = copyto_monotonic!(newss, ss)
                    @atomic :release once.xs = xs
                    @atomic :release once.ss = ss
                end
                state = @atomic :monotonic ss[tid]
                while state == PerStateConcurrent
                    # lost race, wait for notification this is done running elsewhere
                    # without releasing this thread
                    unlock(PerThreadLock)
                    while state == PerStateConcurrent
                        # spin loop until ready
                        ss = @atomic :acquire once.ss
                        state = @atomic :monotonic ss[tid]
                        GC.safepoint()
                    end
                    lock(PerThreadLock)
                    ss = @atomic :monotonic once.ss
                    state = @atomic :monotonic ss[tid]
                end
                if state == PerStateInitial
                    # won the race, drop lock in exchange for state, and run user initializer
                    @atomic :monotonic ss[tid] = PerStateConcurrent
                    result = try
                        unlock(PerThreadLock)
                        once.initializer()
                    catch
                        lock(PerThreadLock)
                        ss = @atomic :monotonic once.ss
                        @atomic :release ss[tid] = PerStateErrored
                        rethrow()
                    end
                    # store result and notify waiters
                    lock(PerThreadLock)
                    xs = @atomic :monotonic once.xs
                    @atomic :release xs[tid] = result
                    ss = @atomic :monotonic once.ss
                    @atomic :release ss[tid] = PerStateHasrun
                elseif state == PerStateErrored
                    error("OncePerThread initializer failed previously")
                elseif state != PerStateHasrun
                    error("invalid state for OncePerThread")
                end
            finally
                unlock(PerThreadLock)
            end
            nothing
        end)(once, tid)
```
-/
def initPerThread {Once F V Values States : Type} (p : ThreadOnceOps E W Once F V Values States)
    (once : Once) (tid : I) : M E W Unit := do
  let states ← p.loadStates .acquire once
  let values ← p.loadValues .monotonic once
  let len ← p.states.length states
  let nt ← p.maxThreadId
  if !(0 < tid.val && tid.val ≤ nt.val) then throw (p.argumentError "thread id outside of allocated range")
  if tid.val ≤ (← p.states.length states).val then
    if (← p.states.load .acquire states tid) == 2 then throw (p.error "OncePerThread initializer failed previously")
  let mut newValues := values
  let mut newStates := states
  if tid.val > len.val then
    if (← p.values.length values).val < (← p.states.length states).val then throw (p.assertionError "logical constraint violation")
    newValues ← p.values.allocate (len + nt)
    newStates ← p.states.allocate (len + nt)
  p.lock
  finallyDo (do
    let mut workingStates ← p.loadStates .monotonic once
    let mut workingValues ← p.loadValues .monotonic once
    if tid.val > (← p.states.length workingStates).val then
      if (← p.states.length workingStates).val == 0 then
        p.replaceValuesOnPrecompile once workingValues
        p.replaceStatesOnPrecompile once workingStates
      let currentLength ← p.states.length workingStates
      if !(len.val ≤ currentLength.val && currentLength.val ≤ (← p.states.length newStates).val) then
        throw (p.assertionError "logical constraint violation")
      let _ ← fillMonotonic p.states newStates 0
      workingValues ← copytoMonotonic p.values.nextIndex p.values.isAssigned (p.values.load .plain) p.values.store newValues workingValues
      workingStates ← copytoMonotonic p.states.nextIndex p.states.isAssigned (p.states.load .plain) p.states.store newStates workingStates
      p.storeValues .release once workingValues
      p.storeStates .release once workingStates
    let state ← p.states.load .monotonic workingStates tid
    let (states, state) ← loop (fun (pair : States × UInt8) => do
      if pair.2 != 3 then return .inl pair
      p.unlock
      let _ ← loop (fun (pair : States × UInt8) => do
        if pair.2 != 3 then return .inl pair
        let states ← p.loadStates .acquire once
        let state ← p.states.load .monotonic states tid
        p.gcSafepoint
        pure (.inr (states, state))) pair
      p.lock
      let states ← p.loadStates .monotonic once
      let state ← p.states.load .monotonic states tid
      pure (.inr (states, state))) (workingStates, state)
    if state == 0 then
      p.states.store .monotonic states tid 3
      let result ← tryCatch (do
        p.unlock
        p.call (p.initializer once)) (fun error => do
          p.lock
          let states ← p.loadStates .monotonic once
          p.states.store .release states tid 2
          throw error)
      p.lock
      let values ← p.loadValues .monotonic once
      p.values.store .release values tid result
      let states ← p.loadStates .monotonic once
      p.states.store .release states tid 1
    else if state == 2 then throw (p.error "OncePerThread initializer failed previously")
    else if state != 1 then throw (p.error "invalid state for OncePerThread")) p.unlock

/--
Julia source: base/lock.jl:930-1019 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function getindex(once::OncePerThread{T,F}, tid::Integer) where {T,F}
    tid = Int(tid)
    ss = @atomic :acquire once.ss
    xs = @atomic :monotonic once.xs
    # n.b. length(xs) >= length(ss)
    if tid <= 0 || tid > length(ss) || (@atomic :acquire ss[tid]) != PerStateHasrun
        (@noinline function init_perthread(once::OncePerThread{T,F}, tid::Int) where {T,F}
            local ss = @atomic :acquire once.ss
            local xs = @atomic :monotonic once.xs
            local len = length(ss)
            # slow path to allocate it
            nt = Threads.maxthreadid()
            0 < tid <= nt || throw(ArgumentError("thread id outside of allocated range"))
            if tid <= length(ss) && (@atomic :acquire ss[tid]) == PerStateErrored
                error("OncePerThread initializer failed previously")
            end
            newxs = xs
            newss = ss
            if tid > len
                # attempt to do all allocations outside of PerThreadLock for better scaling
                @assert length(xs) >= length(ss) "logical constraint violation"
                newxs = typeof(xs)(undef, len + nt)
                newss = typeof(ss)(undef, len + nt)
            end
            # uses state and locks to ensure this runs exactly once per tid argument
            lock(PerThreadLock)
            try
                ss = @atomic :monotonic once.ss
                xs = @atomic :monotonic once.xs
                if tid > length(ss)
                    if length(ss) == 0 # We are the first to initialize
                        ccall(:jl_set_precompile_field_replace, Cvoid, (Any, Any, Any),
                            once, :xs, xs)
                        ccall(:jl_set_precompile_field_replace, Cvoid, (Any, Any, Any),
                            once, :ss, ss)
                    end
                    @assert len <= length(ss) <= length(newss) "logical constraint violation"
                    fill_monotonic!(newss, PerStateInitial)
                    xs = copyto_monotonic!(newxs, xs)
                    ss = copyto_monotonic!(newss, ss)
                    @atomic :release once.xs = xs
                    @atomic :release once.ss = ss
                end
                state = @atomic :monotonic ss[tid]
                while state == PerStateConcurrent
                    # lost race, wait for notification this is done running elsewhere
                    # without releasing this thread
                    unlock(PerThreadLock)
                    while state == PerStateConcurrent
                        # spin loop until ready
                        ss = @atomic :acquire once.ss
                        state = @atomic :monotonic ss[tid]
                        GC.safepoint()
                    end
                    lock(PerThreadLock)
                    ss = @atomic :monotonic once.ss
                    state = @atomic :monotonic ss[tid]
                end
                if state == PerStateInitial
                    # won the race, drop lock in exchange for state, and run user initializer
                    @atomic :monotonic ss[tid] = PerStateConcurrent
                    result = try
                        unlock(PerThreadLock)
                        once.initializer()
                    catch
                        lock(PerThreadLock)
                        ss = @atomic :monotonic once.ss
                        @atomic :release ss[tid] = PerStateErrored
                        rethrow()
                    end
                    # store result and notify waiters
                    lock(PerThreadLock)
                    xs = @atomic :monotonic once.xs
                    @atomic :release xs[tid] = result
                    ss = @atomic :monotonic once.ss
                    @atomic :release ss[tid] = PerStateHasrun
                elseif state == PerStateErrored
                    error("OncePerThread initializer failed previously")
                elseif state != PerStateHasrun
                    error("invalid state for OncePerThread")
                end
            finally
                unlock(PerThreadLock)
            end
            nothing
        end)(once, tid)
        xs = @atomic :monotonic once.xs
    end
    return xs[tid]
end
```
-/
def oncePerThreadGetindex {Once F V Values States Index : Type} (p : ThreadOnceOps E W Once F V Values States)
    (toInt : Index → M E W I) (once : Once) (index : Index) : M E W V := do
  let tid ← toInt index
  let states ← p.loadStates .acquire once
  let mut values ← p.loadValues .monotonic once
  let mut needsInit : Bool := tid.val ≤ 0
  if !needsInit then
    if tid.val > (← p.states.length states).val then needsInit := true
    else needsInit := (← p.states.load .acquire states tid) != 1
  if needsInit then
    initPerThread p once tid
    values ← p.loadValues .monotonic once
  p.values.load .plain values tid

/--
Julia source: base/lock.jl:929-929 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline (once::OncePerThread{T,F})() where {T,F} = once[Threads.threadid()]
```
-/
def oncePerThread {Once F V Values States : Type} (p : ThreadOnceOps E W Once F V Values States) (once : Once) : M E W V := do
  let tid ← JuliaLean.base.threadingconstructs.threadid r.task.condition.queries
  oncePerThreadGetindex p pure once tid

/--
Julia source: base/lock.jl:1061-1063 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function (once::OncePerTask{T,F})() where {T,F}
    get!(once.initializer, task_local_storage(), once)::T
end
```
-/
def oncePerTask {Once F Store V : Type} (initializer : Once → F)
    (taskLocalStorage : M E W Store) (getOrInit : F → Store → Once → M E W V)
    (assertTarget : V → M E W V) (once : Once) : M E W V := do
  let value ← getOrInit (initializer once) (← taskLocalStorage) once
  assertTarget value

/--
Julia source: base/lock.jl:813-813 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
OncePerProcess{T}(initializer::Type{U}) where {T, U} = OncePerProcess{T, Type{U}}(initializer)
```
-/
def oncePerProcessTypeConstructor {Ty F Once : Type} (p : OnceTypeOps E W Ty F Once)
    (target sourceType : Ty) (initializer : F) : M E W Once :=
  p.construct target (p.typeOfType sourceType) initializer

/--
Julia source: base/lock.jl:814-814 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
OncePerProcess{T}(initializer::F) where {T, F} = OncePerProcess{T, F}(initializer)
```
-/
def oncePerProcessTypedConstructor {Ty F Once : Type} (p : OnceTypeOps E W Ty F Once)
    (target initializerType : Ty) (initializer : F) : M E W Once :=
  p.construct target initializerType initializer

/--
Julia source: base/lock.jl:815-815 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
OncePerProcess(initializer::Type{U}) where U = OncePerProcess{Base.promote_op(initializer), Type{U}}(initializer)
```
-/
def oncePerProcessInferredType {Ty F Once : Type} (p : OnceTypeOps E W Ty F Once)
    (sourceType : Ty) (initializer : F) : M E W Once := do
  p.construct (← p.promoteOp initializer) (p.typeOfType sourceType) initializer

/--
Julia source: base/lock.jl:816-816 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
OncePerProcess(initializer) = OncePerProcess{Base.promote_op(initializer), typeof(initializer)}(initializer)
```
-/
def oncePerProcessInferred {Ty F Once : Type} (p : OnceTypeOps E W Ty F Once) (initializer : F) : M E W Once := do
  p.construct (← p.promoteOp initializer) (p.typeofInitializer initializer) initializer

/--
Julia source: base/lock.jl:925-925 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
OncePerThread{T}(initializer::Type{U}) where {T, U} = OncePerThread{T,Type{U}}(initializer)
```
-/
def oncePerThreadTypeConstructor {Ty F Once : Type} (p : OnceTypeOps E W Ty F Once)
    (target sourceType : Ty) (initializer : F) : M E W Once :=
  p.construct target (p.typeOfType sourceType) initializer

/--
Julia source: base/lock.jl:926-926 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
OncePerThread{T}(initializer::F) where {T, F} = OncePerThread{T,F}(initializer)
```
-/
def oncePerThreadTypedConstructor {Ty F Once : Type} (p : OnceTypeOps E W Ty F Once)
    (target initializerType : Ty) (initializer : F) : M E W Once :=
  p.construct target initializerType initializer

/--
Julia source: base/lock.jl:927-927 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
OncePerThread(initializer::Type{U}) where U = OncePerThread{Base.promote_op(initializer), Type{U}}(initializer)
```
-/
def oncePerThreadInferredType {Ty F Once : Type} (p : OnceTypeOps E W Ty F Once)
    (sourceType : Ty) (initializer : F) : M E W Once := do
  p.construct (← p.promoteOp initializer) (p.typeOfType sourceType) initializer

/--
Julia source: base/lock.jl:928-928 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
OncePerThread(initializer) = OncePerThread{Base.promote_op(initializer), typeof(initializer)}(initializer)
```
-/
def oncePerThreadInferred {Ty F Once : Type} (p : OnceTypeOps E W Ty F Once) (initializer : F) : M E W Once := do
  p.construct (← p.promoteOp initializer) (p.typeofInitializer initializer) initializer

/--
Julia source: base/lock.jl:1055-1055 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    OncePerTask{T}(initializer::Type{U}) where {T, U} = new{T,Type{U}}(initializer)
```
-/
def oncePerTaskTypeConstructor {Ty F Once : Type} (p : OnceTypeOps E W Ty F Once)
    (target sourceType : Ty) (initializer : F) : M E W Once :=
  p.allocate target (p.typeOfType sourceType) initializer

/--
Julia source: base/lock.jl:1056-1056 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    OncePerTask{T}(initializer::F) where {T, F} = new{T,F}(initializer)
```
-/
def oncePerTaskTypedConstructor {Ty F Once : Type} (p : OnceTypeOps E W Ty F Once)
    (target initializerType : Ty) (initializer : F) : M E W Once :=
  p.allocate target initializerType initializer

/--
Julia source: base/lock.jl:1057-1057 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    OncePerTask{T,F}(initializer::F) where {T, F} = new{T,F}(initializer)
```
-/
def oncePerTaskExplicitConstructor {Ty F Once : Type} (p : OnceTypeOps E W Ty F Once)
    (target initializerType : Ty) (initializer : F) : M E W Once :=
  p.allocate target initializerType initializer

/--
Julia source: base/lock.jl:1058-1058 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    OncePerTask(initializer::Type{U}) where U = new{Base.promote_op(initializer), Type{U}}(initializer)
```
-/
def oncePerTaskInferredType {Ty F Once : Type} (p : OnceTypeOps E W Ty F Once)
    (sourceType : Ty) (initializer : F) : M E W Once := do
  p.allocate (← p.promoteOp initializer) (p.typeOfType sourceType) initializer

/--
Julia source: base/lock.jl:1059-1059 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    OncePerTask(initializer) = new{Base.promote_op(initializer), typeof(initializer)}(initializer)
```
-/
def oncePerTaskInferred {Ty F Once : Type} (p : OnceTypeOps E W Ty F Once) (initializer : F) : M E W Once := do
  p.allocate (← p.promoteOp initializer) (p.typeofInitializer initializer) initializer

/--
Julia source: base/lock.jl:90-90 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, ::ReentrantLock) = print(io, ReentrantLock, "()")
```
-/
def showReentrantLock {IO V : Type} (p : LockDisplayOps E W IO Task V) (io : IO) (_l : RL) : M E W Unit :=
  p.print io [.reentrantLockType, .text "()"]

/--
Julia source: base/lock.jl:92-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, ::MIME"text/plain", l::ReentrantLock)
    show(io, l)
    if !(get(io, :compact, false)::Bool)
        locked_by = l.locked_by
        if locked_by isa Task
            print(io, " (locked by ", locked_by === current_task() ? "current " : "", locked_by, ")")
        else
            print(io, " (unlocked)")
        end
    end
end
```
-/
def showReentrantLockPlain {IO V : Type} (p : LockDisplayOps E W IO Task V) (io : IO) (l : RL) : M E W Unit := do
  showReentrantLock p io l
  if !(← p.assertBool (← p.getCompact io false)) then
    match ← r.loadOwner .plain l with
    | some owner =>
      let current ← currentTask r
      p.print io [.text " (locked by ", .text (if r.task.sameTask owner current then "current " else ""), .task owner, .text ")"]
    | none => p.print io [.text " (unlocked)"]

-- UNTRANSLATED
-- Source: base/lock.jl:431-441 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro lock(l, expr)
--     quote
--         temp = $(esc(l))
--         lock(temp)
--         try
--             $(esc(expr))
--         finally
--             unlock(temp)
--         end
--     end
-- end
-- /Source
-- Reason: Compile-time Julia AST quotation, escaping, and macro expansion are untranslated; the corresponding runtime lock/acquire functions are modelled.

-- UNTRANSLATED
-- Source: base/lock.jl:450-458 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro lock_nofail(l, expr)
--     quote
--         temp = $(esc(l))
--         lock(temp)
--         val = $(esc(expr))
--         unlock(temp)
--         val
--     end
-- end
-- /Source
-- Reason: Compile-time Julia AST quotation, escaping, and macro expansion are untranslated; the corresponding runtime lock/acquire functions are modelled.

-- UNTRANSLATED
-- Source: base/lock.jl:650-660 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro acquire(s, expr)
--     quote
--         local temp = $(esc(s))
--         Base.acquire(temp)
--         try
--             $(esc(expr))
--         finally
--             Base.release(temp)
--         end
--     end
-- end
-- /Source
-- Reason: Compile-time Julia AST quotation, escaping, and macro expansion are untranslated; the corresponding runtime lock/acquire functions are modelled.


end
end JuliaLean.base.lock

namespace JuliaLean.ConcurrencyCov.Locks

open JuliaLean JuliaLean.ConcurrencyCov

/-- `LOCKED_BIT` and `PARKED_BIT`, lines 12-16. -/
def LOCKED : Nat := 1
def PARKED : Nat := 2

/-- The fields of `ReentrantLock` (lines 48-86) with the queue of its `cond_wait`. -/
structure RLock where
  lockedBy : Option Nat := none
  cnt : U32 := u32 0
  /-- `havelock`, two bits. -/
  havelock : Nat := 0
  waitq : List Nat := []
  deriving DecidableEq, Repr

/-- Lock plus the per-task finalizer-inhibit counters and the tasks woken by
`notify` (which retry the acquisition in their own later step). -/
structure St where
  l : RLock
  fin : Nat → Int
  woken : List Nat := []

def St.disableFin (s : St) (t : Nat) : St := { s with fin := upd s.fin t (s.fin t + 1) }
def St.enableFin (s : St) (t : Nat) : St := { s with fin := upd s.fin t (s.fin t - 1) }

/-- `current_task()`, line 10: the running task. -/
def currentTask (cur : Nat) : Nat := cur

/-- `ReentrantLock()`, line 85. -/
def reentrantLock : RLock := {}

/-- `islocked(rl)`, lines 143-145. -/
def islocked (l : RLock) : Bool := l.havelock % 2 = 1

/-- `assert_havelock(l, l.locked_by)` (line 88 with base/condition.jl:32-36). -/
def assertHavelock (t : Nat) (l : RLock) : R Unit :=
  match l.lockedBy with
  | none => .error .concurrencyViolation
  | some o => if islocked l ∧ o = t then .ok () else .error .concurrencyViolation

/-- `show(io, ::ReentrantLock)`, line 90. -/
def showLock : String := "ReentrantLock()"

/-- `show(io, ::MIME"text/plain", l)`, lines 92-102; `cur` is `current_task()`
and task `n` prints as `Task#n`. -/
def showPlain (compact : Bool) (cur : Nat) (l : RLock) : String :=
  showLock ++ (if compact then "" else match l.lockedBy with
    | some o => " (locked by " ++ (if o = cur then "current " else "") ++ s!"Task#{o})"
    | none => " (unlocked)")

/-- `_trylock(rl, ct)`, lines 173-183: the compare-and-swap of `havelock` from its
parked bit alone to that bit plus the locked bit. -/
def trylockSlow (t : Nat) (s : St) : Bool × St :=
  let s := s.disableFin t
  let state := (s.l.havelock / 2 % 2) * PARKED
  if s.l.havelock = state then
    (true, { s with l := { s.l with havelock := state + LOCKED, cnt := u32 1, lockedBy := some t } })
  else (false, s.enableFin t)

/-- `trylock(rl)`, lines 165-172. -/
def trylock (t : Nat) (s : St) : Bool × St :=
  if s.l.lockedBy = some t then
    (true, { s with l := { s.l with cnt := s.l.cnt + u32 1 } })
  else trylockSlow t s

/-- Result of one `lock` step. -/
inductive LockStep where
  | acquired (s : St)
  /-- The task parked on `cond_wait` (lines 234-250). -/
  | parked (s : St)
  /-- A cancelled token refused the acquisition (lines 213-219). -/
  | refused (e : Exn) (s : St)

/-- One pass of `slowlock`'s loop (lines 196-255) for a task that does not hold
the lock: grab it when the locked bit is clear (releasing it again and throwing
when its token was cancelled meanwhile); otherwise set the parked bit and park. -/
def slowlock (t : Nat) (tok : Option Bool) (s : St) : LockStep :=
  let state := s.l.havelock
  if state % 2 = 0 then
    let s := s.disableFin t
    let s := { s with l := { s.l with havelock := state + LOCKED, cnt := u32 1, lockedBy := some t } }
    if tok = some true then
      -- `unlock(rl)` of the just-acquired hold, then `checkcancel`
      let s := { s with l := { s.l with lockedBy := none, cnt := u32 0, havelock := state } }
      .refused (.cancellation 1) (s.enableFin t)
    else .acquired s
  else
    .parked { s with l := { s.l with havelock := LOCKED + PARKED, waitq := s.l.waitq ++ [t] } }

/-- `lock(rl; cancel)`, lines 194-257: the fast `trylock`, else `slowlock`. -/
def lock (t : Nat) (tok : Option Bool) (s : St) : LockStep :=
  match trylock t s with
  | (true, s) => .acquired s
  | (false, s) => slowlock t tok s

/-- `lock(c::GenericCondition{ReentrantLock}; cancel)`, lines 263-264, and
`_uncancellable_lock(l)`, line 299 (no token). -/
def lockCond (t : Nat) (tok : Option Bool) (s : St) : LockStep := lock t tok s
def uncancellableLock (t : Nat) (s : St) : LockStep := lock t none s

/-- `notifywaiters(rl)`, lines 327-341: wake the first waiter; the parked bit stays
set while waiters remain. -/
def notifywaiters (s : St) : St :=
  match s.l.waitq with
  | [] => { s with l := { s.l with havelock := 0 } }
  | w :: q =>
    { s with l := { s.l with waitq := q, havelock := if q.isEmpty then 0 else PARKED },
             woken := s.woken ++ [w] }

/-- `_unlock(rl)`, lines 318-346: `true` when the hold count reached zero. -/
def unlockInner (s : St) : Bool × St :=
  let n := s.l.cnt - u32 1
  let s := { s with l := { s.l with cnt := n } }
  if n.val = 0 then
    let s := { s with l := { s.l with lockedBy := none } }
    if s.l.havelock = LOCKED then (true, { s with l := { s.l with havelock := 0 } })
    else (true, notifywaiters s)
  else (false, s)

/-- `unlock(rl)`, lines 315-348. -/
def unlock (t : Nat) (s : St) : R St :=
  if s.l.lockedBy ≠ some t then
    .error (.errorException (if s.l.cnt.val = 0 then "unlock count must match lock count"
      else "unlock from wrong thread"))
  else
    match unlockInner s with
    | (true, s) => .ok (s.enableFin t)
    | (false, s) => .ok s

/-- `unlockall(rl)`, lines 350-354: the old count, after releasing every level. -/
def unlockall (t : Nat) (s : St) : R (U32 × St) := do
  let n := s.l.cnt
  let s ← unlock t { s with l := { s.l with cnt := u32 1 } }
  return (n, s)

/-- `relockall(rl, n)` after its `lock(rl; cancel=nothing)` acquired, lines 356-365. -/
def relockall (n : U32) (s : St) : R St :=
  let old := s.l.cnt
  let s := { s with l := { s.l with cnt := n } }
  if old.val = 1 then .ok s else .error .concurrencyViolation

/-- `relockall_but_one(rl, state)`, lines 301-305: `none` when nothing is relocked,
otherwise the count `relockall` restores. -/
def relockallButOne (state : U32) : Option U32 :=
  if state.val = 1 then none else some (state - u32 1)

/-- `wait_no_relock(c, tok)`, lines 266-296: with no token, or a token not yet
cancelled, the task is registered and parks; a cancelled token is refused at the
registration recheck, so the task is withdrawn and the refusal thrown. -/
inductive Parked where
  | parked
  | refused (e : Exn)
  deriving DecidableEq, Repr

def waitNoRelock (tok : Option Bool) : Parked :=
  if tok = some true then .refused (.cancellation 1) else .parked

/-! ## Closure forms, lines 367-515 -/

/-- A function run under the lock: its outcome. -/
abbrev Body := Outcome

/-- `lock(f, l)` (lines 382-389 and 392-399) when `lock` acquires: `f()` then the
`unlock` of the `finally` block. -/
def lockDo (t : Nat) (f : Body) (s : St) : R (Nat × St) :=
  match lock t none s with
  | .acquired s =>
    match unlock t s with
    | .ok s => match f with
      | .ok v => .ok (v, s)
      | .error e => .error e
    | .error e => .error e
  | .parked _ => .error (.errorException "blocked")
  | .refused e _ => .error e

/-- The state after `lockDo`. -/
def lockDoState (t : Nat) (s : St) : Option St :=
  match lock t none s with
  | .acquired s => (unlock t s).toOption
  | _ => none

/-- `trylock(f, l)`, lines 401-410: `false` (as `none`) without calling `f` when
the lock is unavailable. -/
def trylockDo (t : Nat) (f : Body) (s : St) : R (Option Nat) × St :=
  match trylock t s with
  | (false, s) => (.ok none, s)
  | (true, s) =>
    match unlock t s with
    | .ok s' => (f.map some, s')
    | .error e => (.error e, s)

/-- `@lock l expr`, lines 431-441: `lock(temp); try expr finally unlock(temp) end`. -/
def lockMacro (t : Nat) (expr : Body) (s : St) : R (Nat × St) := lockDo t expr s

/-- `@lock_nofail l expr`, lines 450-458: no `try`, so an exception from `expr`
leaves the lock held. -/
def lockNofail (t : Nat) (expr : Body) (s : St) : R Nat × St :=
  match lock t none s with
  | .acquired s =>
    match expr with
    | .ok v => match unlock t s with
      | .ok s' => (.ok v, s')
      | .error e => (.error e, s)
    | .error e => (.error e, s)
  | .parked s => (.error (.errorException "blocked"), s)
  | .refused e s => (.error e, s)

/-- `Lockable(value, lock)`, lines 485-491. -/
structure Lockable where
  value : Nat
  lock : St

/-- `Lockable(value)`, line 490: a fresh `ReentrantLock`. -/
def lockable (value : Nat) : Lockable := ⟨value, ⟨reentrantLock, fun _ => 0, []⟩⟩

/-- `getindex(l::Lockable)`, line 491. -/
def lockableGet (t : Nat) (l : Lockable) : R Nat := do
  assertHavelock t l.lock.l
  return l.value

/-- `lock(f, l::Lockable)`, lines 506-510: `f` receives the value. -/
def lockableDo (t : Nat) (f : Nat → Body) (l : Lockable) : R (Nat × St) := lockDo t (f l.value) l.lock

/-- `lock`, `trylock`, `unlock` of a `Lockable`, lines 513-515. -/
def lockableLock (t : Nat) (l : Lockable) : LockStep := lock t none l.lock
def lockableTrylock (t : Nat) (l : Lockable) : Bool × St := trylock t l.lock
def lockableUnlock (t : Nat) (l : Lockable) : R St := unlock t l.lock

/-! ## Semaphore and Event, lines 556-763 -/

/-- `Semaphore(sem_size)`, line 569, for integer sizes. -/
structure Sem where
  size : Int
  curr : Int
  deriving DecidableEq, Repr

def semaphore (sz : Int) : R Sem :=
  if 0 < sz then .ok ⟨sz, 0⟩ else .error (.argumentError "Semaphore size must be > 0")

/-- One `acquire(s)` step, lines 578-597: take a permit or wait for one. -/
def acquire (s : Sem) : Option Sem := if s.curr < s.size then some { s with curr := s.curr + 1 } else none

/-- `release(s)`, lines 669-679. -/
def release (s : Sem) : R Sem :=
  if 0 < s.curr then .ok { s with curr := s.curr - 1 }
  else .error (.errorException "release count must match acquire count")

/-- `acquire(f, s)`, lines 623-630, and `@acquire s expr`, lines 650-660: `f` runs
holding a permit, which the `finally` block returns. -/
def acquireDo (f : Body) (s : Sem) : Option (R Nat × Sem) :=
  match acquire s with
  | none => none
  | some s' => match release s' with
    | .ok s'' => some (f, s'')
    | .error e => some (.error e, s')

def acquireMacro (expr : Body) (s : Sem) : Option (R Nat × Sem) := acquireDo expr s

/-- `Event(autoreset)`, line 705. -/
structure Event where
  autoreset : Bool
  set : Bool
  deriving DecidableEq, Repr

def event (autoreset : Bool := false) : Event := ⟨autoreset, false⟩

/-- `reset(e)`, lines 755-758. -/
def reset (e : Event) : Event := { e with set := false }

/-! ## Once-per-process, -thread and -task values, lines 765-1063 -/

/-- `PerStateInitial`, `PerStateHasrun`, `PerStateErrored`, `PerStateConcurrent`. -/
inductive PerState where
  | initial | hasrun | errored | concurrent
  deriving DecidableEq, Repr

/-- A `OncePerProcess`: its stored value, state and initializer. The initializer's
successive calls return the outcomes in `inits` (index = number of earlier runs). -/
structure OnceProc where
  value : Option Nat
  state : PerState
  runs : Nat
  deriving DecidableEq, Repr

/-- The constructors at lines 808-816 all build `new(nothing, PerStateInitial, true,
initializer, ReentrantLock())`; the type parameter only differs. -/
def oncePerProcess : OnceProc := ⟨none, .initial, 0⟩

/-- `init_perprocesss(once, state)`, lines 820-845, holding `once.lock`. -/
def initPerprocess (init : Nat → Outcome) (state : PerState) (o : OnceProc) : R OnceProc :=
  if state = .errored then .error (.errorException "OncePerProcess initializer failed previously")
  else
    match o.state with
    | .initial =>
      match init o.runs with
      | .ok v => .ok { value := some v, state := .hasrun, runs := o.runs + 1 }
      | .error e => .error e
    | .errored => .error (.errorException "OncePerProcess initializer failed previously")
    | .hasrun => .ok o
    | .concurrent => .error (.errorException "invalid state for OncePerProcess")

/-- The state after a failed initializer run (the `catch` branch, line 838). -/
def initFailed (o : OnceProc) : OnceProc :=
  if o.state = .initial then { o with state := .errored, runs := o.runs + 1 } else
  if o.state = .hasrun then o else { o with state := .errored }

/-- `(once::OncePerProcess)()`, lines 817-848: the value and the new state. -/
def callOnceProc (init : Nat → Outcome) (o : OnceProc) : R Nat × OnceProc :=
  if o.state = .hasrun then (o.value.elim (.error .methodError) .ok, o)
  else
    match initPerprocess init o.state o with
    | .ok o' => (o'.value.elim (.error .methodError) .ok, o')
    | .error e => (.error e, if o.state = .errored then o else initFailed o)

/-- `copyto_monotonic!(dest, src)`, lines 850-861: assigned source slots are stored
at the same position; `dest[i]` is bounds-checked. -/
def copytoMonotonic {α : Type} (dest src : List (Option α)) : R (List (Option α)) :=
  if src.length ≤ dest.length then
    .ok ((List.range dest.length).map fun i =>
      match src[i]? with
      | some (some x) => some x
      | _ => dest[i]?.getD none)
  else .error .boundsError

/-- `fill_monotonic!(dest, x)`, lines 863-868. -/
def fillMonotonic {α : Type} (dest : List (Option α)) (x : α) : List (Option α) :=
  dest.map fun _ => some x

/-- A `OncePerThread`: per-thread states and values (`ss`, `xs`), and the number of
initializer runs. -/
structure OnceThread where
  ss : List PerState
  xs : List (Option Nat)
  runs : Nat
  deriving DecidableEq, Repr

/-- The constructors at lines 919-928 start with empty arrays. -/
def oncePerThread : OnceThread := ⟨[], [], 0⟩

/-- `getindex(once, tid)` (lines 930-1019) with `maxthreadid() = nt`, run by one
task without interference: grow the arrays to `len + nt` when needed, run the
initializer for an initial slot, and return the slot's value. -/
def onceThreadGet (init : Nat → Outcome) (nt : Nat) (tid : Int) (o : OnceThread) :
    R Nat × OnceThread :=
  if 0 < tid ∧ tid ≤ o.ss.length ∧ o.ss[(tid - 1).toNat]? = some .hasrun then
    ((o.xs[(tid - 1).toNat]?.join).elim (.error .boundsError) .ok, o)
  else if ¬ (0 < tid ∧ tid ≤ nt) then (.error (.argumentError "thread id outside of allocated range"), o)
  else
    let i := (tid - 1).toNat
    if tid ≤ o.ss.length ∧ o.ss[i]? = some .errored then
      (.error (.errorException "OncePerThread initializer failed previously"), o)
    else
      let o := if o.ss.length < tid then
          { o with ss := o.ss ++ List.replicate nt .initial, xs := o.xs ++ List.replicate nt none }
        else o
      match o.ss[i]? with
      | some .initial =>
        match init o.runs with
        | .ok v => (.ok v, { ss := o.ss.set i .hasrun, xs := o.xs.set i (some v), runs := o.runs + 1 })
        | .error e => (.error e, { o with ss := o.ss.set i .errored, runs := o.runs + 1 })
      | some .errored => (.error (.errorException "OncePerThread initializer failed previously"), o)
      | some .hasrun => ((o.xs[i]?.join).elim (.error .boundsError) .ok, o)
      | _ => (.error (.errorException "invalid state for OncePerThread"), o)

/-- `(once::OncePerThread)()`, line 929: `once[threadid()]`. -/
def callOnceThread (init : Nat → Outcome) (nt : Nat) (threadid : Int) (o : OnceThread) :
    R Nat × OnceThread := onceThreadGet init nt threadid o

/-- A `OncePerTask` call, lines 1061-1063: `get!(initializer, task_local_storage(),
once)` on the current task's storage, a map from tasks to values, and the runs. -/
structure OnceTask where
  store : Nat → Option Nat
  runs : Nat

/-- The constructors at lines 1055-1059 store only the initializer. -/
def oncePerTask : OnceTask := ⟨fun _ => none, 0⟩

def callOnceTask (init : Nat → Outcome) (task : Nat) (o : OnceTask) : R Nat × OnceTask :=
  match o.store task with
  | some v => (.ok v, o)
  | none =>
    match init o.runs with
    | .ok v => (.ok v, { store := upd o.store task (some v), runs := o.runs + 1 })
    | .error e => (.error e, { o with runs := o.runs + 1 })

end JuliaLean.ConcurrencyCov.Locks

namespace JuliaLean.ConcurrencyCov.FaithfulLock

open JuliaLean.ConcurrencyCov

def currentTaskM := Locks.currentTask
def reentrantCtor := Locks.reentrantLock
def assertHavelockM := Locks.assertHavelock
def showLockM := Locks.showLock
def showPlainM := Locks.showPlain
def islockedM := Locks.islocked
def trylockM := Locks.trylock
def trylockSlowM := Locks.trylockSlow
def lockM := Locks.lock
def slowlockM := Locks.slowlock
def conditionLockM := Locks.lockCond
def waitNoRelockM := Locks.waitNoRelock
def uncancellableM := Locks.uncancellableLock
def relockallButOneM := Locks.relockallButOne
def unlockM := Locks.unlock
def unlockInnerM := Locks.unlockInner
def notifywaitersM := Locks.notifywaiters
def unlockallM := Locks.unlockall
def relockallM := Locks.relockall
def genericLockDo (acquire : Nat → R Unit) (release : Nat → R Unit) (body : Outcome) (lock : Nat) : R Nat := do
  acquire lock
  match body with
  | .ok value => let _ ← release lock; return value
  | .error e => let _ ← release lock; .error e
def reentrantLockDoM := Locks.lockDo
def genericTrylockDoM := Locks.trylockDo
def lockMacroM := Locks.lockMacro
def lockNofailM := Locks.lockNofail
def lockableCtor := Locks.lockable
def lockableGetM := Locks.lockableGet
def lockableDoM := Locks.lockableDo
def lockableLockM := Locks.lockableLock
def lockableTrylockM := Locks.lockableTrylock
def lockableUnlockM := Locks.lockableUnlock
def semaphoreCtor := Locks.semaphore
def semaphoreAcquire := Locks.acquire
def semaphoreAcquireDo := Locks.acquireDo
def semaphoreMacro := Locks.acquireMacro
def semaphoreRelease := Locks.release
def eventCtor (autoreset : Bool) := Locks.event autoreset
def eventWait (event : Locks.Event) : Bool × Locks.Event :=
  if event.set then (true, if event.autoreset then { event with set := false } else event)
  else (false, event)
def eventNotify (event : Locks.Event) := { event with set := true }
def eventResetM := Locks.reset
structure ProcCtor where
  initializer : Nat
  cell : Locks.OnceProc
def procCtor (initializer : Nat) : ProcCtor := ⟨initializer, Locks.oncePerProcess⟩
def callProcM := Locks.callOnceProc
def initProcM := Locks.initPerprocess
def copyMonotonicM := @Locks.copytoMonotonic
def fillMonotonicM := @Locks.fillMonotonic
structure ThreadCtor where
  initializer : Nat
  cell : Locks.OnceThread
def threadCtor (initializer : Nat) : ThreadCtor := ⟨initializer, Locks.oncePerThread⟩
def callThreadM := Locks.callOnceThread
def threadGetM := Locks.onceThreadGet
def initThreadM := Locks.onceThreadGet
structure TaskCtor where
  initializer : Nat
  cell : Locks.OnceTask
def taskCtor (initializer : Nat) : TaskCtor := ⟨initializer, Locks.oncePerTask⟩
def callTaskM := Locks.callOnceTask

end JuliaLean.ConcurrencyCov.FaithfulLock

namespace JuliaLean.Tasks



/-! ## base/lock.jl:10-458, ReentrantLock and higher-order wrappers -/

structure CoverageReentrantLock where
  owner : Option Nat := none
  count : Nat := 0
  locked : Bool := false
  deriving Repr, DecidableEq

def newReentrantLock : CoverageReentrantLock := {}

def reentrantTryLock (lock : CoverageReentrantLock) (task : Nat) :
    Bool × CoverageReentrantLock :=
  if lock.owner == some task then
    (true, { lock with count := (lock.count + 1) % 2^32 })
  else if lock.locked then (false, lock)
  else (true, ⟨some task, 1, true⟩)

def reentrantUnlock (lock : CoverageReentrantLock) (task : Nat) :
    Except String CoverageReentrantLock :=
  if lock.owner != some task then .error "unlock owner"
  else
    let count := (lock.count + 2^32 - 1) % 2^32
    if count == 0 then .ok {} else .ok { lock with count := count }

def unlockAll (lock : CoverageReentrantLock) (task : Nat) :
    Except String (Nat × CoverageReentrantLock) :=
  if lock.owner == some task then .ok (lock.count, {}) else .error "unlock owner"

def relockAll (lock : CoverageReentrantLock) (task count : Nat) : CoverageReentrantLock :=
  if count == 0 then lock else ⟨some task, count % 2^32, true⟩

inductive WrappedCall (α : Type) where | returned (value : α) | threw
  deriving Repr, DecidableEq

def withLock (lockSucceeded bodySucceeded : Bool) (value : Nat) : WrappedCall Nat :=
  if !lockSucceeded then .threw else if bodySucceeded then .returned value else .threw

def lockableGet (holdsLock : Bool) (value : Nat) : WrappedCall Nat :=
  if holdsLock then .returned value else .threw

/-! ## base/lock.jl:565-679, Semaphore -/

structure CoverageSemaphore where
  size : Nat
  current : Nat := 0
  waiting : Nat := 0
  deriving Repr, DecidableEq

inductive SemaphoreResult where | acquired | parked | released | error
  deriving Repr, DecidableEq

def semaphoreAcquire (semaphore : CoverageSemaphore) : SemaphoreResult × CoverageSemaphore :=
  if semaphore.current < semaphore.size then
    (.acquired, { semaphore with current := semaphore.current + 1 })
  else (.parked, { semaphore with waiting := semaphore.waiting + 1 })

def semaphoreRelease (semaphore : CoverageSemaphore) : SemaphoreResult × CoverageSemaphore :=
  if semaphore.current == 0 then (.error, semaphore)
  else if 0 < semaphore.waiting then
    (.released, ⟨semaphore.size, semaphore.current - 1, semaphore.waiting - 1⟩)
  else (.released, { semaphore with current := semaphore.current - 1 })

/-! ## base/lock.jl:701-758, Event -/

structure CoverageEvent where
  autoreset : Bool
  set : Bool := false
  deriving Repr, DecidableEq

def eventWait (event : CoverageEvent) : Bool × CoverageEvent :=
  if event.set then (true, if event.autoreset then { event with set := false } else event)
  else (false, event)

def eventNotify (event : CoverageEvent) : CoverageEvent := { event with set := true }

def eventReset (event : CoverageEvent) : CoverageEvent := { event with set := false }

/-! ## base/lock.jl:801-868, OncePerProcess and AtomicMemory helpers -/

inductive OnceState where | initial | running | hasRun | failed
  deriving Repr, DecidableEq

structure OnceCell where
  state : OnceState := .initial
  value : Option Nat := none
  deriving Repr, DecidableEq

def oncePerProcess (cell : OnceCell) (initializer : Except Nat Nat) : OnceCell :=
  match cell.state with
  | .hasRun | .failed => cell
  | .running => cell
  | .initial =>
      match initializer with
      | .ok value => ⟨.hasRun, some value⟩
      | .error error => ⟨.failed, some error⟩

def copyMonotonic (source : List Nat) : List Nat := source

def fillMonotonic (length value : Nat) : List Nat := List.replicate length value

/-! ## base/lock.jl:914-1019, OncePerThread -/

def oncePerThreadGet (cells : List OnceCell) (thread : Nat) (initializer : Except Nat Nat) :
    List OnceCell :=
  match cells[thread]? with
  | none => cells
  | some cell => cells.set thread (oncePerProcess cell initializer)

/-! ## base/lock.jl:1052-1063, OncePerTask -/

def oncePerTaskGet (hasValue : Bool) (value initialized : Nat) : Nat :=
  if hasValue then value else initialized

end JuliaLean.Tasks

namespace JuliaLean.Channels



/-- Julia ErrorException; its messages distinguish the checks in base/lock.jl. -/
inductive LockError where
  | errorException (message : String)
  deriving DecidableEq

/-- Ownership and the locked bit of `base/lock.jl:143-179`; the recursion count is UInt32. -/
structure LockState where
  lockedBy : Option Nat := none
  reentrancy_cnt : JInt .u32 := JInt.lit .u32 0
  islocked : Bool := false
  deriving DecidableEq

/-- `base/lock.jl:165-183`: reentrant increment, uncontended acquisition, or failure. -/
def lockTry (t : Nat) (s : LockState) : Bool × LockState :=
  if s.lockedBy = some t then
    (true, { s with reentrancy_cnt := s.reentrancy_cnt + JInt.lit .u32 1 })
  else if s.islocked then (false, s)
  else (true, { lockedBy := some t, reentrancy_cnt := JInt.lit .u32 1, islocked := true })

/-- `base/lock.jl:315-347`: the ownership check precedes every mutation.
Condition notification after releasing the locked bit does not change these fields. -/
def lockUnlock (t : Nat) (s : LockState) : Except LockError Unit × LockState :=
  if s.lockedBy ≠ some t then
    (.error (.errorException (if s.reentrancy_cnt.val = 0 then
      "unlock count must match lock count" else "unlock from wrong thread")), s)
  else
    let n := s.reentrancy_cnt - JInt.lit .u32 1
    (.ok (), if n.val = 0 then { lockedBy := none, reentrancy_cnt := n, islocked := false }
      else { s with reentrancy_cnt := n })

/-- Repeated owner-only `trylock`, `base/lock.jl:167-169`. -/
def reentrantCount (c : JInt .u32) : Nat → JInt .u32
  | 0 => c
  | n + 1 => reentrantCount c n + JInt.lit .u32 1

/-- Owner-only acquisition trace, `base/lock.jl:165-179`; first acquisition sets one. -/
def lockAcquires (t : Nat) : Nat → LockState
  | 0 => {}
  | n + 1 => { lockedBy := some t, reentrancy_cnt := reentrantCount (JInt.lit .u32 1) n, islocked := true }

/-- Owner-only `unlock` trace, `base/lock.jl:315-347`; errors retain the state. -/
def lockUnlocks (t : Nat) : Nat → LockState → LockState
  | 0, s => s
  | k + 1, s => lockUnlocks t k (lockUnlock t s).2

/-- Semaphore operations at `base/lock.jl:578-597,669-679`, with no cancellation. -/
inductive SemOp where
  | acquire | release
  deriving DecidableEq

/-- Remaining operations are a per-task program counter. Task identities are scheduler labels. -/
structure SemTask where
  id : Nat
  ops : List SemOp
  deriving DecidableEq

/-- `base/lock.jl:565-569`. Counts are natural numbers counting live permits/tasks;
`curr_cnt < sem_size` before increment prevents Julia Int overflow. Queue membership
records the wait/relock program counter; `woken` tasks have wake value `nothing`. -/
structure SemState where
  curr : Nat := 0
  ready : List SemTask := []
  parked : List SemTask := []
  woken : List SemTask := []
  deriving DecidableEq

/-- `Semaphore(sem_size)`, `base/lock.jl:569`, for positive Julia Int sizes. -/
def semInitial (inputs : List (List SemOp)) : SemState :=
  { ready := inputs.zipIdx |>.map (fun (ops, id) => ⟨id, ops⟩) }

/-- `base/lock.jl:669-679`: check, decrement, FIFO notification, and unlock.
The caller's continuation is advanced separately by `SemStep`. -/
def semRelease (s : SemState) : Except LockError Unit × SemState :=
  if s.curr = 0 then (.error (.errorException "release count must match acquire count"), s)
  else
    match s.parked with
    | [] => (.ok (), { s with curr := s.curr - 1 })
    | t :: ts => (.ok (), { s with curr := s.curr - 1, parked := ts, woken := s.woken ++ [t] })

/-- Event operations, `base/lock.jl:708-757`, without cancellation. -/
inductive EventOp where
  | wait | notify | reset
  deriving DecidableEq

/-- `slow` distinguishes the first atomic read/swap from the locked recheck. -/
structure EventTask where
  id : Nat
  ops : List EventOp
  slow : Bool := false
  deriving DecidableEq

/-- `base/lock.jl:701-705`. Queue membership is the parked/relock PC.
`released` counts wait calls that returned or received a wake value;
`notifies` counts completed notify calls. These natural numbers are observation counters. -/
structure EventState where
  set : Bool := false
  ready : List EventTask := []
  parked : List EventTask := []
  woken : List EventTask := []
  released : Nat := 0
  notifies : Nat := 0
  deriving DecidableEq

def eventInitial (inputs : List (List EventOp)) : EventState :=
  { ready := inputs.zipIdx |>.map (fun (ops, id) => ⟨id, ops, false⟩) }

/-- One valid thread id's state, `base/lock.jl:765-768,973-1009`. -/
inductive OncePhase where
  | initial | concurrent | hasrun
  deriving DecidableEq

/-- Per-task PCs, including a yielding initializer and the non-yielding spin loop. -/
inductive OncePC where
  | enter | initializing (yieldsLeft : Nat) | spin | done
  deriving DecidableEq

structure OnceState where
  phase : OncePhase := .initial
  tasks : List OncePC
  current : Option Nat := none
  deriving DecidableEq

/-- `base/lock.jl:919-923,936-972`: one valid thread id starts uninitialized.
Array allocation and the brief PerThreadLock section have no cooperative yield. -/
def onceInitial (k : Nat) : OnceState := { tasks := List.replicate k .enter }

/-- `base/lock.jl:973-1013`. The current task keeps the thread until it yields
or finishes. `GC.safepoint()` in lines 978-983 does not yield to another task.
The initializer is a total function represented by a finite number of yields. -/
def onceStep (y choice : Nat) (s : OnceState) : OnceState :=
  let t := s.current.getD choice
  match s.tasks[t]? with
  | none => s
  | some .done => { s with current := none }
  | some .enter =>
    match s.phase with
    | .initial => { phase := .concurrent, tasks := s.tasks.set t (.initializing y), current := some t }
    | .concurrent => { s with tasks := s.tasks.set t .spin, current := some t }
    | .hasrun => { s with tasks := s.tasks.set t .done, current := none }
  | some (.initializing (n + 1)) =>
      { s with tasks := s.tasks.set t (.initializing n), current := none }
  | some (.initializing 0) =>
      { phase := .hasrun, tasks := s.tasks.set t .done, current := none }
  | some .spin =>
    match s.phase with
    | .concurrent => s
    | _ => { s with tasks := s.tasks.set t .done, current := none }

def onceRun (y : Nat) (schedule : Nat → Nat) : Nat → OnceState → OnceState
  | 0, s => s
  | n + 1, s => onceStep y (schedule n) (onceRun y schedule n s)



end JuliaLean.Channels
