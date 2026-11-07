import JuliaLean.Core

/-!
# Typed model of `base/locks-mt.jl`

Atomic loads, swaps, and stores take an explicit memory order and share the
caller's mutable world. Runtime calls may block or throw. No fairness or
interference restrictions are assumed. Padding bytes are uninitialized and
unobserved by the source methods.
-/
namespace JuliaLean.base.locks_mt
open JuliaLean
abbrev I := JInt .i64
def int (x : Int) : I := JInt.wrap .i64 x

inductive MemoryOrder where
  | plain | monotonic | acquire | release | acquireRelease | sequentiallyConsistent
  deriving DecidableEq, Repr

/-- Failure retains mutations; `none` is nontermination, including a blocked wait. -/
abbrev M (E W A : Type) := W → Option (Except (E × W) (A × W))

instance {E W : Type} : Monad (M E W) where
  pure value := fun world => some (.ok (value, world))
  bind action next := fun world => match action world with
    | none => none
    | some (.error error) => some (.error error)
    | some (.ok (value, world)) => next value world

instance {E W : Type} : MonadExceptOf E (M E W) where
  throw error := fun world => some (.error (error, world))
  tryCatch action handler := fun world => match action world with
    | none => none
    | some (.error (error, world)) => handler error world
    | some (.ok result) => some (.ok result)

def loop {E W S A : Type} (step : S → M E W (Sum A S)) (state : S) : M E W A :=
  fun world => match step state world with
    | none => none
    | some (.error error) => some (.error error)
    | some (.ok (.inl result, world)) => some (.ok (result, world))
    | some (.ok (.inr next, world)) => loop step next world
partial_fixpoint

def finallyDo {E W A : Type} (body : M E W A) (cleanup : M E W Unit) : M E W A := do
  let result : Except E A ← tryCatch (do pure (.ok (← body))) (fun e => pure (.error e))
  cleanup
  match result with
  | .ok value => pure value
  | .error error => throw error

def liftFrame {E W F A : Type} (action : M E W A) : M E (F × W) A :=
  fun (frame, world) => match action world with
    | none => none
    | some (.error (error, world)) => some (.error (error, (frame, world)))
    | some (.ok (value, world)) => some (.ok (value, (frame, world)))

def runFrame {E W F A : Type} (initial : F) (action : M E (F × W) A) : M E W A :=
  fun world => match action (initial, world) with
    | none => none
    | some (.error (error, (_, world))) => some (.error (error, world))
    | some (.ok (value, (_, world))) => some (.ok (value, world))

def getFrame {E W F : Type} : M E (F × W) F := fun state => some (.ok (state.1, state))
def setFrame {E W F : Type} (frame : F) : M E (F × W) Unit :=
  fun (_, world) => some (.ok ((), (frame, world)))

structure Runtime (E W Lock : Type) where
  newSpinLock : I → M E W Lock
  newPaddedSpinLock : M E W Lock
  loadOwned : MemoryOrder → Lock → M E W I
  swapOwned : MemoryOrder → Lock → I → M E W I
  storeOwned : MemoryOrder → Lock → I → M E W Unit
  disableFinalizers : M E W Unit
  enableFinalizers : M E W Unit
  cpuSuspend : M E W Unit
  gcSafepoint : M E W Unit
  cpuWake : M E W Unit
  error : String → E
  concurrencyViolation : M E W Unit

-- Source: base/locks-mt.jl:1-45 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- import .Base: lock, trylock, unlock, islocked, AbstractLock
-- 
-- export SpinLock
-- public PaddedSpinLock
-- # Important Note: these low-level primitives defined here
-- #   are typically not for general usage
-- 
-- ##########################################
-- # Atomic Locks
-- ##########################################
-- 
-- """
--     abstract type AbstractSpinLock <: AbstractLock end
-- 
-- A non-reentrant, test-and-test-and-set spin lock.
-- Recursive use will result in a deadlock.
-- This kind of lock should only be used around code that takes little time
-- to execute and does not block (e.g. perform I/O).
-- In general, [`ReentrantLock`](@ref) should be used instead.
-- 
-- Each [`lock`](@ref) must be matched with an [`unlock`](@ref).
-- If [`!islocked(lck::AbstractSpinLock)`](@ref islocked) holds, [`trylock(lck)`](@ref trylock)
-- succeeds unless there are other tasks attempting to hold the lock "at the same time."
-- 
-- Test-and-test-and-set spin locks are quickest up to about 30ish
-- contending threads. If you have more contention than that, different
-- synchronization approaches should be considered.
-- 
-- !!! compat "Julia 1.13"
--     This type requires at least Julia 1.13.
-- """
-- abstract type AbstractSpinLock <: AbstractLock end
-- 
-- """
--     SpinLock() <: AbstractSpinLock
-- 
-- Spinlocks are not padded, and so may suffer from false sharing.
-- See also [`PaddedSpinLock`](@ref).
-- 
-- See the documentation for [`AbstractSpinLock`](@ref) regarding correct usage.
-- """
-- mutable struct SpinLock <: AbstractSpinLock
--     @atomic owned::Int
-- /Source

-- Source: base/locks-mt.jl:47-69 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- end
-- 
-- # TODO: Determine the cache line size using e.g., CPUID. Meanwhile, this is correct for most
-- # processors.
-- const CACHE_LINE_SIZE = 64
-- 
-- """
--     PaddedSpinLock() <: AbstractSpinLock
-- 
-- PaddedSpinLocks are padded so that each is guaranteed to be on its own cache line, to avoid
-- false sharing.
-- See also [`SpinLock`](@ref).
-- 
-- See the documentation for [`AbstractSpinLock`](@ref) regarding correct usage.
-- 
-- !!! compat "Julia 1.13"
--     This type requires at least Julia 1.13.
-- """
-- mutable struct PaddedSpinLock <: AbstractSpinLock
--     # we make this much larger than necessary to minimize false-sharing
--     _padding_before::NTuple{max(0, CACHE_LINE_SIZE - sizeof(Int)), UInt8}
--     @atomic owned::Int
--     _padding_after::NTuple{max(0, CACHE_LINE_SIZE - sizeof(Int)), UInt8}
-- /Source

-- Source: base/locks-mt.jl:75-78 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- end
-- 
-- # Note: this cannot assert that the lock is held by the correct thread, because we do not
-- # track which thread locked it. Users beware.
-- /Source

-- Source: base/locks-mt.jl:80-80 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/locks-mt.jl:91-91 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/locks-mt.jl:103-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/locks-mt.jl:112-112 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

/--
Julia source: base/locks-mt.jl:46-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    SpinLock() = new(0)
```
-/
def SpinLock {E W L : Type} (r : Runtime E W L) : M E W L := r.newSpinLock (int 0)

/--
Julia source: base/locks-mt.jl:70-74 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function PaddedSpinLock()
        l = new()
        @atomic l.owned = 0
        return l
    end
```
-/
def PaddedSpinLock {E W L : Type} (r : Runtime E W L) : M E W L := do
  let l ← r.newPaddedSpinLock
  r.storeOwned .sequentiallyConsistent l (int 0)
  pure l

/--
Julia source: base/locks-mt.jl:113-115 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function islocked(l::AbstractSpinLock)
    return (@atomic :monotonic l.owned)::Int != 0
end
```
-/
def islocked {E W L : Type} (r : Runtime E W L) (l : L) : M E W Bool := do
  pure ((← r.loadOwned .monotonic l).val != 0)

/--
Julia source: base/locks-mt.jl:79-79 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.assert_havelock(l::AbstractSpinLock) = islocked(l) ? nothing : Base.concurrency_violation()
```
-/
def assertHaveLock {E W L : Type} (r : Runtime E W L) (l : L) : M E W Unit := do
  if ← islocked r l then pure () else r.concurrencyViolation

/--
Julia source: base/locks-mt.jl:92-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function trylock(l::AbstractSpinLock)
    if l.owned::Int == 0
        GC.disable_finalizers()
        p = (@atomicswap :acquire l.owned = 1)::Int
        if p == 0
            return true
        end
        GC.enable_finalizers()
    end
    return false
end
```
-/
def trylock {E W L : Type} (r : Runtime E W L) (l : L) : M E W Bool := do
  if (← r.loadOwned .plain l).val == 0 then
    r.disableFinalizers
    let previous ← r.swapOwned .acquire l (int 1)
    if previous.val == 0 then return true
    r.enableFinalizers
  pure false

/--
Julia source: base/locks-mt.jl:81-90 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function lock(l::AbstractSpinLock)
    while true
        if @inline trylock(l)
            return
        end
        ccall(:jl_cpu_suspend, Cvoid, ())
        # Temporary solution before we have gc transition support in codegen.
        ccall(:jl_gc_safepoint, Cvoid, ())
    end
end
```
-/
def lock {E W L : Type} (r : Runtime E W L) (l : L) : M E W Unit :=
  loop (fun (_ : Unit) => do
    if ← trylock r l then return .inl ()
    r.cpuSuspend
    r.gcSafepoint
    pure (.inr ())) ()

/--
Julia source: base/locks-mt.jl:104-111 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unlock(l::AbstractSpinLock)
    if (@atomicswap :release l.owned = 0)::Int == 0
        error("unlock count must match lock count")
    end
    GC.enable_finalizers()
    ccall(:jl_cpu_wake, Cvoid, ())
    return
end
```
-/
def unlock {E W L : Type} (r : Runtime E W L) (l : L) : M E W Unit := do
  if (← r.swapOwned .release l (int 0)).val == 0 then
    throw (r.error "unlock count must match lock count")
  r.enableFinalizers
  r.cpuWake


end JuliaLean.base.locks_mt

namespace JuliaLean.ConcurrencyCov

open JuliaLean

abbrev I64 := JInt .i64
abbrev U64 := JInt .u64
abbrev I32 := JInt .i32
abbrev I16 := JInt .i16
abbrev I8 := JInt .i8
abbrev U32 := JInt .u32
abbrev U8 := JInt .u8

def i64 (x : Int) : I64 := JInt.lit .i64 x
def i32 (x : Int) : I32 := JInt.lit .i32 x
def i8 (x : Int) : I8 := JInt.lit .i8 x
def u32 (x : Int) : U32 := JInt.lit .u32 x
def u64 (x : Int) : U64 := JInt.lit .u64 x

/-- Exceptions thrown by the modelled methods. -/
inductive Exn where
  | errorException (msg : String)
  | argumentError (msg : String)
  | inexactError
  | domainError
  | boundsError
  | methodError
  | concurrencyViolation
  | assertionError (msg : String)
  /-- `TypeError` of a failed type assertion. -/
  | typeError
  | undefVarError (name : String)
  /-- `InvalidStateException(msg, state)`. -/
  | invalidState (msg : String) (state : String)
  /-- `TaskFailedException(t)` for the task numbered `t`. -/
  | taskFailed (t : Nat)
  /-- `CompositeException` of `TaskFailedException`s of the listed tasks. -/
  | composite (ts : List Nat)
  /-- `CancellationRequest(sev)`. -/
  | cancellation (sev : Nat)
  /-- A user exception, e.g. thrown by a callback. -/
  | user (n : Nat)
  deriving DecidableEq, Repr, Inhabited

abbrev R (α : Type) := Except Exn α

/-- Outcome of user code: a value or a thrown exception. -/
abbrev Outcome := R Nat

/-- A per-task table with the entry of task `t` replaced by `v`. -/
def upd {β : Type} (f : Nat → β) (t : Nat) (v : β) : Nat → β := fun u => if u = t then v else f u
end JuliaLean.ConcurrencyCov

namespace JuliaLean.ConcurrencyCov.Locks

open JuliaLean.ConcurrencyCov

/-! ## Spin locks, `base/locks-mt.jl` -/

/-- `SpinLock` / `PaddedSpinLock`: the `owned` field and the per-task finalizer
counters. -/
structure Spin where
  owned : Int
  fin : Nat → Int

/-- `SpinLock()` (line 46) and `PaddedSpinLock()` (lines 70-74). -/
def spinLock : Spin := ⟨0, fun _ => 0⟩
def paddedSpinLock : Spin := ⟨0, fun _ => 0⟩

/-- `islocked(l)`, lines 113-115. -/
def spinIslocked (l : Spin) : Bool := l.owned ≠ 0

/-- `assert_havelock(l::AbstractSpinLock)`, line 79. -/
def spinAssertHavelock (l : Spin) : R Unit :=
  if spinIslocked l then .ok () else .error .concurrencyViolation

/-- `trylock(l)`, lines 92-102. -/
def spinTrylock (t : Nat) (l : Spin) : Bool × Spin :=
  if l.owned = 0 then
    let fin := upd l.fin t (l.fin t + 1)
    let p := l.owned
    if p = 0 then (true, { owned := 1, fin })
    else (false, { owned := 1, fin := upd fin t (fin t - 1) })
  else (false, l)

/-- `lock(l)`, lines 81-90: one pass of the loop; `none` keeps spinning. -/
def spinLockStep (t : Nat) (l : Spin) : Option Spin :=
  match spinTrylock t l with
  | (true, l) => some l
  | (false, _) => none

/-- `unlock(l)`, lines 104-111. -/
def spinUnlock (t : Nat) (l : Spin) : R Spin :=
  let p := l.owned
  let l := { l with owned := 0 }
  if p = 0 then .error (.errorException "unlock count must match lock count")
  else .ok { l with fin := upd l.fin t (l.fin t - 1) }

end JuliaLean.ConcurrencyCov.Locks

namespace JuliaLean.ConcurrencyCov.FaithfulSmall

open JuliaLean.ConcurrencyCov

def spinLockCtor : Locks.Spin := ⟨0, fun _ => 0⟩
def paddedSpinLockCtor : Locks.Spin :=
  let l : Locks.Spin := ⟨0, fun _ => 0⟩
  { l with owned := 0 }
def spinAssertHavelock (violation : R Unit) (l : Locks.Spin) : R Unit :=
  if Locks.spinIslocked l then .ok () else violation
inductive SpinLoopOp where | suspend | safepoint
  deriving DecidableEq, Repr

/-- Each list element is the lock state observed at the next loop iteration. -/
def spinLockLoop (task : Nat) : List Locks.Spin → Option (Locks.Spin × List SpinLoopOp)
  | [] => none
  | l :: rest =>
    match Locks.spinTrylock task l with
    | (true, acquired) => some (acquired, [])
    | (false, _) => (spinLockLoop task rest).map fun (acquired, ops) =>
        (acquired, [.suspend, .safepoint] ++ ops)
def spinTrylock (task : Nat) (l : Locks.Spin) : Bool × Locks.Spin :=
  if l.owned = 0 then
    let disabled := upd l.fin task (l.fin task + 1)
    let previous := l.owned
    let swapped : Locks.Spin := ⟨1, disabled⟩
    if previous = 0 then (true, swapped)
    else (false, { swapped with fin := upd swapped.fin task (swapped.fin task - 1) })
  else (false, l)
def spinUnlock (wake : Locks.Spin → Locks.Spin) (task : Nat) (l : Locks.Spin) : R Locks.Spin :=
  let previous := l.owned
  let released := { l with owned := 0 }
  if previous = 0 then .error (.errorException "unlock count must match lock count")
  else
    let enabled := { released with fin := upd released.fin task (released.fin task - 1) }
    .ok (wake enabled)
def spinIslocked (monotonicLoad : Int → Int) (l : Locks.Spin) : Bool :=
  monotonicLoad l.owned != 0
end JuliaLean.ConcurrencyCov.FaithfulSmall
