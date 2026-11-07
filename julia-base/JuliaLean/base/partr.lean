import JuliaLean.Core
import JuliaLean.base.io
import JuliaLean.base.int
import JuliaLean.base.file

/-!
# Model of `base/partr.jl`

The `Base.Partr` multiqueue task scheduler of Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`:
per-threadpool vectors of task min-heaps keyed by task priority, a thread-local linear
congruential RNG, insertion and deletion of the minimum. Heaps, the global `heaps` vector
and task priorities are references into the mutable world, read and written through typed
accessors that carry the source's atomic ordering; a `Vector` is the list of its slots
(`none` is an unassigned slot). Spin locks, the thread-local RNG state and the runtime's
thread and threadpool calls are typed parameters with no assumed laws. Integer arithmetic is
the installed `JuliaLean.base.int` model at Julia's types. Recursion and loops are fuel-free
(`partial_fixpoint`, `whileLoop`): `none` is divergence.
-/

namespace JuliaLean.base.partr

open JuliaLean
open JuliaLean.base.io (M Error whileLoop finallyDo liftJl)

abbrev I8 := JInt .i8
abbrev I16 := JInt .i16
abbrev I32 := JInt .i32
abbrev I64 := JInt .i64
abbrev U16 := JInt .u16
abbrev U32 := JInt .u32
abbrev U64 := JInt .u64

def add {t : IntTy} (x y : JInt t) : JInt t := JuliaLean.base.int.add x y
def sub {t : IntTy} (x y : JInt t) : JInt t := JuliaLean.base.int.sub x y
def mul {t : IntTy} (x y : JInt t) : JInt t := JuliaLean.base.int.mul x y
/-- `x % T` for an integer type `T`. -/
def remT {t : IntTy} (u : IntTy) (x : JInt t) : JInt u := JuliaLean.base.int.remT u x
/-- `T(x)`: `InexactError` when `x` does not fit `T`. -/
def convertTo {World : Type} (name : String) (u : IntTy) {t : IntTy} (x : JInt t) : M World (JInt u) :=
  liftJl (JInt.convert name u x.val)

/-- The memory ordering of an atomic field access; `plain` is a field access without one. -/
inductive Ordering where
  | plain
  | monotonic
  deriving DecidableEq, Repr

def undefRef : Error := .foreignError "UndefRefError" "access to undefined reference"

/-- `v[i]` on a `Vector` of references: `BoundsError` outside it, `UndefRefError` on an
unassigned slot. -/
def getSlot {World A : Type} (v : List (Option A)) (i : Int) : M World A :=
  if 1 ≤ i ∧ i ≤ v.length then
    match v[(i - 1).toNat]? with
    | some (some x) => pure x
    | _ => throw undefRef
  else throw (.jl .boundsError)

/-- `v[i] = x` on a `Vector` (`none` is `unsetindex!`): `BoundsError` outside it. -/
def setSlot {World A : Type} (v : List (Option A)) (i : Int) (x : Option A) : M World (List (Option A)) :=
  if 1 ≤ i ∧ i ≤ v.length then pure (v.set (i - 1).toNat x) else throw (.jl .boundsError)

/-- `v[i]` on a fully assigned `Vector`. -/
def getIndex {World A : Type} (v : List A) (i : Int) : M World A :=
  if 1 ≤ i ∧ i ≤ v.length then
    match v[(i - 1).toNat]? with
    | some x => pure x
    | none => throw (.jl .boundsError)
  else throw (.jl .boundsError)

/-- The fields of `taskheap` references `Heap` and the scheduler fields of tasks. -/
structure HeapFields (World Heap Task SpinLock : Type) where
  /-- `new(SpinLock(), Vector{Task}(undef, 256), zero(Int32), typemax(UInt16))`, given the
  new lock. -/
  new : SpinLock → List (Option Task) → I32 → U16 → M World Heap
  lock : Heap → M World SpinLock
  tasks : Heap → M World (List (Option Task))
  /-- Mutate the `tasks` vector in place (`setindex!`, `resize!`, `unsetindex!`). -/
  setTasks : Heap → List (Option Task) → M World Unit
  ntasks : Heap → Ordering → M World I32
  setNtasks : Heap → Ordering → I32 → M World Unit
  priority : Heap → Ordering → M World U16
  setPriority : Heap → Ordering → U16 → M World Unit
  taskPriority : Task → M World U16
  setTaskPriority : Task → U16 → M World Unit

/-- The runtime calls, spin locks and the module's global `heaps` and `heaps_lock`. -/
structure Runtime (World Heap Task SpinLock : Type) where
  newSpinLock : M World SpinLock
  lock : SpinLock → M World Unit
  trylock : SpinLock → M World Bool
  unlock : SpinLock → M World Unit
  /-- The global `heaps`, a `Vector` of two `Vector{taskheap}`s. -/
  heaps : M World (List (List Heap))
  /-- `heaps[tp] = v` (after its bounds check). -/
  setHeaps : List (List Heap) → M World Unit
  /-- The global `heaps_lock`. -/
  heapsLock : List SpinLock
  /-- `ccall(:jl_get_ptls_rng, UInt64, ())` and `ccall(:jl_set_ptls_rng, ...)`. -/
  getPtlsRng : M World U64
  setPtlsRng : U64 → M World Unit
  /-- `Threads._nthreads_in_pool(tpid)`. -/
  nthreadsInPool : I8 → M World I32
  getTaskThreadpoolid : Task → M World I8
  /-- `ccall(:jl_threadpoolid, Int8, (Int16,), tid)`. -/
  threadpoolid : I16 → M World I8
  threadid : M World I64
  setTaskTid : Task → I32 → M World I32
  getTaskTid : Task → M World I16
  wakeupThread : I16 → M World I32
  /-- `ccall(:SwitchToThread, ...)` on Windows, `ccall(:sched_yield, ...)` elsewhere. -/
  switchToThread : M World I32
  schedYield : M World I32
  iswindows : Bool
  safepoint : M World Unit

section
variable {World Heap Task SpinLock : Type}
variable (f : HeapFields World Heap Task SpinLock) (r : Runtime World Heap Task SpinLock)

def assertion (message : String) : Error := .foreignError "AssertionError" message

-- Reason: The module header and its `using` are load-time structure.
-- UNTRANSLATED
-- Source: base/partr.jl:1-6 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- module Partr
-- 
-- using ..Threads: SpinLock
-- 
-- /Source

/--
Julia source: base/partr.jl:7-15 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# a task minheap
mutable struct taskheap
    const lock::SpinLock
    const tasks::Vector{Task}
    @atomic ntasks::Int32
    @atomic priority::UInt16
    taskheap() = new(SpinLock(), Vector{Task}(undef, 256), zero(Int32), typemax(UInt16))
end

```
-/
def taskheapNew : M World Heap := do
  f.new (← r.newSpinLock) (List.replicate 256 none) (JInt.lit .i32 0) (JInt.lit .u16 0xffff)

/--
Julia source: base/partr.jl:16-21 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# multiqueue minheap state
const heap_d = UInt32(8)
const heaps = [Vector{taskheap}(undef, 0), Vector{taskheap}(undef, 0)]
const heaps_lock = [SpinLock(), SpinLock()]

```
-/
def heap_d : U32 := JInt.lit .u32 8

/--
Julia source: base/partr.jl:30-31 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
get_ptls_rng() = ccall(:jl_get_ptls_rng, UInt64, ())

```
-/
def get_ptls_rng : M World U64 := r.getPtlsRng

/--
Julia source: base/partr.jl:32-33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
set_ptls_rng(seed::UInt64) = ccall(:jl_set_ptls_rng, Cvoid, (UInt64,), seed)

```
-/
def set_ptls_rng (seed : U64) : M World Unit := r.setPtlsRng seed

/--
Julia source: base/partr.jl:47-76 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# This implementation is based on OpenSSL's implementation of rand_uniform
# https://github.com/openssl/openssl/blob/1d2cbd9b5a126189d5e9bc78a3bdb9709427d02b/crypto/rand/rand_uniform.c#L13-L99
# Comments are vendored from their implementation as well.
# For the original developer check the PR to swift https://github.com/apple/swift/pull/39143.

# Essentially it boils down to incrementally generating a fixed point
# number on the interval [0, 1) and multiplying this number by the upper
# range limit.  Once it is certain what the fractional part contributes to
# the integral part of the product, the algorithm has produced a definitive
# result.
"""
    rand_uniform_max_int32(max::UInt32, seed::UInt64)

Return a random UInt32 in the range `0:max-1` using the given seed.
Max must be greater than 0.
"""
Base.@assume_effects :total function rand_uniform_max_int32(max::UInt32, seed::UInt64)
    if max == UInt32(1)
        return UInt32(0), seed
    end
    # We are generating a fixed point number on the interval [0, 1).
    # Multiplying this by the range gives us a number on [0, upper).
    # The high word of the multiplication result represents the integral part
    # This is not completely unbiased as it's missing the fractional part of the original implementation but it's good enough for our purposes
    seed = UInt64(69069) *% seed +% UInt64(362437)
    prod = (UInt64(max)) * (seed % UInt32) # 64 bit product
    i = prod >> 32 % UInt32 # integral part
    return i % UInt32, seed
end

```
-/
def rand_uniform_max_int32 (max : U32) (seed : U64) : U32 × U64 :=
  if max.val == 1 then (JInt.lit .u32 0, seed)
  else
    let seed := add (mul (JInt.lit .u64 69069) seed) (JInt.lit .u64 362437)
    let prod := mul (JInt.wrap .u64 max.val) (JInt.wrap .u64 (remT .u32 seed).val)
    let i := remT .u32 (JuliaLean.base.int.shr_Int prod (JInt.lit .i64 32))
    (remT .u32 i, seed)

/--
Julia source: base/partr.jl:34-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    rand_ptls(max::UInt32)

Return a random UInt32 in the range `0:max-1` using the thread-local RNG
state. Max must be greater than 0.
"""
Base.@assume_effects :removable :inaccessiblememonly :notaskstate function rand_ptls(max::UInt32)
    rngseed = get_ptls_rng()
    val, seed = rand_uniform_max_int32(max, rngseed)
    set_ptls_rng(seed)
    return val % UInt32
end

```
-/
def rand_ptls (max : U32) : M World U32 := do
  let rngseed ← get_ptls_rng r
  let (val, seed) := rand_uniform_max_int32 max rngseed
  set_ptls_rng r seed
  return remT .u32 val

/--
Julia source: base/partr.jl:22-29 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

"""
    cong(max::UInt32)

Return a random UInt32 in the range `1:max` except if max is 0, in that case return 0.
"""
cong(max::UInt32) = iszero(max) ? UInt32(0) : rand_ptls(max) + UInt32(1) #TODO: make sure users don't use 0 and remove this check

```
-/
def cong (max : U32) : M World U32 := do
  if max.val == 0 then return JInt.lit .u32 0
  return add (← rand_ptls r max) (JInt.lit .u32 1)

/--
Julia source: base/partr.jl:77-92 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia


function multiq_sift_up(heap::taskheap, idx::Int32)
    while idx > Int32(1)
        parent = (idx - Int32(2)) ÷ heap_d + Int32(1)
        if heap.tasks[idx].priority < heap.tasks[parent].priority
            t = heap.tasks[parent]
            heap.tasks[parent] = heap.tasks[idx]
            heap.tasks[idx] = t
            idx = parent
        else
            break
        end
    end
end

```
-/
def multiq_sift_up (heap : Heap) (idx : I32) : M World Unit := do
  whileLoop (fun (idx : Int) => do
    if !(idx > 1) then return .inl ()
    -- `(idx - Int32(2)) ÷ heap_d + Int32(1)` computes in `UInt32`
    let parent := add (← liftJl (JuliaLean.base.int.div_BitUnsigned64
      (← convertTo "UInt32" .u32 (JInt.wrap .i64 (idx - 2))) heap_d)) (JInt.lit .u32 1)
    let tasks ← f.tasks heap
    let ti ← getSlot tasks idx
    let tp ← getSlot tasks parent.val
    if (← f.taskPriority ti).val < (← f.taskPriority tp).val then
      let t ← getSlot (← f.tasks heap) parent.val
      let x ← getSlot (← f.tasks heap) idx
      f.setTasks heap (← setSlot (← f.tasks heap) parent.val (some x))
      f.setTasks heap (← setSlot (← f.tasks heap) idx (some t))
      return .inr parent.val
    else return .inl ()) idx.val

/--
Julia source: base/partr.jl:93-109 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function multiq_sift_down(heap::taskheap, idx::Int32)
    if idx <= heap.ntasks
        for child = (heap_d * idx - heap_d + 2):(heap_d * idx + 1)
            child = Int(child)
            child > length(heap.tasks) && break
            if isassigned(heap.tasks, child) &&
                    heap.tasks[child].priority < heap.tasks[idx].priority
                t = heap.tasks[idx]
                heap.tasks[idx] = heap.tasks[child]
                heap.tasks[child] = t
                multiq_sift_down(heap, Int32(child))
            end
        end
    end
end

```
-/
def multiq_sift_down (heap : Heap) (idx : I32) : M World Unit := do
  if idx.val ≤ (← f.ntasks heap .plain).val then
    let idxU := JInt.wrap .u32 idx.val
    let lo := add (sub (mul heap_d idxU) heap_d) (JInt.lit .u32 2)
    let hi := add (mul heap_d idxU) (JInt.lit .u32 1)
    for child in (List.range (hi.val - lo.val + 1).toNat).map (fun (k : Nat) => lo.val + (k : Int)) do
      let tasks ← f.tasks heap
      if child > tasks.length then break
      let assigned := match tasks[(child - 1).toNat]? with
        | some (some _) => true
        | _ => false
      if assigned then
        let tc ← getSlot tasks child
        let ti ← getSlot tasks idx.val
        if (← f.taskPriority tc).val < (← f.taskPriority ti).val then
          let t ← getSlot (← f.tasks heap) idx.val
          let x ← getSlot (← f.tasks heap) child
          f.setTasks heap (← setSlot (← f.tasks heap) idx.val (some x))
          f.setTasks heap (← setSlot (← f.tasks heap) child (some t))
          multiq_sift_down heap (← convertTo "Int32" .i32 (JInt.wrap .i64 child))
partial_fixpoint

/-- `UInt32(Threads._nthreads_in_pool(tpid))`, raised to 1 for an empty pool. -/
def poolThreads (tpid : I8) : M World U32 := do
  let nt ← convertTo "UInt32" .u32 (← r.nthreadsInPool tpid)
  return if nt.val == 0 then JInt.lit .u32 1 else nt

/--
Julia source: base/partr.jl:110-151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function multiq_size(tpid::Int8)
    nt = UInt32(Threads._nthreads_in_pool(tpid))
    if nt == 0
        # A pool with no threads can still receive tasks (e.g. during
        # sysimage bootstrap); size the heaps so insertion can park them
        # instead of indexing an empty heap vector.
        nt = UInt32(1)
    end
    tp = tpid + 1
    tpheaps = heaps[tp]
    heap_c = UInt32(2)
    heap_p = UInt32(length(tpheaps))

    if heap_c * nt <= heap_p
        return heap_p
    end

    @lock heaps_lock[tp] begin
        # Re-read under the lock; growing from a stale copy would replace the
        # current heaps and orphan tasks concurrently inserted into them (#62144).
        tpheaps = heaps[tp]
        heap_p = UInt32(length(tpheaps))
        nt = UInt32(Threads._nthreads_in_pool(tpid))
        if nt == 0
            nt = UInt32(1)
        end
        if heap_c * nt <= heap_p
            return heap_p
        end

        heap_p += heap_c * nt
        newheaps = Vector{taskheap}(undef, heap_p)
        copyto!(newheaps, tpheaps)
        for i = (1 + length(tpheaps)):heap_p
            newheaps[i] = taskheap()
        end
        heaps[tp] = newheaps
    end

    return heap_p
end

```
-/
def multiq_size (tpid : I8) : M World U32 := do
  let nt ← poolThreads r tpid
  let tp := add tpid (JInt.lit .i8 1)
  let tpheaps ← getIndex (← r.heaps) tp.val
  let heap_c := JInt.lit .u32 2
  let heap_p ← convertTo "UInt32" .u32 (JInt.wrap .i64 tpheaps.length)
  if (mul heap_c nt).val ≤ heap_p.val then return heap_p
  let lock ← getIndex r.heapsLock tp.val
  r.lock lock
  finallyDo (do
    let tpheaps ← getIndex (← r.heaps) tp.val
    let heap_p ← convertTo "UInt32" .u32 (JInt.wrap .i64 tpheaps.length)
    let nt ← poolThreads r tpid
    if (mul heap_c nt).val ≤ heap_p.val then return heap_p
    let heap_p := add heap_p (mul heap_c nt)
    let mut newheaps := tpheaps
    for _i in List.range (heap_p.val - tpheaps.length).toNat do
      newheaps := newheaps ++ [← taskheapNew f r]
    let heaps ← r.heaps
    let _ ← getIndex heaps tp.val
    r.setHeaps (heaps.set (tp.val - 1).toNat newheaps)
    return heap_p) (r.unlock lock)

/--
Julia source: base/partr.jl:152-183 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function multiq_insert(task::Task, priority::UInt16)
    tpid = ccall(:jl_get_task_threadpoolid, Int8, (Any,), task)
    @assert tpid > -1 "invalid tpid"
    heap_p = multiq_size(tpid)
    tp = tpid + 1

    task.priority = priority

    rn = cong(heap_p)
    tpheaps = heaps[tp]
    while !trylock(tpheaps[rn].lock)
        rn = cong(heap_p)
    end

    heap = tpheaps[rn]
    if heap.ntasks >= length(heap.tasks)
        resize!(heap.tasks, length(heap.tasks) * 2)
    end

    ntasks = heap.ntasks + Int32(1)
    @atomic :monotonic heap.ntasks = ntasks
    heap.tasks[ntasks] = task
    multiq_sift_up(heap, ntasks)
    priority = heap.priority
    if task.priority < priority
        @atomic :monotonic heap.priority = task.priority
    end
    unlock(heap.lock)

    return true
end

```
-/
def multiq_insert (task : Task) (priority : U16) : M World Bool := do
  let tpid ← r.getTaskThreadpoolid task
  if !(tpid.val > -1) then throw (assertion "invalid tpid")
  let heap_p ← multiq_size f r tpid
  let tp := add tpid (JInt.lit .i8 1)
  f.setTaskPriority task priority
  let rn ← cong r heap_p
  let tpheaps ← getIndex (← r.heaps) tp.val
  let rn ← whileLoop (fun (rn : U32) => do
    if ← r.trylock (← f.lock (← getIndex tpheaps rn.val)) then return .inl rn
    return .inr (← cong r heap_p)) rn
  let heap ← getIndex tpheaps rn.val
  let tasks ← f.tasks heap
  if (← f.ntasks heap .plain).val ≥ tasks.length then
    f.setTasks heap (tasks ++ List.replicate tasks.length none)
  let ntasks := add (← f.ntasks heap .plain) (JInt.lit .i32 1)
  f.setNtasks heap .monotonic ntasks
  f.setTasks heap (← setSlot (← f.tasks heap) ntasks.val (some task))
  multiq_sift_up f heap ntasks
  let priority ← f.priority heap .plain
  if (← f.taskPriority task).val < priority.val then
    f.setPriority heap .monotonic (← f.taskPriority task)
  r.unlock (← f.lock heap)
  return true

/--
Julia source: base/partr.jl:184-185 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
yield_os_thread() = @static Sys.iswindows() ? ccall(:SwitchToThread, stdcall, Cint, ()) : ccall(:sched_yield, Cint, ())

```
-/
def yield_os_thread : M World I32 := if r.iswindows then r.switchToThread else r.schedYield

/-- `tid - 1` passed to a `ccall` argument of integer type `t`. -/
def tidArg (t : IntTy) (tid : I64) : M World (JInt t) :=
  convertTo (if t == .i16 then "Int16" else "Int32") t (sub tid (JInt.lit .i64 1))

/--
Julia source: base/partr.jl:186-256 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function multiq_deletemin()
    local rn1::UInt32
    local heap, task

    tid = Threads.threadid()
    tp = ccall(:jl_threadpoolid, Int8, (Int16,), tid-1) + 1
    if tp == 0 # Foreign thread
        return nothing
    end
    tpheaps = heaps[tp]

    while true
        GC.safepoint()
        heap_p = UInt32(length(tpheaps))
        for i = UInt32(0):heap_p
            if i == heap_p
                return nothing
            end
            rn1 = cong(heap_p)
            rn2 = cong(heap_p)
            prio1 = tpheaps[rn1].priority
            prio2 = tpheaps[rn2].priority
            if prio1 > prio2
                prio1 = prio2
                rn1 = rn2
            elseif prio1 == prio2 && prio1 == typemax(UInt16)
                continue
            end
            if trylock(tpheaps[rn1].lock)
                if prio1 == tpheaps[rn1].priority
                    break
                end
                unlock(tpheaps[rn1].lock)
            end
        end

        @assert @isdefined(rn1) "Assertion to tell the compiler about the definedness of this variable"

        heap = tpheaps[rn1]
        task = heap.tasks[1]
        if ccall(:jl_set_task_tid, Cint, (Any, Cint), task, tid-1) == 0
            # This task is sticky to a different thread, so we can't run it.
            # Wake that thread so it can come pick up its own work, then keep
            # looking for something we are allowed to run.
            task_tid = ccall(:jl_get_task_tid, Int16, (Any,), task)
            unlock(heap.lock)
            if task_tid != Int16(-1)
                ccall(:jl_wakeup_thread, Cint, (Int16,), task_tid)
            end
            # Keep polling (the owner may release the task without waking
            # anyone), but give up the CPU in case that thread needs it.
            yield_os_thread()
            continue
        end
        break
    end
    ntasks = heap.ntasks
    @atomic :monotonic heap.ntasks = ntasks - Int32(1)
    heap.tasks[1] = heap.tasks[ntasks]
    Base.unsetindex!(heap.tasks, Int(ntasks))
    prio1 = typemax(UInt16)
    if ntasks > 1
        multiq_sift_down(heap, Int32(1))
        prio1 = heap.tasks[1].priority
    end
    @atomic :monotonic heap.priority = prio1
    unlock(heap.lock)

    return task
end

```
-/
def multiq_deletemin : M World (Option Task) := do
  let tid ← r.threadid
  let tp := add (← r.threadpoolid (← tidArg .i16 tid)) (JInt.lit .i8 1)
  if tp.val == 0 then return none
  let tpheaps ← getIndex (← r.heaps) tp.val
  let found ← whileLoop (fun (_ : Unit) => do
    r.safepoint
    let heap_p ← convertTo "UInt32" .u32 (JInt.wrap .i64 tpheaps.length)
    let chosen ← whileLoop (fun (i : Int) => do
      if i == heap_p.val then return .inl none
      let mut rn1 ← cong r heap_p
      let rn2 ← cong r heap_p
      let mut prio1 ← f.priority (← getIndex tpheaps rn1.val) .plain
      let prio2 ← f.priority (← getIndex tpheaps rn2.val) .plain
      if prio1.val > prio2.val then
        prio1 := prio2
        rn1 := rn2
      else if prio1.val == prio2.val && prio1.val == 0xffff then
        return .inr (i + 1)
      let lock ← f.lock (← getIndex tpheaps rn1.val)
      if ← r.trylock lock then
        if prio1.val == (← f.priority (← getIndex tpheaps rn1.val) .plain).val then
          return .inl (some rn1)
        r.unlock (← f.lock (← getIndex tpheaps rn1.val))
      return .inr (i + 1)) 0
    match chosen with
    | none => return .inl none
    | some rn1 =>
      let heap ← getIndex tpheaps rn1.val
      let task ← getSlot (← f.tasks heap) 1
      if (← r.setTaskTid task (← tidArg .i32 tid)).val == 0 then
        let task_tid ← r.getTaskTid task
        r.unlock (← f.lock heap)
        if task_tid.val != -1 then
          let _ ← r.wakeupThread task_tid
        let _ ← yield_os_thread r
        return .inr ()
      return .inl (some (heap, task))) ()
  match found with
  | none => return none
  | some (heap, task) =>
    let ntasks ← f.ntasks heap .plain
    f.setNtasks heap .monotonic (sub ntasks (JInt.lit .i32 1))
    let last ← getSlot (← f.tasks heap) ntasks.val
    f.setTasks heap (← setSlot (← f.tasks heap) 1 (some last))
    f.setTasks heap (← setSlot (← f.tasks heap) ntasks.val none)
    let mut prio1 := JInt.lit .u16 0xffff
    if ntasks.val > 1 then
      multiq_sift_down f heap (JInt.lit .i32 1)
      prio1 ← f.taskPriority (← getSlot (← f.tasks heap) 1)
    f.setPriority heap .monotonic prio1
    r.unlock (← f.lock heap)
    return some task

/--
Julia source: base/partr.jl:257-270 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function multiq_check_empty()
    tid = Threads.threadid()
    tp = ccall(:jl_threadpoolid, Int8, (Int16,), tid-1) + 1
    if tp == 0 # Foreign thread
        return true
    end
    for i = UInt32(1):length(heaps[tp])
        if heaps[tp][i].ntasks != 0
            return false
        end
    end
    return true
end

```
-/
def multiq_check_empty : M World Bool := do
  let tid ← r.threadid
  let tp := add (← r.threadpoolid (← tidArg .i16 tid)) (JInt.lit .i8 1)
  if tp.val == 0 then return true
  let n := (← getIndex (← r.heaps) tp.val).length
  for i in (List.range n).map (fun (k : Nat) => (k : Int) + 1) do
    let heap ← getIndex (← getIndex (← r.heaps) tp.val) i
    if (← f.ntasks heap .plain).val != 0 then return false
  return true

end

-- Reason: The module end is load-time structure.
-- UNTRANSLATED
-- Source: base/partr.jl:271-271 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- end
-- /Source
end JuliaLean.base.partr


namespace JuliaLean.Tasks



/-! ## base/partr.jl:28-75, task-local RNG -/

def partrCong (maximum draw : Nat) : Nat := if maximum == 0 then 0 else draw % maximum + 1

def partrNextSeed (seed : Nat) : Nat :=
  (69069 * seed + 362437) % 2^64

def partrRandom (maximum seed : Nat) : Nat × Nat :=
  if maximum == 1 then (0, seed)
  else
    let next := partrNextSeed seed
    (((maximum * (next % 2^32)) / 2^32) % 2^32, next)

/-! ## base/partr.jl:8-269, heap and multiqueue branches -/

structure CoverageTaskHeap where
  tasks : List Nat := []
  priorities : List Nat := []
  advertised : Nat := 65535
  deriving Repr, DecidableEq

def taskHeap : CoverageTaskHeap := {}

def heapInsert (heap : CoverageTaskHeap) (task priority : Nat) : CoverageTaskHeap :=
  { tasks := heap.tasks ++ [task]
    priorities := heap.priorities ++ [priority]
    advertised := min heap.advertised priority }

def heapDeleteFirst (heap : CoverageTaskHeap) : Option Nat × CoverageTaskHeap :=
  match heap.tasks, heap.priorities with
  | [], _ => (none, heap)
  | task :: tasks, _ :: priorities =>
      (some task, ⟨tasks, priorities, priorities.foldl min 65535⟩)
  | _, [] => (none, heap)

def siftUpDecision (index child parent : Nat) : Bool × Nat :=
  if 1 < index && child < parent then (true, (index - 2) / 8 + 1) else (false, index)

def siftDownDecision (index child childPriority parentPriority : Nat) : Bool × Nat :=
  if child ≤ 8 * index + 1 && childPriority < parentPriority then (true, child)
  else (false, index)

end JuliaLean.Tasks
