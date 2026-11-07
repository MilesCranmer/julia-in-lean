import JuliaLean.Core
import JuliaLean.base.float
import JuliaLean.base.uuid
import JuliaLean.base.pkgid
import JuliaLean.base.util
import JuliaLean.base.int
import JuliaLean.base.show
import JuliaLean.base.runtime_internals

/-!
# Model of `base/precompilation.jl`

Typed model of the module `Base.Precompilation` at Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`
on a 64-bit platform. Each modelled method is a Lean definition whose docstring carries the
method's verbatim source; its body follows the Julia body call by call.

* `Dict` and `Set` values are an abstract dictionary type with the operations of `DictOps`;
  `Set{T}` is a `Dict{T,Nothing}`. Iteration order is the dictionary's own (`DictOps.keys`), so
  every loop over a dictionary visits keys in the order Julia does. Keys are compared with
  `isequal` (`BEq`). Vectors are lists, mutated by returning the updated list.
* Package identities are the `base/pkgid.jl` `PkgId`; names are UTF-8 bytes, like the messages
  built from them.
* Methods run in a monad `m` with the `PError` exceptions. Calls into later-loaded or
  runtime functions (`Base.in_sysimage`, `uuid5`, logging, printing) and methods of this file
  not yet translated are callees.
-/

namespace JuliaLean.base.precompilation
open JuliaLean
open JuliaLean.base.pkgid (PkgId)
open JuliaLean.base.uuid (UUID)

abbrev Bytes := List UInt8
abbrev JInt64 := JInt .i64
abbrev U8 := JInt .u8
def lit (s : String) : Bytes := s.toUTF8.toList

/-- Exceptions thrown by the modelled methods. -/
inductive PError where
  | keyError
  | boundsError
  | assertionError
  | typeError
  | methodError
  | inexactError
  /-- `error(msg)`: an `ErrorException`. -/
  | errorException (msg : Bytes)
  | interruptException
  | invalidStateException
  | eofError
  | argumentError
  | divideError
  /-- `Base.CancellationRequest`. -/
  | cancellationRequest
  | pkgPrecompileError (msg : Bytes)
  /-- An exception of another type thrown by a runtime callee: its type name and `showerror` text. -/
  | other (typeName msg : Bytes)
  deriving Repr, DecidableEq

/-- Julia's `Dict` over every key and value type (`Set{T}` is `Dict T Unit`). -/
structure DictOps (Dict : Type → Type → Type) where
  empty : {K V : Type} → Dict K V
  get : {K V : Type} → [BEq K] → Dict K V → K → Option V
  set : {K V : Type} → [BEq K] → Dict K V → K → V → Dict K V
  delete : {K V : Type} → [BEq K] → Dict K V → K → Dict K V
  /-- The keys in iteration order, each once. -/
  keys : {K V : Type} → Dict K V → List K

section dicts
variable {m : Type → Type} [Monad m] [MonadExceptOf PError m] {Dict : Type → Type → Type}

def throwP {α : Type} (e : PError) : m α := throwThe PError e

/-- `d[k]`. -/
def getindex {K V : Type} [BEq K] (D : DictOps Dict) (d : Dict K V) (k : K) : m V :=
  match D.get d k with
  | some v => pure v
  | none => throwP .keyError

def haskey {K V : Type} [BEq K] (D : DictOps Dict) (d : Dict K V) (k : K) : Bool := (D.get d k).isSome

/-- `get(f, d, k)`: the value, or `dflt`. -/
def getD {K V : Type} [BEq K] (D : DictOps Dict) (d : Dict K V) (k : K) (dflt : V) : V :=
  (D.get d k).getD dflt

/-- `push!(s, x)` of a `Set`. -/
def setPush {K : Type} [BEq K] (D : DictOps Dict) (s : Dict K Unit) (x : K) : Dict K Unit := D.set s x ()

/-- `x in s` of a `Set`. -/
def setIn {K : Type} [BEq K] (D : DictOps Dict) (s : Dict K Unit) (x : K) : Bool := haskey D s x

/-- `filter!(f, d)`: delete every key whose pair fails `f`. -/
def filterBang {K V : Type} [BEq K] (D : DictOps Dict) (f : K → V → Bool) (d : Dict K V) : Dict K V :=
  let bad := (D.keys d).filter fun k => match D.get d k with
    | some v => !f k v
    | none => false
  bad.foldl (fun d k => D.delete d k) d

/-- `filter(f, d)`: a new dictionary with the passing pairs, inserted in `d`'s iteration order. -/
def filterDict {K V : Type} [BEq K] (D : DictOps Dict) (f : K → V → Bool) (d : Dict K V) : Dict K V :=
  (D.keys d).foldl (fun df k => match D.get d k with
    | some v => if f k v then D.set df k v else df
    | none => df) D.empty

end dicts

/-- `PkgId(uuid, name)`: `nothing` for the zero `UUID`. -/
def mkPkgId (u : UUID) (name : Bytes) : PkgId :=
  ⟨if u.value.val = 0 then none else some u, name⟩

-- UNTRANSLATED
-- the `module` header and `using` imports: no method (the `Config`/`PkgConfig` aliases are defined as `Config`/`PkgConfig` with the session types)
-- Source: base/precompilation.jl:1-8 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- module Precompilation
-- 
-- using Base: CoreLogging, PkgId, UUID, SHA1, StaleCacheKey, parsed_toml,
--             project_file_manifest_path, get_deps, preferences_names,
--             base_project, isdefined
-- 
-- const Config = Pair{Cmd, Base.CacheFlags}
-- const PkgConfig = Tuple{PkgId,Config}
-- /Source

/--
Julia source: base/precompilation.jl:9-29 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# --- Precompile jobserver (JuliaLang/julia#58591) ----------------------------
# A token pool of size `ntokens` shared with worker subprocesses that caps total
# CPU threads across all parallel workers: each holds one baseline token while
# CPU-active and its AOT imaging phase draws extra codegen threads from the same
# pool. Only one pool exists per process; a concurrent session (e.g. from package
# loading) whose create fails joins the existing pool instead, holding baselines
# against it without tearing it down. Returns:
#   :created -- created and owns the pool (must tear it down)
#   :joined  -- sharing a pool another session in this process owns
#   :none    -- no pool available; run uncoordinated
function setup_precompile_jobserver!(ntokens::Int)
    namep = ccall(:jl_precompile_jobserver_create, Ptr{UInt8}, (Cint,), ntokens)
    if namep != C_NULL
        ENV["JULIA_PRECOMPILE_JOBSERVER"] = unsafe_string(namep)
        return :created
    end
    # create failed: join an existing pool, else run uncoordinated (OS refused it)
    ccall(:jl_precompile_jobserver_active, Cint, ()) != 0 ? :joined : :none
end

```
-/
/-
The result of `setup_precompile_jobserver!`.
-/
inductive JobserverSetup where
  | created
  | joined
  | none
  deriving Repr, DecidableEq

/-- The runtime calls of the jobserver (`jl_precompile_jobserver_*`), and `ENV` writes. -/
structure JobserverOps (m : Type → Type) (P : Type) where
  /-- `ccall(:jl_precompile_jobserver_create, Ptr{UInt8}, (Cint,), ntokens)`. -/
  create : JInt .i32 → m P
  isNull : P → Bool
  unsafe_string : P → m Bytes
  /-- `ccall(:jl_precompile_jobserver_active, Cint, ())`. -/
  active : m (JInt .i32)
  /-- `ccall(:jl_precompile_jobserver_destroy, Cvoid, ())`. -/
  destroy : m Unit
  /-- `ccall(:jl_precompile_jobserver_acquire, Cint, ())`. -/
  acquire : m (JInt .i32)
  /-- `ccall(:jl_precompile_jobserver_release, Cvoid, ())`. -/
  release : m Unit
  setENV : Bytes → Bytes → m Unit
  deleteENV : Bytes → m Unit

/-- `setup_precompile_jobserver!(ntokens)`; `Cint(ntokens)` throws `InexactError` outside the
`Int32` range. -/
def setup_precompile_jobserver {m : Type → Type} [Monad m] [MonadExceptOf PError m] {P : Type}
    (j : JobserverOps m P) (ntokens : JInt .i64) : m JobserverSetup := do
  if ntokens.val < IntTy.min .i32 || ntokens.val > IntTy.max .i32 then throwP .inexactError
  let namep ← j.create (JInt.wrap .i32 ntokens.val)
  if !j.isNull namep then
    j.setENV (lit "JULIA_PRECOMPILE_JOBSERVER") (← j.unsafe_string namep)
    return .created
  -- create failed: join an existing pool, else run uncoordinated (OS refused it)
  return if (← j.active).val != 0 then .joined else .none

/--
Julia source: base/precompilation.jl:30-35 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function teardown_precompile_jobserver!()
    ccall(:jl_precompile_jobserver_destroy, Cvoid, ())
    delete!(ENV, "JULIA_PRECOMPILE_JOBSERVER")
    return nothing
end

```
-/
def teardown_precompile_jobserver {m : Type → Type} [Monad m] {P : Type} (j : JobserverOps m P) : m Unit := do
  j.destroy
  j.deleteENV (lit "JULIA_PRECOMPILE_JOBSERVER")
  return ()

/--
Julia source: base/precompilation.jl:36-63 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Bounds concurrently CPU-active workers. The `Base.Semaphore` enforces the
# process-count cap; when the jobserver is active each worker also holds one
# baseline token from the shared pool while CPU-active, balancing worker
# baselines and imaging codegen threads against one budget. A worker's main
# thread sleeps during imaging, so its baseline token doubles as that phase's
# first codegen thread.
#
# Baseline acquisition is best-effort: it proceeds tokenless when the pool is
# torn down, cancelled, or starved past a timeout (tokens leak if a worker is
# killed mid-imaging), degrading to bounded oversubscription instead of hanging.
# `ntokens` tracks tokens actually held, so releases only post back while it is
# positive and tokenless acquires can never over-post.
#
# Slots are handed out by priority rather than in request order: a package that a
# long chain of other packages is waiting on starts before one nothing depends on,
# so the environment's critical path is not delayed behind leaves that happened to
# become ready first.
mutable struct WorkerLimiter
    const cond::Threads.Condition   # guards `active`, `seq` and `waiting`
    const max::Int
    const jobserver::Bool
    active::Int
    seq::Int
    const waiting::Vector{Tuple{Float64,Int}} # (priority, -request order) of tasks waiting for a slot
    @atomic ntokens::Int
end
WorkerLimiter(max::Int, jobserver::Bool) =
    WorkerLimiter(Threads.Condition(), max, jobserver, 0, 0, Tuple{Float64,Int}[], 0)
```
-/
/-
`WorkerLimiter`: the immutable fields are values; the mutable `active`, `seq`, the contents of
`waiting` and the atomic `ntokens` are read and written through `LimiterOps`, and `cond` is the
lock and condition those operations use.
-/
structure WorkerLimiter (Cond : Type) where
  cond : Cond
  max : JInt .i64
  jobserver : Bool

/-- A waiting-list key `(priority, -request order)`. -/
abbrev Key := JuliaLean.base.float.FV .f64 × JInt .i64

/-- The mutable state of a `WorkerLimiter`, the `Threads.Condition` operations on `cond`, and the
comparisons on keys. -/
structure LimiterOps (m : Type → Type) (Cond : Type) where
  /-- `@lock cond body`. -/
  withLock : {α : Type} → Cond → m α → m α
  /-- `wait(cond)`, which releases the lock until notified. -/
  wait : Cond → m Unit
  notify : Cond → m Unit
  getActive : m (JInt .i64)
  setActive : JInt .i64 → m Unit
  getSeq : m (JInt .i64)
  setSeq : JInt .i64 → m Unit
  getWaiting : m (List Key)
  setWaiting : List Key → m Unit
  /-- `@atomic w.ntokens`. -/
  loadNtokens : m (JInt .i64)
  /-- `@atomic w.ntokens += 1`. -/
  incNtokens : m Unit
  /-- `@atomicreplace w.ntokens old => new`: whether it succeeded. -/
  casNtokens : JInt .i64 → JInt .i64 → m Bool
  /-- `maximum(w.waiting)` (`base/reduce.jl`) over tuple keys. -/
  maximum : List Key → m Key
  /-- `==` on keys (`Float64` `==` and `Int` `==`). -/
  keyEq : Key → Key → Bool

/-- `WorkerLimiter(max, jobserver)`, given the new `Threads.Condition()`; its mutable state starts at
`active = 0`, `seq = 0`, `waiting = []`, `ntokens = 0`. -/
def WorkerLimiter.new {Cond : Type} (cond : Cond) (max : JInt .i64) (jobserver : Bool) : WorkerLimiter Cond :=
  ⟨cond, max, jobserver⟩

/--
Julia source: base/precompilation.jl:64-68 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# How long an acquire keeps polling for a baseline token before proceeding
# without one. Generous enough that it is only ever hit when the pool has been
# starved abnormally (leaked tokens), not during routine imaging contention.
const JOBSERVER_BASELINE_TIMEOUT_S = 240.0
```
-/
def JOBSERVER_BASELINE_TIMEOUT_S : JuliaLean.base.float.FV .f64 := JuliaLean.Promotion.Fl.ofBits 0x406E000000000000

/--
Julia source: base/precompilation.jl:69-99 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# Try to take one baseline token from the shared pool, with a yielding backoff
# so the task scheduler keeps running while the pool is drained by imaging
# workers. Returns whether a token was acquired; bails out tokenless when the
# jobserver reports inactive (torn down), `cancel` returns true, or the timeout
# expires.
function _jobserver_acquire_baseline(w::WorkerLimiter; cancel=Returns(false))
    delay = 0.005
    # time_ns is monotonic, unlike time(); UInt64 subtraction is wrap-safe
    start_ns = time_ns()
    timeout_ns = round(UInt64, JOBSERVER_BASELINE_TIMEOUT_S * 1e9)
    while true
        r = ccall(:jl_precompile_jobserver_acquire, Cint, ())
        if r == 1
            @atomic w.ntokens += 1
            return true
        end
        if r == -1 || cancel()
            return false
        end
        if (time_ns() -% start_ns) >= timeout_ns
            @debug "Precompilation jobserver baseline token unavailable for $(JOBSERVER_BASELINE_TIMEOUT_S)s; proceeding without one"
            return false
        end
        Base.sleep(delay)
        delay = min(2 * delay, 0.1)
    end
end

function _jobserver_release_baseline(w::WorkerLimiter)
    while true
```
-/
/- Runtime callees of `_jobserver_acquire_baseline`. -/
structure BaselineOps (m : Type → Type) where
  time_ns : m (JInt .u64)
  sleep : JuliaLean.base.float.FV .f64 → m Unit
  /-- `round(UInt64, x)`. -/
  roundUInt64 : JuliaLean.base.float.FV .f64 → m (JInt .u64)
  /-- `min(x::Float64, y::Float64)` (`base/math.jl`). -/
  minFloat64 : JuliaLean.base.float.FV .f64 → JuliaLean.base.float.FV .f64 → JuliaLean.base.float.FV .f64
  /-- `@debug "Precompilation jobserver baseline token unavailable for ...; proceeding without one"`. -/
  debugTimeout : m Unit

/-- The `while true` loop of `_jobserver_acquire_baseline`. -/
def jobserver_acquire_loop {m : Type → Type} [Monad m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    {P Cond : Type} (j : JobserverOps m P) (l : LimiterOps m Cond) (b : BaselineOps m) (cancel : m Bool)
    (start_ns timeout_ns : JInt .u64) (delay : JuliaLean.base.float.FV .f64) : m Bool := do
  let r ← j.acquire
  if r.val == 1 then
    l.incNtokens
    return true
  if r.val == -1 || (← cancel) then
    return false
  -- `-%` is wrapping subtraction
  if (JInt.wrap .u64 ((← b.time_ns).val - start_ns.val)).val ≥ timeout_ns.val then
    b.debugTimeout
    return false
  b.sleep delay
  let two : JuliaLean.base.float.FV .f64 := JuliaLean.Promotion.Fl.ofBits 0x4000000000000000
  let tenth : JuliaLean.base.float.FV .f64 := JuliaLean.Promotion.Fl.ofBits 0x3FB999999999999A
  jobserver_acquire_loop j l b cancel start_ns timeout_ns
    (b.minFloat64 (JuliaLean.base.float.mul_float two delay) tenth)
partial_fixpoint

/-- `_jobserver_acquire_baseline(w; cancel)`. -/
def _jobserver_acquire_baseline {m : Type → Type} [Monad m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    {P Cond : Type} (j : JobserverOps m P) (l : LimiterOps m Cond) (b : BaselineOps m) (cancel : m Bool) : m Bool := do
  let delay : JuliaLean.base.float.FV .f64 := JuliaLean.Promotion.Fl.ofBits 0x3F747AE147AE147B -- 0.005
  -- time_ns is monotonic, unlike time(); UInt64 subtraction is wrap-safe
  let start_ns ← b.time_ns
  let e9 : JuliaLean.base.float.FV .f64 := JuliaLean.Promotion.Fl.ofBits 0x41CDCD6500000000
  let timeout_ns ← b.roundUInt64 (JuliaLean.base.float.mul_float JOBSERVER_BASELINE_TIMEOUT_S e9)
  jobserver_acquire_loop j l b cancel start_ns timeout_ns delay

/--
Julia source: base/precompilation.jl:100-112 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        old = @atomic w.ntokens
        old == 0 && return false
        (; success) = @atomicreplace w.ntokens old => old - 1
        if success
            ccall(:jl_precompile_jobserver_release, Cvoid, ())
            return true
        end
    end
end

function _acquire_slot(w::WorkerLimiter, priority::Float64)
    @lock w.cond begin
        key = (priority, -(w.seq += 1))
```
-/
def _jobserver_release_baseline {m : Type → Type} [Monad m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    {P Cond : Type} (j : JobserverOps m P) (l : LimiterOps m Cond) : m Bool := do
  let old ← l.loadNtokens
  if old.val == 0 then return false
  let success ← l.casNtokens old (JInt.wrap .i64 (old.val - 1))
  if success then
    j.release
    return true
  _jobserver_release_baseline j l
partial_fixpoint

/--
Julia source: base/precompilation.jl:113-126 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        push!(w.waiting, key)
        # admitted when a slot is free and no waiter outranks us
        while w.active >= w.max || maximum(w.waiting) != key
            wait(w.cond)
        end
        deleteat!(w.waiting, findfirst(==(key), w.waiting)::Int)
        w.active += 1
    end
    return nothing
end

function _release_slot(w::WorkerLimiter)
    @lock w.cond begin
        w.active -= 1
```
-/
/- The `while w.active >= w.max || maximum(w.waiting) != key` loop. -/
def acquire_slot_wait {m : Type → Type} [Monad m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    {Cond : Type} (l : LimiterOps m Cond) (w : WorkerLimiter Cond) (key : Key) : m Unit := do
  if (← l.getActive).val ≥ w.max.val || !l.keyEq (← l.maximum (← l.getWaiting)) key then
    l.wait w.cond
    acquire_slot_wait l w key
  else pure ()
partial_fixpoint

def _acquire_slot {m : Type → Type} [Monad m] [MonadExceptOf PError m] [∀ α, Lean.Order.CCPO (m α)]
    [Lean.Order.MonoBind m] {Cond : Type} (l : LimiterOps m Cond) (w : WorkerLimiter Cond)
    (priority : JuliaLean.base.float.FV .f64) : m Unit := do
  l.withLock w.cond do
    let seq := JInt.wrap .i64 ((← l.getSeq).val + 1)
    l.setSeq seq
    let key : Key := (priority, JInt.wrap .i64 (-seq.val))
    l.setWaiting ((← l.getWaiting) ++ [key])
    -- admitted when a slot is free and no waiter outranks us
    acquire_slot_wait l w key
    let waiting ← l.getWaiting
    -- `findfirst(==(key), w.waiting)::Int`
    match waiting.findIdx? (l.keyEq · key) with
    | none => throwP .typeError
    | some i => l.setWaiting (waiting.eraseIdx i)
    l.setActive (JInt.wrap .i64 ((← l.getActive).val + 1))
  return ()

/--
Julia source: base/precompilation.jl:127-134 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        notify(w.cond)
    end
    return nothing
end

function Base.acquire(w::WorkerLimiter; priority::Float64=0.0, cancel=Returns(false))
    _acquire_slot(w, priority)
    if w.jobserver
```
-/
def _release_slot {m : Type → Type} [Monad m] {Cond : Type} (l : LimiterOps m Cond) (w : WorkerLimiter Cond) :
    m Unit := do
  l.withLock w.cond do
    l.setActive (JInt.wrap .i64 ((← l.getActive).val - 1))
    l.notify w.cond
  return ()

/--
Julia source: base/precompilation.jl:135-147 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        try
            _jobserver_acquire_baseline(w; cancel)
        catch
            _release_slot(w)
            rethrow()
        end
    end
    return nothing
end

function Base.release(w::WorkerLimiter)
    w.jobserver && _jobserver_release_baseline(w)
    _release_slot(w)
```
-/
/- `Base.acquire(w; priority, cancel)`. -/
def acquire {m : Type → Type} [Monad m] [MonadExceptOf PError m] [∀ α, Lean.Order.CCPO (m α)]
    [Lean.Order.MonoBind m] {P Cond : Type} (j : JobserverOps m P) (l : LimiterOps m Cond) (b : BaselineOps m)
    (w : WorkerLimiter Cond) (priority : JuliaLean.base.float.FV .f64) (cancel : m Bool) : m Unit := do
  _acquire_slot l w priority
  if w.jobserver then
    tryCatchThe PError (discard (_jobserver_acquire_baseline j l b cancel)) fun e => do
      _release_slot l w
      throwThe PError e
  return ()

/--
Julia source: base/precompilation.jl:148-153 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    return nothing
end

function Base.acquire(f, w::WorkerLimiter; priority::Float64=0.0, cancel=Returns(false))
    Base.acquire(w; priority, cancel)
    try
```
-/
def release {m : Type → Type} [Monad m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] {P Cond : Type}
    (j : JobserverOps m P) (l : LimiterOps m Cond) (w : WorkerLimiter Cond) : m Unit := do
  if w.jobserver then discard (_jobserver_release_baseline j l)
  _release_slot l w
  return ()

/--
Julia source: base/precompilation.jl:154-159 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        return f()
    finally
        Base.release(w)
    end
end

```
-/
/- `Base.acquire(f, w; priority, cancel)`. -/
def acquire_f {m : Type → Type} [Monad m] [MonadExceptOf PError m] [MonadFinally m] [∀ α, Lean.Order.CCPO (m α)]
    [Lean.Order.MonoBind m] {P Cond α : Type} (j : JobserverOps m P) (l : LimiterOps m Cond) (b : BaselineOps m)
    (f : m α) (w : WorkerLimiter Cond) (priority : JuliaLean.base.float.FV .f64) (cancel : m Bool) : m α := do
  acquire j l b w priority cancel
  tryFinally f (release j l w)

/--
Julia source: base/precompilation.jl:160-171 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
## PrecompileJob

# Per-package compilation status and associated state.
@enum JobStatus::UInt8 begin
    JOB_PENDING      # not yet started
    JOB_STARTED      # compilation in progress
    JOB_RECOMPILED   # successfully compiled
    JOB_SOFT_ERROR   # compilecache returned an Exception (may work after restart)
    JOB_FAILED       # hard compile error
    JOB_DEP_FAILED   # not attempted because a dependency failed to precompile
end

```
-/
/- `@enum JobStatus::UInt8`. -/
inductive JobStatus where
  | JOB_PENDING
  | JOB_STARTED
  | JOB_RECOMPILED
  | JOB_SOFT_ERROR
  | JOB_FAILED
  | JOB_DEP_FAILED
  deriving Repr, DecidableEq
/--
Base `Enums.jl:17`; macro expansion is `Enums.jl:218-237`.
Julia source: base/precompilation.jl:163-163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum JobStatus::UInt8 begin
```
-/
def jobStatusBaseType : IntTy := .u8

/--
Base `Enums.jl:221-224`; `membershiptest` is `Enums.jl:79-87`; macro expansion is `Enums.jl:218-237`.
Julia source: base/precompilation.jl:163-163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum JobStatus::UInt8 begin
```
-/
def jobStatusFromInteger {I : Type}
    (atLeastZero : U8 → I → Bool) (atMostFive : I → U8 → Bool)
    (convert : I → Except PError U8) (showInteger : I → String) (x : I) :
    Except PError JobStatus :=
  if !atLeastZero (JInt.lit .u8 0) x then
    .error (.other (lit "ArgumentError")
      (lit ("invalid value for Enum JobStatus: " ++ showInteger x)))
  else if !atMostFive x (JInt.lit .u8 5) then
    .error (.other (lit "ArgumentError")
      (lit ("invalid value for Enum JobStatus: " ++ showInteger x)))
  else do
    let code ← convert x
    match code.val with
    | 0 => pure .JOB_PENDING
    | 1 => pure .JOB_STARTED
    | 2 => pure .JOB_RECOMPILED
    | 3 => pure .JOB_SOFT_ERROR
    | 4 => pure .JOB_FAILED
    | 5 => pure .JOB_DEP_FAILED
    | _ => .error (.other (lit "ArgumentError")
        (lit ("invalid value for Enum JobStatus: " ++ showInteger x)))

/--
Base `Enums.jl:19`; macro expansion is `Enums.jl:218-237`.
Julia source: base/precompilation.jl:163-163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum JobStatus::UInt8 begin
```
-/
def jobStatusInteger : JobStatus → U8
  | .JOB_PENDING => JInt.lit .u8 0
  | .JOB_STARTED => JInt.lit .u8 1
  | .JOB_RECOMPILED => JInt.lit .u8 2
  | .JOB_SOFT_ERROR => JInt.lit .u8 3
  | .JOB_FAILED => JInt.lit .u8 4
  | .JOB_DEP_FAILED => JInt.lit .u8 5

/--
Base `Enums.jl:19`; macro expansion is `Enums.jl:218-237`.
Julia source: base/precompilation.jl:163-163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum JobStatus::UInt8 begin
```
-/
def jobStatusConvert {Target : Type} (convert : U8 → Except PError Target)
    (x : JobStatus) : Except PError Target :=
  convert (jobStatusInteger x)

/--
Base `Enums.jl:20`; macro expansion is `Enums.jl:218-237`.
Julia source: base/precompilation.jl:163-163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum JobStatus::UInt8 begin
```
-/
def jobStatusCconvert {M : Type → Type} {A : Type}
    (convert : U8 → M A) (x : JobStatus) : M A :=
  convert (jobStatusInteger x)

/--
Base `Enums.jl:21`; macro expansion is `Enums.jl:218-237`.
Julia source: base/precompilation.jl:163-163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum JobStatus::UInt8 begin
```
-/
def jobStatusWrite {Io Result : Type} {M : Type → Type}
    (writeInteger : Io → U8 → M Result) (io : Io) (x : JobStatus) : M Result :=
  writeInteger io (jobStatusInteger x)

/--
Base `Enums.jl:22`; macro expansion is `Enums.jl:218-237`.
Julia source: base/precompilation.jl:163-163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum JobStatus::UInt8 begin
```
-/
def jobStatusRead {Io : Type} {M : Type → Type} [Monad M]
    (readInteger : Io → M U8) (construct : U8 → M JobStatus) (io : Io) : M JobStatus := do
  let code ← readInteger io
  construct code

/--
Base `Enums.jl:32`; macro expansion is `Enums.jl:218-237`.
Julia source: base/precompilation.jl:163-163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum JobStatus::UInt8 begin
```
-/
def jobStatusIsless (x y : JobStatus) : Bool :=
  JuliaLean.base.int.ltSame (jobStatusInteger x) (jobStatusInteger y)

/--
Base `Enums.jl:30, 233-237`; macro expansion is `Enums.jl:218-237`.
Julia source: base/precompilation.jl:163-163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum JobStatus::UInt8 begin
```
-/
def jobStatusEnumHash (typeHash : JInt .u64)
    (hashInteger : U8 → JInt .u64 → JInt .u64)
    (hashUInt : JInt .u64 → JInt .u64 → JInt .u64)
    (x : JobStatus) (h : JInt .u64) : JInt .u64 :=
  hashUInt typeHash (hashInteger (jobStatusInteger x) h)

/--
Base `Enums.jl:225`; macro expansion is `Enums.jl:218-237`.
Julia source: base/precompilation.jl:163-163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum JobStatus::UInt8 begin
```
-/
def jobStatusNameMap : List (U8 × String) :=
  [(JInt.lit .u8 0, "JOB_PENDING"), (JInt.lit .u8 1, "JOB_STARTED"),
   (JInt.lit .u8 2, "JOB_RECOMPILED"), (JInt.lit .u8 3, "JOB_SOFT_ERROR"),
   (JInt.lit .u8 4, "JOB_FAILED"), (JInt.lit .u8 5, "JOB_DEP_FAILED")]

/--
Base `Enums.jl:226`; macro expansion is `Enums.jl:218-237`.
Julia source: base/precompilation.jl:163-163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum JobStatus::UInt8 begin
```
-/
def jobStatusTypemin : JobStatus := .JOB_PENDING

/--
Base `Enums.jl:227`; macro expansion is `Enums.jl:218-237`.
Julia source: base/precompilation.jl:163-163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum JobStatus::UInt8 begin
```
-/
def jobStatusTypemax : JobStatus := .JOB_DEP_FAILED

/--
Base `Enums.jl:235-237`; macro expansion is `Enums.jl:218-237`.
Julia source: base/precompilation.jl:163-163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum JobStatus::UInt8 begin
```
-/
def jobStatusInstances : List JobStatus :=
  [.JOB_PENDING, .JOB_STARTED, .JOB_RECOMPILED, .JOB_SOFT_ERROR, .JOB_FAILED, .JOB_DEP_FAILED]

/--
Base `Enums.jl:34`; macro expansion is `Enums.jl:218-237`.
Julia source: base/precompilation.jl:163-163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum JobStatus::UInt8 begin
```
-/
def jobStatusSymbol (x : JobStatus) : String :=
  match x with
  | .JOB_PENDING => "JOB_PENDING"
  | .JOB_STARTED => "JOB_STARTED"
  | .JOB_RECOMPILED => "JOB_RECOMPILED"
  | .JOB_SOFT_ERROR => "JOB_SOFT_ERROR"
  | .JOB_FAILED => "JOB_FAILED"
  | .JOB_DEP_FAILED => "JOB_DEP_FAILED"

/--
Base `Enums.jl:36-40`; macro expansion is `Enums.jl:218-237`.
Julia source: base/precompilation.jl:163-163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum JobStatus::UInt8 begin
```
-/
def jobStatusInternalSymbol (code : U8) : String :=
  match jobStatusNameMap.find? (fun (value, _) => value.val == code.val) with
  | some (_, name) => name
  | none => "<invalid #" ++ toString code.val ++ ">"

/--
Base `Enums.jl:42`; macro expansion is `Enums.jl:218-237`.
Julia source: base/precompilation.jl:163-163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum JobStatus::UInt8 begin
```
-/
def jobStatusPrint {m : Type → Type} [Monad m] {Io V : Type}
    (p : JuliaLean.base.show.IOPrims m Io V)
    (io : JuliaLean.base.show.JIO Io V) (x : JobStatus) : m Unit :=
  JuliaLean.base.show.print_Symbol p io (jobStatusSymbol x)

/--
Base `Enums.jl:44-55`; macro expansion is `Enums.jl:218-237`.
Julia source: base/precompilation.jl:163-163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum JobStatus::UInt8 begin
```
-/
def jobStatusShow {m : Type → Type} {Io V Ty Mod : Type} [Monad m]
    [MonadExceptOf JuliaLean.base.show.ShowError m]
    (p : JuliaLean.base.show.IOPrims m Io V) (a : JuliaLean.base.show.AnyOps V Ty)
    (moduleOfValue : V → Except JuliaLean.base.show.ShowError (Option Mod))
    (main parent : Mod) (isvisible : String → Mod → Mod → m Bool)
    (showModule : JuliaLean.base.show.JIO Io V → Mod → m Unit)
    (io : JuliaLean.base.show.JIO Io V) (x : JobStatus) : m Unit := do
  if !(← JuliaLean.base.show.assertBool a (JuliaLean.base.show.getIO p io "compact" false)) then
    let origin ← match JuliaLean.base.show.getIO p io "module" main with
      | .inl value =>
          match moduleOfValue value with
          | .ok module => pure module
          | .error error => JuliaLean.base.show.throwShow error
      | .inr fallback => pure (some fallback)
    let qualify ← match origin with
      | none => pure true
      | some originModule => do
          let visible ← isvisible (jobStatusSymbol x) parent originModule
          pure !visible
    if qualify then
      showModule io parent
      JuliaLean.base.show.printStr p io "."
  JuliaLean.base.show.print_Symbol p io (jobStatusSymbol x)

/--
Base `Enums.jl:57-62`; macro expansion is `Enums.jl:218-237`.
Julia source: base/precompilation.jl:163-163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum JobStatus::UInt8 begin
```
-/
def jobStatusShowTextPlain {m : Type → Type} {Io V Ty : Type} [Monad m]
    [MonadExceptOf JuliaLean.base.show.ShowError m]
    (p : JuliaLean.base.show.IOPrims m Io V) (a : JuliaLean.base.show.AnyOps V Ty)
    (showType : JuliaLean.base.show.JIO Io V → m Unit)
    (showInteger : JuliaLean.base.show.JIO Io V → U8 → m Unit)
    (io : JuliaLean.base.show.JIO Io V) (x : JobStatus) : m Unit := do
  jobStatusPrint p io x
  JuliaLean.base.show.printStr p io "::"
  let compactIO ← JuliaLean.base.show.withBool p a io "compact" true
  showType compactIO
  JuliaLean.base.show.printStr p io " = "
  showInteger io (jobStatusInteger x)

/--
Base `Enums.jl:64-75`; macro expansion is `Enums.jl:218-237`.
Julia source: base/precompilation.jl:163-163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum JobStatus::UInt8 begin
```
-/
def jobStatusShowTypeTextPlain {m : Type → Type} {Io V : Type} [Monad m]
    (p : JuliaLean.base.show.IOPrims m Io V)
    (showDatatype : JuliaLean.base.show.JIO Io V → m Unit)
    (showInteger : JuliaLean.base.show.JIO Io V → U8 → m Unit)
    (io : JuliaLean.base.show.JIO Io V) : m Unit := do
  JuliaLean.base.show.printStr p io "Enum "
  showDatatype io
  JuliaLean.base.show.printStr p io ":"
  for x in jobStatusInstances do
    JuliaLean.base.show.printStr p io "\n"
    JuliaLean.base.show.print_Symbol p io (jobStatusSymbol x)
    JuliaLean.base.show.printStr p io " = "
    showInteger io (jobStatusInteger x)

/--
Base `Enums.jl:91`; `Ref` uses the installed `base/refvalue.jl` constructor.
Julia source: base/precompilation.jl:163-163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum JobStatus::UInt8 begin
```
-/
def jobStatusBroadcastable {R : Type} (makeRef : JobStatus → R) (x : JobStatus) : R :=
  makeRef x

/--
Julia source: base/precompilation.jl:172-185 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mutable struct PrecompileJob
    status::JobStatus
    started_at::Float64
    error_msg::String
    output::IOBuffer
    pid::Int32
    had_pid::Bool  # sticky: true once a subprocess was actually spawned for this job
    lock_holder::String
    waiting_for_bg::Bool
    verbose_timing::String  # raw payload from the worker subprocess; surfaced in verbose mode
    peak_rss_bytes::UInt64  # max RSS observed by `poll_process_stats!`; 0 on unsupported platforms
    PrecompileJob() = new(JOB_PENDING, 0.0, "", IOBuffer(), Int32(0), false, "", false, "", UInt64(0))
end

```
-/
/- `PrecompileJob`, whose `output::IOBuffer` is of type `Buf`. -/
structure PrecompileJob (Buf : Type) where
  status : JobStatus
  started_at : JuliaLean.base.float.FV .f64
  error_msg : Bytes
  output : Buf
  pid : JInt .i32
  had_pid : Bool
  lock_holder : Bytes
  waiting_for_bg : Bool
  verbose_timing : Bytes
  peak_rss_bytes : JInt .u64

/-- `PrecompileJob()`, given the fresh `IOBuffer()`. -/
def PrecompileJob.new {Buf : Type} (buf : Buf) : PrecompileJob Buf :=
  ⟨.JOB_PENDING, JuliaLean.Promotion.Fl.ofBits 0, [], buf, JInt.wrap .i32 0, false, [], false, [], JInt.wrap .u64 0⟩

section job
variable {Buf : Type}

/--
Julia source: base/precompilation.jl:186-196 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
is_pending(j::PrecompileJob)    = j.status == JOB_PENDING
is_started(j::PrecompileJob)    = j.status == JOB_STARTED
is_recompiled(j::PrecompileJob) = j.status == JOB_RECOMPILED
is_soft_error(j::PrecompileJob) = j.status == JOB_SOFT_ERROR
is_failed(j::PrecompileJob)     = j.status == JOB_FAILED
is_dep_failed(j::PrecompileJob) = j.status == JOB_DEP_FAILED
has_pid(j::PrecompileJob)       = j.pid > 0
had_pid(j::PrecompileJob)       = j.had_pid
is_locked(j::PrecompileJob)     = !isempty(j.lock_holder)
is_waiting(j::PrecompileJob)    = j.waiting_for_bg

```
-/
-- Source: base/precompilation.jl:186 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def is_pending (j : PrecompileJob Buf) : Bool := j.status == .JOB_PENDING
-- Source: base/precompilation.jl:187 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def is_started (j : PrecompileJob Buf) : Bool := j.status == .JOB_STARTED
-- Source: base/precompilation.jl:188 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def is_recompiled (j : PrecompileJob Buf) : Bool := j.status == .JOB_RECOMPILED
-- Source: base/precompilation.jl:189 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def is_soft_error (j : PrecompileJob Buf) : Bool := j.status == .JOB_SOFT_ERROR
-- Source: base/precompilation.jl:190 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def is_failed (j : PrecompileJob Buf) : Bool := j.status == .JOB_FAILED
-- Source: base/precompilation.jl:191 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def is_dep_failed (j : PrecompileJob Buf) : Bool := j.status == .JOB_DEP_FAILED
-- Source: base/precompilation.jl:192 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def has_pid (j : PrecompileJob Buf) : Bool := j.pid.val > 0
-- Source: base/precompilation.jl:193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def had_pid (j : PrecompileJob Buf) : Bool := j.had_pid
-- Source: base/precompilation.jl:194 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def is_locked (j : PrecompileJob Buf) : Bool := !j.lock_holder.isEmpty
-- Source: base/precompilation.jl:195 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def is_waiting (j : PrecompileJob Buf) : Bool := j.waiting_for_bg

/--
Julia source: base/precompilation.jl:197-211 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mark_started!(j::PrecompileJob, t::Float64=time()) = (j.status = JOB_STARTED; j.started_at = t)
mark_recompiled!(j::PrecompileJob) = (j.status = JOB_RECOMPILED)
mark_soft_error!(j::PrecompileJob) = (j.status = JOB_SOFT_ERROR)
mark_failed!(j::PrecompileJob, msg::String) = (j.status = JOB_FAILED; j.error_msg = msg)
# `root` names the package whose failure caused the skip
mark_dep_failed!(j::PrecompileJob, root::String) = (j.status = JOB_DEP_FAILED; j.error_msg = root)
set_pid!(j::PrecompileJob, pid::Int32) = (j.pid = pid; j.had_pid = true)
clear_pid!(j::PrecompileJob) = (j.pid = Int32(0))

function clear_failure!(j::PrecompileJob)
    j.status = JOB_PENDING
    j.error_msg = ""
    truncate(j.output, 0)
end

```
-/
/- `mark_started!(j, t)`; the default `t` is `time()`. -/
def mark_started (j : PrecompileJob Buf) (t : JuliaLean.base.float.FV .f64) : PrecompileJob Buf :=
  { j with status := .JOB_STARTED, started_at := t }
-- Source: base/precompilation.jl:198 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def mark_recompiled_result (j : PrecompileJob Buf) : JobStatus × PrecompileJob Buf :=
  (.JOB_RECOMPILED, { j with status := .JOB_RECOMPILED })

def mark_recompiled (j : PrecompileJob Buf) : PrecompileJob Buf :=
  (mark_recompiled_result j).2

-- Source: base/precompilation.jl:199 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def mark_soft_error_result (j : PrecompileJob Buf) : JobStatus × PrecompileJob Buf :=
  (.JOB_SOFT_ERROR, { j with status := .JOB_SOFT_ERROR })

def mark_soft_error (j : PrecompileJob Buf) : PrecompileJob Buf :=
  (mark_soft_error_result j).2

-- Source: base/precompilation.jl:200 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def mark_failed_result (j : PrecompileJob Buf) (msg : Bytes) : Bytes × PrecompileJob Buf :=
  let j := { j with status := .JOB_FAILED }
  (msg, { j with error_msg := msg })

def mark_failed (j : PrecompileJob Buf) (msg : Bytes) : PrecompileJob Buf :=
  (mark_failed_result j msg).2

-- Source: base/precompilation.jl:202 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def mark_dep_failed_result (j : PrecompileJob Buf) (root : Bytes) : Bytes × PrecompileJob Buf :=
  let j := { j with status := .JOB_DEP_FAILED }
  (root, { j with error_msg := root })

def mark_dep_failed (j : PrecompileJob Buf) (root : Bytes) : PrecompileJob Buf :=
  (mark_dep_failed_result j root).2

-- Source: base/precompilation.jl:203 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def set_pid_result (j : PrecompileJob Buf) (pid : JInt .i32) : Bool × PrecompileJob Buf :=
  let j := { j with pid := pid }
  (true, { j with had_pid := true })

def set_pid (j : PrecompileJob Buf) (pid : JInt .i32) : PrecompileJob Buf :=
  (set_pid_result j pid).2

-- Source: base/precompilation.jl:204 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def clear_pid_result (j : PrecompileJob Buf) : JInt .i32 × PrecompileJob Buf :=
  (JInt.wrap .i32 0, { j with pid := JInt.wrap .i32 0 })

def clear_pid (j : PrecompileJob Buf) : PrecompileJob Buf :=
  (clear_pid_result j).2

/-- `clear_failure!(j)`; `truncate0` is `truncate(io, 0)` of the job's `IOBuffer`. -/
def clear_failure {m : Type → Type} [Monad m] (truncate0 : Buf → m Buf) (j : PrecompileJob Buf) :
    m (PrecompileJob Buf) := do
  let j := { j with status := .JOB_PENDING, error_msg := [] }
  return { j with output := ← truncate0 j.output }

end job

/--
Julia source: base/precompilation.jl:346-355 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
## Constants and formatting utilities

const ansi_movecol1 = "\e[1G"
const ansi_cleartoend = "\e[0J"
const ansi_cleartoendofline = "\e[0K"
const ansi_enablecursor = "\e[?25h"
const ansi_disablecursor = "\e[?25l"
const ansi_clearline = "\e[2K"
ansi_moveup(n::Int) = string("\e[", n, "A")

```
-/
def ansi_movecol1 : Bytes := lit "\x1b[1G"
def ansi_cleartoend : Bytes := lit "\x1b[0J"
def ansi_cleartoendofline : Bytes := lit "\x1b[0K"
def ansi_enablecursor : Bytes := lit "\x1b[?25h"
def ansi_disablecursor : Bytes := lit "\x1b[?25l"
def ansi_clearline : Bytes := lit "\x1b[2K"
/-- `ansi_moveup(n)`; `string(n)` of an `Int` is `stringInt`. -/
def ansi_moveup (stringInt : JInt .i64 → Bytes) (n : JInt .i64) : Bytes := lit "\x1b[" ++ stringInt n ++ lit "A"

/--
Julia source: base/precompilation.jl:356-364 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct PkgPrecompileError <: Exception
    msg::String
end
Base.showerror(io::IO, err::PkgPrecompileError) = print(io, err.msg)
Base.showerror(io::IO, err::PkgPrecompileError, bt; kw...) = Base.showerror(io, err) # hide stacktrace

# This needs a show method to make `julia> err` show nicely
Base.show(io::IO, err::PkgPrecompileError) = print(io, "PkgPrecompileError: ", err.msg)

```
-/
structure PkgPrecompileError where
  msg : Bytes

section printing
variable {m : Type → Type} [Monad m] {Io : Type}

-- Source: base/precompilation.jl:359 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def showerror_PkgPrecompileError {Result : Type} (print : Io → Bytes → m Result)
    (io : Io) (err : PkgPrecompileError) : m Result :=
  print io err.msg

-- Source: base/precompilation.jl:360 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def showerror_PkgPrecompileError_bt {BT Result : Type} (print : Io → Bytes → m Result)
    (io : Io) (err : PkgPrecompileError) (_bt : BT) : m Result :=
  showerror_PkgPrecompileError print io err

-- Source: base/precompilation.jl:363 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def show_PkgPrecompileError_selected {Result : Type}
    (print : Io → Bytes → Bytes → m Result) (io : Io) (err : PkgPrecompileError) : m Result :=
  print io (lit "PkgPrecompileError: ") err.msg

def show_PkgPrecompileError (print : Io → Bytes → m Unit) (io : Io) (err : PkgPrecompileError) : m Unit :=
  show_PkgPrecompileError_selected (fun stream label message => print stream (label ++ message)) io err

/--
Julia source: base/precompilation.jl:365-366 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
can_fancyprint(io::IO) = @something(get(io, :force_fancyprint, nothing), (Base.unwrapcontext(io)[1] isa Base.TTY && (get(ENV, "CI", nothing) != "true")))

```
-/
/- `can_fancyprint(io)`: `get(io, :force_fancyprint, nothing)` when it is not `nothing` (a value of
any type, `.inl`), else whether the stream inside the context is a `TTY` and `ENV["CI"]` is not
`"true"`. -/
def can_fancyprint {V : Type} (getForceFancyprint : Io → m (Option V)) (unwrappedIsTTY : Io → m Bool)
    (getENV : Bytes → m (Option Bytes)) (io : Io) : m (V ⊕ Bool) := do
  match ← getForceFancyprint io with
  | some v => return .inl v
  | none => return .inr ((← unwrappedIsTTY io) && (← getENV (lit "CI")) != some (lit "true"))

/--
Julia source: base/precompilation.jl:367-374 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# The driver prints through one concrete io type whatever stream it was given, so it and
# the closures it spawns are compiled once (into the sysimage) rather than once per
# stream type. A pipe, for example, is otherwise re-inferred by every process that
# captures `Pkg.precompile` output.
unstable_iocontext(io::IOContext{IO}) = io
unstable_iocontext(io::IOContext) = IOContext{IO}(io.io, io.dict)
unstable_iocontext(io::IO) = IOContext{IO}(io)

```
-/
/-
`unstable_iocontext(io)`: an `IOContext{IO}` with the same stream and properties. All three methods
return a context equal to their argument's (an `io::IO` that is not a context gets the empty one);
only the static type parameter changes, which the model does not represent. `wrap io` is
`IOContext{IO}(io)`.
-/
def unstable_iocontext {C : Type} (isContext : Io → Option C) (wrap : Io → C) (io : Io) : C :=
  match isContext io with
  | some c => c
  | none => wrap io

/--
Julia source: base/precompilation.jl:375-381 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function printpkgstyle(io, header, msg; color=:green)
    return @lock io begin
        printstyled(io, header; color, bold=true)
        println(io, " ", msg)
    end
end

```
-/
/- `printpkgstyle(io, header, msg; color)`: `printstyled(io, header; color, bold=true)` then
`println(io, " ", msg)` under `@lock io`. -/
def printpkgstyle {Color Header : Type} (lockIO : {α : Type} → Io → m α → m α)
    (printstyledBold : Io → Header → Color → m Unit) (print : Io → Bytes → m Unit)
    (io : Io) (header : Header) (msg : Bytes) (color : Color) : m Unit :=
  lockIO io do
    printstyledBold io header color
    print io (lit " " ++ msg ++ lit "\n")

end printing


/--
Julia source: base/precompilation.jl:440-443 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Header that labels the columns produced by `format_verbose_timing`. The leading
# 8 spaces account for `timing_string`'s width so columns line up.
format_verbose_timing_header() = "   total │ include   (deps)   (comp) │ methods  img-gen     cache  ~pk-rss"

```
-/
-- Source: base/precompilation.jl:442 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def format_verbose_timing_header : Bytes :=
  lit "   total │ include   (deps)   (comp) │ methods  img-gen     cache  ~pk-rss"

/--
Julia source: base/precompilation.jl:444-457 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Sum the on-disk size of the `.ji` cache file and (optionally) its companion
# pkgimage (`.so`/`.dylib`/`.dll`). Returns 0 if files are missing.
function _precompile_cache_bytes(cf_jl::AbstractString, cf_so::Union{Nothing,AbstractString})
    total = 0
    try
        isfile(cf_jl) && (total += filesize(cf_jl))
        cf_so === nothing || (isfile(cf_so) && (total += filesize(cf_so)))
    catch
    end
    return total
end



```
-/
/- `_precompile_cache_bytes(cf_jl, cf_so)`; the `try ... catch end` discards every exception of
`isfile`/`filesize` (here `PError`s), keeping the total so far. -/
def _precompile_cache_bytes {m : Type → Type} [Monad m] [MonadExceptOf PError m]
    (isfile : Bytes → m Bool) (filesize : Bytes → m (JInt .i64)) (cf_jl : Bytes) (cf_so : Option Bytes) :
    m (JInt .i64) := do
  let total := JInt.wrap .i64 0
  -- `isfile(cf_jl) && (total += filesize(cf_jl))`; an exception ends the `try` block
  let first ← tryCatchThe PError (do
    if ← isfile cf_jl then return some (JInt.wrap .i64 (total.val + (← filesize cf_jl).val))
    return some total) fun _ => pure none
  match first with
  | none => return total
  | some total =>
    -- `cf_so === nothing || (isfile(cf_so) && (total += filesize(cf_so)))`
    match cf_so with
    | none => return total
    | some so =>
      tryCatchThe PError (do
        if ← isfile so then return JInt.wrap .i64 (total.val + (← filesize so).val)
        return total) fun _ => pure total

/--
Julia source: base/precompilation.jl:458-466 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function color_string(cstr::String, col::Union{Int64, Symbol}, hascolor)
    if hascolor
        enable_ansi  = get(Base.text_colors, col, Base.text_colors[:default])
        disable_ansi = get(Base.disable_text_style, col, Base.text_colors[:default])
        return string(enable_ansi, cstr, disable_ansi)
    else
        return cstr
    end
end
```
-/
/- `color_string(cstr, col, hascolor)`, over the `base/util.jl` color tables. -/
def color_string {m : Type → Type} [Monad m] [MonadExceptOf PError m]
    (cstr : Bytes) (col : JuliaLean.base.util.Color) (hascolor : Bool) : m Bytes := do
  if hascolor then
    let dflt ← match JuliaLean.base.util.textColorEntry (.symbol "default") with
      | some s => pure s
      | none => throwP .keyError
    let enable_ansi := (JuliaLean.base.util.textColorEntry col).getD dflt
    let disable_ansi := (JuliaLean.base.util.disableTextStyleEntry col).getD dflt
    return lit enable_ansi ++ cstr ++ lit disable_ansi
  else
    return cstr

/--
Julia source: base/precompilation.jl:467-482 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# using Printf
Base.@kwdef mutable struct MiniProgressBar
    max::Int = 1
    header::String = ""
    color::Symbol = :nothing
    width::Int = 40
    current::Int = 0
    prev::Int = 0
    has_shown::Bool = false
    time_shown::Float64 = 0.0
    percentage::Bool = true
    always_reprint::Bool = false
    indent::Int = 4
end

```
-/
/- `MiniProgressBar`; `color` is a `Symbol`. -/
structure MiniProgressBar where
  max : JInt .i64 := JInt.wrap .i64 1
  header : Bytes := []
  color : Bytes := lit "nothing"
  width : JInt .i64 := JInt.wrap .i64 40
  current : JInt .i64 := JInt.wrap .i64 0
  prev : JInt .i64 := JInt.wrap .i64 0
  has_shown : Bool := false
  time_shown : JuliaLean.base.float.FV .f64 := JuliaLean.Promotion.Fl.ofBits 0
  percentage : Bool := true
  always_reprint : Bool := false
  indent : JInt .i64 := JInt.wrap .i64 4

/--
Julia source: base/precompilation.jl:483-485 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const PROGRESS_BAR_TIME_GRANULARITY = Ref(1 / 30.0) # 30 fps
const PROGRESS_BAR_PERCENTAGE_GRANULARITY = Ref(0.1)

```
-/
/- `PROGRESS_BAR_TIME_GRANULARITY[]` initially: `1 / 30.0`. -/
def PROGRESS_BAR_TIME_GRANULARITY : JuliaLean.base.float.FV .f64 :=
  JuliaLean.base.float.div_float (JuliaLean.base.float.sitofp .f64 (JInt.wrap .i64 1))
    (JuliaLean.Promotion.Fl.ofBits 0x403E000000000000)
/-- `PROGRESS_BAR_PERCENTAGE_GRANULARITY[]` initially: `0.1`. -/
def PROGRESS_BAR_PERCENTAGE_GRANULARITY : JuliaLean.base.float.FV .f64 := JuliaLean.Promotion.Fl.ofBits 0x3FB999999999999A

section progress
variable {m : Type → Type} [Monad m] [MonadExceptOf PError m] {Io : Type}

/--
Julia source: base/precompilation.jl:486-487 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
start_progress(io::IO, _::MiniProgressBar) = print(io, ansi_disablecursor)

```
-/
def start_progress (print : Io → Bytes → m Unit) (io : Io) (_p : MiniProgressBar) : m Unit :=
  print io ansi_disablecursor

/--
Julia source: base/precompilation.jl:488-535 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_progress(io::IO, p::MiniProgressBar; termwidth=nothing, carriagereturn=true)
    if p.max == 0
        perc = 0.0
        prev_perc = 0.0
    else
        perc = p.current / p.max * 100
        prev_perc = p.prev / p.max * 100
    end
    # Bail early if we are not updating the progress bar,
    # Saves printing to the terminal
    if !p.always_reprint && p.has_shown && !((perc - prev_perc) > PROGRESS_BAR_PERCENTAGE_GRANULARITY[])
        return
    end
    t = time()
    if !p.always_reprint && p.has_shown && (t - p.time_shown) < PROGRESS_BAR_TIME_GRANULARITY[]
        return
    end
    p.time_shown = t
    p.prev = p.current
    p.has_shown = true

    progress_text = string(p.current, "/",  p.max)
    termwidth = @something termwidth (displaysize(io)::Tuple{Int,Int})[2]
    max_progress_width = max(0, min(termwidth - textwidth(p.header) - textwidth(progress_text) - 10 , p.width))
    filled = max_progress_width * clamp(perc / 100, 0.0, 1.0)
    (partial_filled, n_filled::Int64) = modf(filled) # get fractional / integer part
    n_left = max_progress_width - n_filled
    headers = split(p.header, ' ')
    to_print = sprint(; context=io) do io
        print(io, " "^p.indent)
        printstyled(io, headers[1], " "; color=:green, bold=true)
        printstyled(io, join(headers[2:end], ' '))
        print(io, " ")
        printstyled(io, "━"^n_filled; color=p.color)
        if n_left > 0
            if partial_filled > 0.5
                printstyled(io, "╸"; color=p.color) # More filled, use ╸
            else
                printstyled(io, "╺"; color=:light_black) # Less filled, use ╺
            end
            printstyled(io, "━"^(n_left-1); color=:light_black)
        end
        printstyled(io, " "; color=:light_black)
        print(io, progress_text)
        carriagereturn && print(io, "\r")
    end
    # Print everything in one call
    print(io, to_print)
```
-/
/- Callees of `show_progress`. `printstyled io s color bold`; `sprintCtx io f` is
`sprint(f; context=io)`; `repeatStr s n` is `s^n` (an `ArgumentError` for `n < 0`); `modf` is
`base/math.jl`'s; `toInt64` is `convert(Int64, x)` of a `Float64` (`InexactError` unless integral);
`clamp01 x` is `clamp(x, 0.0, 1.0)` (`base/intfuncs.jl`); the `Ref`s hold `granularities`. -/
structure ProgressOps (m : Type → Type) (Io : Type) where
  print : Io → Bytes → m Unit
  printstyled : Io → Bytes → Bytes → Bool → m Unit
  sprintCtx : Io → (Io → m Unit) → m Bytes
  time : m (JuliaLean.base.float.FV .f64)
  displaysizeCols : Io → m (JInt .i64)
  textwidth : Bytes → JInt .i64
  stringInt : JInt .i64 → Bytes
  split : Bytes → UInt8 → List Bytes
  repeatStr : Bytes → JInt .i64 → m Bytes
  clamp01 : JuliaLean.base.float.FV .f64 → JuliaLean.base.float.FV .f64
  modf : JuliaLean.base.float.FV .f64 → JuliaLean.base.float.FV .f64 × JuliaLean.base.float.FV .f64
  toInt64 : JuliaLean.base.float.FV .f64 → m (JInt .i64)
  granularities : m (JuliaLean.base.float.FV .f64 × JuliaLean.base.float.FV .f64)

open JuliaLean.base.float in
/-- `show_progress(io, p; termwidth, carriagereturn)`: returns the updated `p`. -/
def show_progress (o : ProgressOps m Io) (io : Io) (p : MiniProgressBar) (termwidth : Option (JInt .i64) := none)
    (carriagereturn : Bool := true) : m MiniProgressBar := do
  let f (n : Int) : FV .f64 := sitofp .f64 (JInt.wrap .i64 n)
  let (perc, prev_perc) :=
    if p.max.val == 0 then (f 0, f 0)
    else (mul_float (div_float (f p.current.val) (f p.max.val)) (f 100),
          mul_float (div_float (f p.prev.val) (f p.max.val)) (f 100))
  let (time_gran, perc_gran) ← o.granularities
  -- Bail early if we are not updating the progress bar, saves printing to the terminal
  if !p.always_reprint && p.has_shown && !(lt_float perc_gran (sub_float perc prev_perc)) then
    return p
  let t ← o.time
  if !p.always_reprint && p.has_shown && lt_float (sub_float t p.time_shown) time_gran then
    return p
  let p := { p with time_shown := t, prev := p.current, has_shown := true }
  let progress_text := o.stringInt p.current ++ lit "/" ++ o.stringInt p.max
  let termwidth ← match termwidth with
    | some w => pure w
    | none => o.displaysizeCols io
  let w := JInt.wrap .i64 (termwidth.val - (o.textwidth p.header).val - (o.textwidth progress_text).val - 10)
  let max_progress_width := JInt.wrap .i64 (max 0 (min w.val p.width.val))
  let filled := mul_float (f max_progress_width.val) (o.clamp01 (div_float perc (f 100)))
  let (partial_filled, n_filled_f) := o.modf filled -- get fractional / integer part
  let n_filled ← o.toInt64 n_filled_f
  let n_left := JInt.wrap .i64 (max_progress_width.val - n_filled.val)
  let headers := o.split p.header (' '.toNat.toUInt8)
  let to_print ← o.sprintCtx io fun io => do
    o.print io (← o.repeatStr (lit " ") p.indent)
    match headers with
    | [] => throwP .boundsError
    | h :: rest =>
      o.printstyled io (h ++ lit " ") (lit "green") true
      o.printstyled io ((lit " ").intercalate rest) (lit "normal") false
    o.print io (lit " ")
    o.printstyled io (← o.repeatStr (lit "━") n_filled) p.color false
    if n_left.val > 0 then
      if lt_float (JuliaLean.Promotion.Fl.ofBits 0x3FE0000000000000) partial_filled then
        o.printstyled io (lit "╸") p.color false -- More filled, use ╸
      else
        o.printstyled io (lit "╺") (lit "light_black") false -- Less filled, use ╺
      o.printstyled io (← o.repeatStr (lit "━") (JInt.wrap .i64 (n_left.val - 1))) (lit "light_black") false
    o.printstyled io (lit " ") (lit "light_black") false
    o.print io progress_text
    if carriagereturn then o.print io (lit "\r")
  -- Print everything in one call
  o.print io to_print
  return p

/--
Julia source: base/precompilation.jl:536-541 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
end

end_progress(io, p::MiniProgressBar) = print(io, ansi_enablecursor, ansi_clearline)

print_progress_bottom(io::IO) = print(io, "\e[S", ansi_moveup(1), ansi_clearline, ansi_movecol1)

```
-/
def end_progress {P : Type} (print : Io → Bytes → m Unit) (io : Io) (_p : P) : m Unit :=
  print io (ansi_enablecursor ++ ansi_clearline)

/-- `print_progress_bottom(io)`; `ansi_moveup(1)` is `"\e[1A"`. -/
def print_progress_bottom (print : Io → Bytes → m Unit) (io : Io) : m Unit :=
  print io (lit "\x1b[S" ++ ansi_moveup (fun n => lit (toString n.val)) (JInt.wrap .i64 1) ++ ansi_clearline ++ ansi_movecol1)

end progress

/--
Julia source: base/precompilation.jl:542-566 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
## ExplicitEnv

# This is currently only used for pkgprecompile but the plan is to use this in code loading in the future
# see the `kc/codeloading2.0` branch
struct ExplicitEnv
    path::String
    project_deps::Dict{String, UUID}     # [deps] in the active project's Project.toml
    project_weakdeps::Dict{String, UUID} # [weakdeps] in the active project's Project.toml
    project_extras::Dict{String, UUID}   # [extras] in the active project's Project.toml
    project_extensions::Dict{String, Vector{UUID}} # [extensions] in the active project's Project.toml
    workspace_deps::Dict{UUID, String}   # packages and [deps] from all workspace member Project.tomls
    deps::Dict{UUID, Vector{UUID}}       # full dependency graph from Manifest.toml
    weakdeps::Dict{UUID, Vector{UUID}}   # full weak dependency graph from Manifest.toml
    extensions::Dict{UUID, Dict{String, Vector{UUID}}}
    # Lookup name for a UUID
    names::Dict{UUID, String}
    lookup_strategy::Dict{UUID, Union{
                                      SHA1,     # `git-tree-sha1` entry
                                      String,   # `path` entry
                                      Nothing,  # stdlib (no `path` nor `git-tree-sha1`)
                                      Missing}} # not present in the manifest
    #prefs::Union{Nothing, Dict{String, Any}}
    #local_prefs::Union{Nothing, Dict{String, Any}}
end

```
-/
/- `lookup_strategy` entries: a `git-tree-sha1` (`SHA1`), a `path`, a stdlib (`nothing`), or not
in the manifest (`missing`). -/
inductive LookupStrategy (SHA1 : Type) where
  | sha1 (h : SHA1)
  | path (p : Bytes)
  | stdlib
  | missing

/-- `ExplicitEnv` over the dictionary type `Dict`. -/
structure ExplicitEnv (Dict : Type → Type → Type) (SHA1 : Type) where
  path : Bytes
  project_deps : Dict Bytes UUID
  project_weakdeps : Dict Bytes UUID
  project_extras : Dict Bytes UUID
  project_extensions : Dict Bytes (List UUID)
  workspace_deps : Dict UUID Bytes
  deps : Dict UUID (List UUID)
  weakdeps : Dict UUID (List UUID)
  extensions : Dict UUID (Dict Bytes (List UUID))
  names : Dict UUID Bytes
  lookup_strategy : Dict UUID (LookupStrategy SHA1)

section env
variable {m : Type → Type} [Monad m] [MonadExceptOf PError m] {Dict : Type → Type → Type}

/-- A TOML value of type `Any`, of type `A`: the type tests and assertions applied to it. -/
structure AnyOps (Dict : Type → Type → Type) (A : Type) where
  asString : A → Option Bytes
  asDict : A → Option (Dict Bytes A)
  /-- `x isa Vector{String}`. -/
  asStrings : A → Option (List Bytes)
  /-- `x isa Vector{Any}`. -/
  asAnys : A → Option (List A)

/-- Callees of the `ExplicitEnv` constructors, from `base/loading.jl`, `base/path.jl`,
`base/file.jl` and `base/uuid.jl`. -/
structure EnvOps (n : Type → Type) (Dict : Type → Type → Type) (A SHA1 : Type) where
  active_project : n (Option Bytes)
  isfile : Bytes → n Bool
  project_file_manifest_path : Bytes → n (Option Bytes)
  abspath : Bytes → n Bytes
  parsed_toml : Bytes → n (Dict Bytes A)
  get_deps : Dict Bytes A → n (Dict Bytes A)
  base_project : Bytes → n (Option Bytes)
  /-- `Base.env_project_file(p)` when it is a `String`. -/
  env_project_file : Bytes → n (Option Bytes)
  /-- `Base.locate_project_file(p)` when it is a `String`. -/
  locate_project_file : Bytes → n (Option Bytes)
  joinpath : Bytes → Bytes → n Bytes
  dirname : Bytes → n Bytes
  readdir : Bytes → n (List Bytes)
  STDLIB : Bytes
  /-- `UUID(s::String)`. -/
  parseUUID : Bytes → n UUID
  /-- `SHA1(s::String)`. -/
  parseSHA1 : Bytes → n SHA1

/-- `x::T`, a type assertion. -/
def typeassert {α β : Type} (f : α → Option β) (x : α) : m β :=
  match f x with
  | some y => pure y
  | none => throwP .typeError

/-- `get(d, k, nothing)::Union{T, Nothing}`. -/
def getOpt {A T : Type} (D : DictOps Dict) (f : A → Option T) (d : Dict Bytes A) (k : Bytes) : m (Option T) :=
  match D.get d k with
  | none => pure none
  | some v => some <$> typeassert f v

/-- `get(Dict{String, Any}, d, k)::Dict{String, Any}`. -/
def getDictAny {A : Type} (D : DictOps Dict) (a : AnyOps Dict A) (d : Dict Bytes A) (k : Bytes) : m (Dict Bytes A) :=
  match D.get d k with
  | none => pure D.empty
  | some v => typeassert a.asDict v

/-- `triggers isa String ? [triggers] : triggers::Vector{String}`. -/
def triggerList {A : Type} (a : AnyOps Dict A) (triggers : A) : m (List Bytes) :=
  match a.asString triggers with
  | some s => pure [s]
  | none => typeassert a.asStrings triggers

/-- A manifest `deps`/`weakdeps` entry: compressed names or expanded UUIDs. -/
inductive DepList where
  | names (ns : List Bytes)
  | uuids (us : List UUID)

/--
Julia source: base/precompilation.jl:568-580 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ExplicitEnv(::Nothing, envpath::String="")
    ExplicitEnv(envpath,
        Dict{String, UUID}(),     # project_deps
        Dict{String, UUID}(),     # project_weakdeps
        Dict{String, UUID}(),     # project_extras
        Dict{String, Vector{UUID}}(), # project_extensions
        Dict{UUID, String}(),     # workspace_deps
        Dict{UUID, Vector{UUID}}(),   # deps
        Dict{UUID, Vector{UUID}}(),   # weakdeps
        Dict{UUID, Dict{String, Vector{UUID}}}(), # extensions
        Dict{UUID, String}(),     # names
        Dict{UUID, Union{SHA1, String, Nothing, Missing}}())
end
```
-/
def ExplicitEnv_Nothing {SHA1 : Type} (D : DictOps Dict) (envpath : Bytes := []) : ExplicitEnv Dict SHA1 :=
  ⟨envpath,
    D.empty, -- project_deps
    D.empty, -- project_weakdeps
    D.empty, -- project_extras
    D.empty, -- project_extensions
    D.empty, -- workspace_deps
    D.empty, -- deps
    D.empty, -- weakdeps
    D.empty, -- extensions
    D.empty, -- names
    D.empty⟩

/--
Julia source: base/precompilation.jl:824-851 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function collect_workspace_deps!(workspace_deps::Dict{UUID, String}, seen::Set{String}, project_file::String)
    project_file = abspath(project_file)
    project_file in seen && return
    push!(seen, project_file)

    project = parsed_toml(project_file)
    for (name, _uuid) in get(Dict{String, Any}, project, "deps")::Dict{String, Any}
        workspace_deps[UUID(_uuid::String)] = name
    end

    name = get(project, "name", nothing)::Union{String, Nothing}
    _uuid = get(project, "uuid", nothing)::Union{String, Nothing}
    if name !== nothing && _uuid !== nothing
        workspace_deps[UUID(_uuid)] = name
    end

    workspace = get(project, "workspace", nothing)::Union{Dict{String, Any}, Nothing}
    workspace === nothing && return
    projects = get(workspace, "projects", nothing)::Union{Vector{String}, Nothing, String}
    projects isa Vector || return
    for member in projects
        member_file = Base.env_project_file(joinpath(dirname(project_file), member))
        member_file isa String || continue
        collect_workspace_deps!(workspace_deps, seen, member_file)
    end
    return
end

```
-/
/- `projects = get(workspace, "projects", nothing)::Union{Vector{String}, Nothing, String}`
and `projects isa Vector || return`. -/
def workspaceProjects {A : Type} (D : DictOps Dict) (a : AnyOps Dict A) (workspace : Dict Bytes A) :
    m (Option (List Bytes)) :=
  match D.get workspace (lit "projects") with
  | none => pure none
  | some v => match a.asStrings v, a.asString v with
    | some ps, _ => pure (some ps)
    | none, some _ => pure none
    | none, none => throwP .typeError

mutual
/-- `collect_workspace_deps!(workspace_deps, seen, project_file)`: returns `(workspace_deps, seen)`. -/
def collect_workspace_deps_bang [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] {A SHA1 : Type}
    (D : DictOps Dict) (a : AnyOps Dict A) (e : EnvOps m Dict A SHA1)
    (workspace_deps : Dict UUID Bytes) (seen : Dict Bytes Unit) (project_file : Bytes) :
    m (Dict UUID Bytes × Dict Bytes Unit) := do
  let project_file ← e.abspath project_file
  if setIn D seen project_file then return (workspace_deps, seen)
  let seen := setPush D seen project_file
  let project ← e.parsed_toml project_file
  let mut workspace_deps := workspace_deps
  let deps ← getDictAny D a project (lit "deps")
  for name in D.keys deps do
    let _uuid ← getindex D deps name
    workspace_deps := D.set workspace_deps (← e.parseUUID (← typeassert a.asString _uuid)) name
  let name ← getOpt D a.asString project (lit "name")
  let _uuid ← getOpt D a.asString project (lit "uuid")
  if let (some name, some _uuid) := (name, _uuid) then
    workspace_deps := D.set workspace_deps (← e.parseUUID _uuid) name
  let workspace ← getOpt D a.asDict project (lit "workspace")
  match workspace with
  | none => return (workspace_deps, seen)
  | some workspace =>
    match ← workspaceProjects D a workspace with
    | none => return (workspace_deps, seen)
    | some projects => collect_workspace_members D a e project_file workspace_deps seen projects
partial_fixpoint

/-- The `for member in projects` loop of `collect_workspace_deps!`. -/
def collect_workspace_members [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] {A SHA1 : Type}
    (D : DictOps Dict) (a : AnyOps Dict A) (e : EnvOps m Dict A SHA1) (project_file : Bytes)
    (workspace_deps : Dict UUID Bytes) (seen : Dict Bytes Unit) :
    List Bytes → m (Dict UUID Bytes × Dict Bytes Unit)
  | [] => pure (workspace_deps, seen)
  | member :: rest => do
    let member_file ← e.env_project_file (← e.joinpath (← e.dirname project_file) member)
    match member_file with
    | none => collect_workspace_members D a e project_file workspace_deps seen rest
    | some member_file =>
      let r ← collect_workspace_deps_bang D a e workspace_deps seen member_file
      collect_workspace_members D a e project_file r.1 r.2 rest
partial_fixpoint
end

/--
Julia source: base/precompilation.jl:812-823 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function collect_workspace_deps(project_file::String)
    while true
        base = base_project(project_file)
        base === nothing && break
        project_file = base
    end

    workspace_deps = Dict{UUID, String}()
    collect_workspace_deps!(workspace_deps, Set{String}(), project_file)
    return workspace_deps
end

```
-/
/- The `while true` loop of `collect_workspace_deps`. -/
def base_project_loop [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] {A SHA1 : Type}
    (e : EnvOps m Dict A SHA1) (project_file : Bytes) : m Bytes := do
  match ← e.base_project project_file with
  | none => pure project_file
  | some base => base_project_loop e base
partial_fixpoint

/-- `collect_workspace_deps(project_file)`. -/
def collect_workspace_deps [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] {A SHA1 : Type}
    (D : DictOps Dict) (a : AnyOps Dict A) (e : EnvOps m Dict A SHA1) (project_file : Bytes) :
    m (Dict UUID Bytes) := do
  let project_file ← base_project_loop e project_file
  let r ← collect_workspace_deps_bang D a e D.empty D.empty project_file
  return r.1

/--
Julia source: base/precompilation.jl:852-911 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# A manifest resolved by a different Julia version can record stale information for
# stdlibs: a dependency or extension the stdlib gained later, a dependency that is not in
# the manifest at all, or a git-tree-sha1 from when the package was not a stdlib yet.
# Code loading tolerates this by falling back to the stdlib's own Project.toml (see
# `Base.identify_stdlib_project_dep` and `Base.insert_extension_triggers`), so the
# dependency graph must include those edges too, otherwise a missing dependency is never
# precompiled before the stdlib that needs it and the strict precompile worker fails.
function fixup_stdlib_deps!(deps::Dict{UUID, Vector{UUID}}, weakdeps::Dict{UUID, Vector{UUID}},
                            extensions::Dict{UUID, Dict{String, Vector{UUID}}}, names::Dict{UUID, String},
                            lookup_strategy::Dict{UUID, Union{SHA1, String, Nothing, Missing}})
    stdlib_names = Set(readdir(Sys.STDLIB))
    stack = collect(keys(lookup_strategy))
    while !isempty(stack)
        uuid = pop!(stack)
        name = names[uuid]
        # same check as `Base.is_stdlib`, but keeping the parsed Project.toml
        name in stdlib_names || continue
        project_file = Base.locate_project_file(joinpath(Sys.STDLIB, name))
        project_file isa String || continue
        project_d = parsed_toml(project_file)
        project_uuid = get(project_d, "uuid", nothing)::Union{String, Nothing}
        (project_uuid !== nothing && UUID(project_uuid) == uuid) || continue
        project_deps = get(Dict{String, Any}, project_d, "deps")::Dict{String, Any}
        project_weakdeps = get(Dict{String, Any}, project_d, "weakdeps")::Dict{String, Any}
        project_extensions = get(Dict{String, Any}, project_d, "extensions")::Dict{String, Any}
        pkg_deps = get!(Vector{UUID}, deps, uuid)
        for (dep_name, _dep_uuid) in project_deps
            dep_uuid = UUID(_dep_uuid::String)
            dep_uuid in pkg_deps && continue
            push!(pkg_deps, dep_uuid)
            if !haskey(lookup_strategy, dep_uuid)
                # not in the manifest at all, so it is loaded as a stdlib
                names[dep_uuid] = dep_name
                lookup_strategy[dep_uuid] = nothing
                push!(stack, dep_uuid)
            end
        end
        pkg_weakdeps = get!(Vector{UUID}, weakdeps, uuid)
        for (dep_name, _dep_uuid) in project_weakdeps
            dep_uuid = UUID(_dep_uuid::String)
            dep_uuid in pkg_weakdeps && continue
            push!(pkg_weakdeps, dep_uuid)
            get!(names, dep_uuid, dep_name)
        end
        pkg_extensions = get!(Dict{String, Vector{UUID}}, extensions, uuid)
        for (ext, triggers) in project_extensions
            haskey(pkg_extensions, ext) && continue
            triggers = triggers isa String ? [triggers] : triggers::Vector{String}
            trigger_uuids = UUID[]
            for trigger in triggers
                _trigger_uuid = get(project_weakdeps, trigger, get(project_deps, trigger, nothing))::Union{String, Nothing}
                _trigger_uuid === nothing && break
                push!(trigger_uuids, UUID(_trigger_uuid))
            end
            length(trigger_uuids) == length(triggers) || continue
            pkg_extensions[ext] = trigger_uuids
        end
    end
    return deps
end
```
-/
/- The arguments `fixup_stdlib_deps!` mutates. -/
structure FixupState (Dict : Type → Type → Type) (SHA1 : Type) where
  deps : Dict UUID (List UUID)
  weakdeps : Dict UUID (List UUID)
  extensions : Dict UUID (Dict Bytes (List UUID))
  names : Dict UUID Bytes
  lookup_strategy : Dict UUID (LookupStrategy SHA1)

/-- One iteration of the `while !isempty(stack)` loop of `fixup_stdlib_deps!`, after
`uuid = pop!(stack)`; returns the new state and stack. -/
def fixup_step {A SHA1 : Type} (D : DictOps Dict) (a : AnyOps Dict A) (e : EnvOps m Dict A SHA1)
    (stdlib_names : Dict Bytes Unit) (s : FixupState Dict SHA1) (stack : List UUID) (uuid : UUID) :
    m (FixupState Dict SHA1 × List UUID) := do
  let name ← getindex D s.names uuid
  -- same check as `Base.is_stdlib`, but keeping the parsed Project.toml
  if !setIn D stdlib_names name then return (s, stack)
  let some project_file ← e.locate_project_file (← e.joinpath e.STDLIB name) | return (s, stack)
  let project_d ← e.parsed_toml project_file
  let project_uuid ← getOpt D a.asString project_d (lit "uuid")
  let ok ← match project_uuid with
    | some pu => do
      let pu ← e.parseUUID pu
      pure (pu == uuid)
    | none => pure false
  if !ok then return (s, stack)
  let project_deps ← getDictAny D a project_d (lit "deps")
  let project_weakdeps ← getDictAny D a project_d (lit "weakdeps")
  let project_extensions ← getDictAny D a project_d (lit "extensions")
  let mut s := s
  let mut stack := stack
  -- `pkg_deps = get!(Vector{UUID}, deps, uuid)`
  let mut pkg_deps := getD D s.deps uuid []
  for dep_name in D.keys project_deps do
    let dep_uuid ← e.parseUUID (← typeassert a.asString (← getindex D project_deps dep_name))
    if pkg_deps.contains dep_uuid then continue
    pkg_deps := pkg_deps ++ [dep_uuid]
    if !haskey D s.lookup_strategy dep_uuid then
      -- not in the manifest at all, so it is loaded as a stdlib
      s := { s with names := D.set s.names dep_uuid dep_name,
                    lookup_strategy := D.set s.lookup_strategy dep_uuid .stdlib }
      stack := stack ++ [dep_uuid]
  s := { s with deps := D.set s.deps uuid pkg_deps }
  let mut pkg_weakdeps := getD D s.weakdeps uuid []
  for dep_name in D.keys project_weakdeps do
    let dep_uuid ← e.parseUUID (← typeassert a.asString (← getindex D project_weakdeps dep_name))
    if pkg_weakdeps.contains dep_uuid then continue
    pkg_weakdeps := pkg_weakdeps ++ [dep_uuid]
    if !haskey D s.names dep_uuid then
      s := { s with names := D.set s.names dep_uuid dep_name }
  s := { s with weakdeps := D.set s.weakdeps uuid pkg_weakdeps }
  let mut pkg_extensions := getD D s.extensions uuid D.empty
  for ext in D.keys project_extensions do
    if haskey D pkg_extensions ext then continue
    let triggers ← triggerList a (← getindex D project_extensions ext)
    let mut trigger_uuids : List UUID := []
    for trigger in triggers do
      -- `get(project_weakdeps, trigger, get(project_deps, trigger, nothing))::Union{String, Nothing}`
      let dflt := D.get project_deps trigger
      let _trigger_uuid ← match D.get project_weakdeps trigger <|> dflt with
        | none => pure none
        | some v => some <$> typeassert a.asString v
      match _trigger_uuid with
      | none => break
      | some t => trigger_uuids := trigger_uuids ++ [← e.parseUUID t]
    if trigger_uuids.length != triggers.length then continue
    pkg_extensions := D.set pkg_extensions ext trigger_uuids
  s := { s with extensions := D.set s.extensions uuid pkg_extensions }
  return (s, stack)

/-- The `while !isempty(stack)` loop of `fixup_stdlib_deps!`. -/
def fixup_loop [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] {A SHA1 : Type} (D : DictOps Dict)
    (a : AnyOps Dict A) (e : EnvOps m Dict A SHA1) (stdlib_names : Dict Bytes Unit) (s : FixupState Dict SHA1)
    (stack : List UUID) : m (FixupState Dict SHA1) := do
  match stack.getLast? with
  | none => pure s
  | some uuid =>
    let r ← fixup_step D a e stdlib_names s stack.dropLast uuid
    fixup_loop D a e stdlib_names r.1 r.2
partial_fixpoint

/-- `fixup_stdlib_deps!(deps, weakdeps, extensions, names, lookup_strategy)`. -/
def fixup_stdlib_deps [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] {A SHA1 : Type} (D : DictOps Dict)
    (a : AnyOps Dict A) (e : EnvOps m Dict A SHA1) (s : FixupState Dict SHA1) : m (FixupState Dict SHA1) := do
  let stdlib_names := (← e.readdir e.STDLIB).foldl (setPush D) D.empty
  let stack := D.keys s.lookup_strategy
  fixup_loop D a e stdlib_names s stack

/--
Julia source: base/precompilation.jl:581-811 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ExplicitEnv(envpath::String)
    # Handle missing project file by creating an empty environment
    if !isfile(envpath) || project_file_manifest_path(envpath) === nothing
        envpath = abspath(envpath)
        return ExplicitEnv(nothing, envpath)
    end
    envpath = abspath(envpath)
    project_d = parsed_toml(envpath)

    # TODO: Perhaps verify that two packages with the same UUID do not have different names?
    names = Dict{UUID, String}()
    project_name_to_uuid = Dict{String, UUID}()

    project_deps = Dict{String, UUID}()
    project_weakdeps = Dict{String, UUID}()
    project_extras = Dict{String, UUID}()

    # Collect all direct dependencies of the project
    for key in ["deps", "weakdeps", "extras"]
        for (name, _uuid) in get(Dict{String, Any}, project_d, key)::Dict{String, Any}
            v = key == "deps" ? project_deps :
                key == "weakdeps" ? project_weakdeps :
                key == "extras" ? project_extras :
                error()
            uuid = UUID(_uuid::String)
            v[name] = uuid
            names[uuid] = name
            project_name_to_uuid[name] = uuid
        end
    end

    # A package in both deps and weakdeps is in fact only a weakdep
    for (name, _) in project_weakdeps
        delete!(project_deps, name)
    end

    # This project might be a package, in that case, that is also a "dependency"
    # of the project.
    proj_name = get(project_d, "name", nothing)::Union{String, Nothing}
    _proj_uuid = get(project_d, "uuid", nothing)::Union{String, Nothing}
    proj_uuid = _proj_uuid === nothing ? nothing : UUID(_proj_uuid)

    project_is_package = proj_name !== nothing && proj_uuid !== nothing
    if project_is_package
        # TODO: Error on missing uuid?
        project_deps[proj_name] = proj_uuid
        names[proj_uuid] = proj_name
    end

    project_extensions = Dict{String, Vector{UUID}}()
    # Collect all extensions of the project
    for (name, triggers) in get(Dict{String, Any}, project_d, "extensions")::Dict{String, Any}
        if triggers isa String
            triggers = [triggers]
        else
            triggers = triggers::Vector{String}
        end
        uuids = UUID[]
        for trigger in triggers
            uuid = get(project_name_to_uuid, trigger, nothing)
            if uuid === nothing
                error("Trigger $trigger for extension $name not found in project")
            end
            push!(uuids, uuid)
        end
        project_extensions[name] = uuids
    end

    manifest = project_file_manifest_path(envpath)
    manifest_d = manifest === nothing ? Dict{String, Any}() : parsed_toml(manifest)

    # Dependencies in a manifest can either be stored compressed (when name is unique among all packages)
    # in which case it is a `Vector{String}` or expanded where it is a `name => uuid` mapping.
    deps = Dict{UUID, Union{Vector{String}, Vector{UUID}}}()
    weakdeps = Dict{UUID, Union{Vector{String}, Vector{UUID}}}()
    extensions = Dict{UUID, Dict{String, Vector{String}}}()
    name_to_uuid = Dict{String, UUID}()
    lookup_strategy = Dict{UUID, Union{SHA1, String, Nothing, Missing}}()

    sizehint!(deps, length(manifest_d))
    sizehint!(weakdeps, length(manifest_d))
    sizehint!(extensions, length(manifest_d))
    sizehint!(name_to_uuid, length(manifest_d))
    sizehint!(lookup_strategy, length(manifest_d))

    for (name, pkg_infos) in get_deps(manifest_d)
        for pkg_info in pkg_infos::Vector{Any}
            pkg_info = pkg_info::Dict{String, Any}
            m_uuid = UUID(pkg_info["uuid"]::String)

            # If we have multiple packages with the same name we will overwrite things here
            # but that is fine since we will only use the information in here for packages
            # with unique names
            names[m_uuid] = name
            name_to_uuid[name] = m_uuid

            for key in ["deps", "weakdeps"]
                deps_pkg = get(Vector{String}, pkg_info, key)::Union{Vector{String}, Dict{String, Any}}
                d = key == "deps" ? deps :
                    key == "weakdeps" ? weakdeps :
                    error()

                # Compressed format with unique names:
                if deps_pkg isa Vector{String}
                    d[m_uuid] = deps_pkg
                # Expanded format:
                else
                    uuids = UUID[]
                    for (name_dep, _dep_uuid) in deps_pkg
                        dep_uuid = UUID(_dep_uuid::String)
                        push!(uuids, dep_uuid)
                        names[dep_uuid] = name_dep
                    end
                    d[m_uuid] = uuids
                end
            end

            # Extensions
            deps_pkg = get(Dict{String, Any}, pkg_info, "extensions")::Dict{String, Any}
            deps_pkg_concrete = Dict{String, Vector{String}}()
            for (ext, triggers) in deps_pkg
                if triggers isa String
                    triggers = [triggers]
                else
                    triggers = triggers::Vector{String}
                end
                deps_pkg_concrete[ext] = triggers
            end
            extensions[m_uuid] = deps_pkg_concrete

            # Determine strategy to find package
            lookup_strat = begin
                if (path = get(pkg_info, "path", nothing)::Union{String, Nothing}) !== nothing
                    path
                elseif (git_tree_sha_str = get(pkg_info, "git-tree-sha1", nothing)::Union{String, Nothing}) !== nothing
                    SHA1(git_tree_sha_str)
                else
                    nothing
                end
            end
            lookup_strategy[m_uuid] = lookup_strat
        end
    end

    # No matter if the deps were stored compressed or not in the manifest,
    # we internally store them expanded
    deps_expanded = Dict{UUID, Vector{UUID}}()
    weakdeps_expanded = Dict{UUID, Vector{UUID}}()
    extensions_expanded = Dict{UUID, Dict{String, Vector{UUID}}}()
    sizehint!(deps_expanded, length(deps))
    sizehint!(weakdeps_expanded, length(deps))
    sizehint!(extensions_expanded, length(deps))

    if proj_name !== nothing && proj_uuid !== nothing
        deps_expanded[proj_uuid] = filter!(!=(proj_uuid), collect(values(project_deps)))
        extensions_expanded[proj_uuid] = project_extensions
        path = get(project_d, "path", nothing)::Union{String, Nothing}
        entry_point = path !== nothing ? path : dirname(envpath)
        lookup_strategy[proj_uuid] = entry_point
    end

    for key in ["deps", "weakdeps"]
        d = key == "deps" ? deps :
            key == "weakdeps" ? weakdeps :
            error()
        d_expanded = key == "deps" ? deps_expanded :
                     key == "weakdeps" ? weakdeps_expanded :
                     error()
        for (pkg, deps) in d
            # dependencies was already expanded so use it directly:
            if deps isa Vector{UUID}
                d_expanded[pkg] = deps
                for dep in deps
                    name_to_uuid[names[dep]] = dep
                end
            # find the (unique) UUID associated with the name
            else
                deps_pkg = UUID[]
                sizehint!(deps_pkg, length(deps))
                for dep in deps
                    push!(deps_pkg, name_to_uuid[dep])
                end
                d_expanded[pkg] = deps_pkg
            end
        end
    end

    for (pkg, exts) in extensions
        exts_expanded = Dict{String, Vector{UUID}}()
        for (ext, triggers) in exts
            triggers_expanded = UUID[]
            sizehint!(triggers_expanded, length(triggers))
            for trigger in triggers
                push!(triggers_expanded, name_to_uuid[trigger])
            end
            exts_expanded[ext] = triggers_expanded
        end
        extensions_expanded[pkg] = exts_expanded
    end

    fixup_stdlib_deps!(deps_expanded, weakdeps_expanded, extensions_expanded, names, lookup_strategy)

    # Everything that does not yet have a lookup_strategy is missing from the manifest
    for (_, uuid) in project_deps
        get!(lookup_strategy, uuid, missing)
    end

    #=
    # Preferences:
    prefs = get(project_d, "preferences", nothing)

    # `(Julia)LocalPreferences.toml`
    project_dir = dirname(envpath)
    local_prefs = nothing
    for name in preferences_names
        toml_path = joinpath(project_dir, name)
        if isfile(toml_path)
            local_prefs = parsed_toml(toml_path)
            break
        end
    end
    =#

    workspace_deps = collect_workspace_deps(envpath)

    return ExplicitEnv(envpath, project_deps, project_weakdeps, project_extras,
                       project_extensions, workspace_deps,
                       deps_expanded, weakdeps_expanded, extensions_expanded,
                       names, lookup_strategy, #=prefs, local_prefs=#)
end

```
-/
/- `ExplicitEnv(envpath::String)`. -/
def ExplicitEnv_String [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] {A SHA1 : Type}
    (D : DictOps Dict) (a : AnyOps Dict A) (e : EnvOps m Dict A SHA1) (envpath : Bytes) :
    m (ExplicitEnv Dict SHA1) := do
  -- Handle missing project file by creating an empty environment
  if !(← e.isfile envpath) || (← e.project_file_manifest_path envpath).isNone then
    let envpath ← e.abspath envpath
    return ExplicitEnv_Nothing D envpath
  let envpath ← e.abspath envpath
  let project_d ← e.parsed_toml envpath
  let mut names : Dict UUID Bytes := D.empty
  let mut project_name_to_uuid : Dict Bytes UUID := D.empty
  let mut project_deps : Dict Bytes UUID := D.empty
  let mut project_weakdeps : Dict Bytes UUID := D.empty
  let mut project_extras : Dict Bytes UUID := D.empty
  -- Collect all direct dependencies of the project
  for key in [lit "deps", lit "weakdeps", lit "extras"] do
    let section_ ← getDictAny D a project_d key
    for name in D.keys section_ do
      let uuid ← e.parseUUID (← typeassert a.asString (← getindex D section_ name))
      if key == lit "deps" then project_deps := D.set project_deps name uuid
      else if key == lit "weakdeps" then project_weakdeps := D.set project_weakdeps name uuid
      else project_extras := D.set project_extras name uuid
      names := D.set names uuid name
      project_name_to_uuid := D.set project_name_to_uuid name uuid
  -- A package in both deps and weakdeps is in fact only a weakdep
  for name in D.keys project_weakdeps do
    project_deps := D.delete project_deps name
  -- This project might be a package, in that case, that is also a "dependency" of the project.
  let proj_name ← getOpt D a.asString project_d (lit "name")
  let _proj_uuid ← getOpt D a.asString project_d (lit "uuid")
  let proj_uuid ← match _proj_uuid with
    | none => pure none
    | some u => some <$> e.parseUUID u
  if let (some proj_name, some proj_uuid) := (proj_name, proj_uuid) then
    project_deps := D.set project_deps proj_name proj_uuid
    names := D.set names proj_uuid proj_name
  let mut project_extensions : Dict Bytes (List UUID) := D.empty
  -- Collect all extensions of the project
  let pexts ← getDictAny D a project_d (lit "extensions")
  for name in D.keys pexts do
    let triggers ← triggerList a (← getindex D pexts name)
    let mut uuids : List UUID := []
    for trigger in triggers do
      match D.get project_name_to_uuid trigger with
      | none => throwP (.errorException (lit "Trigger " ++ trigger ++ lit " for extension " ++ name ++
          lit " not found in project"))
      | some uuid => uuids := uuids ++ [uuid]
    project_extensions := D.set project_extensions name uuids
  let manifest ← e.project_file_manifest_path envpath
  let manifest_d ← match manifest with
    | none => pure D.empty
    | some mf => e.parsed_toml mf
  let mut deps : Dict UUID DepList := D.empty
  let mut weakdeps : Dict UUID DepList := D.empty
  let mut extensions : Dict UUID (Dict Bytes (List Bytes)) := D.empty
  let mut name_to_uuid : Dict Bytes UUID := D.empty
  let mut lookup_strategy : Dict UUID (LookupStrategy SHA1) := D.empty
  -- `sizehint!` calls do not change the dictionaries' contents
  let mdeps ← e.get_deps manifest_d
  for name in D.keys mdeps do
    let pkg_infos ← typeassert a.asAnys (← getindex D mdeps name)
    for pkg_info in pkg_infos do
      let pkg_info ← typeassert a.asDict pkg_info
      let m_uuid ← e.parseUUID (← typeassert a.asString (← getindex D pkg_info (lit "uuid")))
      -- If we have multiple packages with the same name we will overwrite things here
      names := D.set names m_uuid name
      name_to_uuid := D.set name_to_uuid name m_uuid
      for key in [lit "deps", lit "weakdeps"] do
        -- `get(Vector{String}, pkg_info, key)::Union{Vector{String}, Dict{String, Any}}`
        let entry : DepList ← match D.get pkg_info key with
          | none => pure (.names [])
          | some v => match a.asStrings v with
            -- Compressed format with unique names:
            | some ns => pure (.names ns)
            -- Expanded format:
            | none => do
              let deps_pkg ← typeassert a.asDict v
              let mut uuids : List UUID := []
              for name_dep in D.keys deps_pkg do
                let dep_uuid ← e.parseUUID (← typeassert a.asString (← getindex D deps_pkg name_dep))
                uuids := uuids ++ [dep_uuid]
                names := D.set names dep_uuid name_dep
              pure (.uuids uuids)
        if key == lit "deps" then deps := D.set deps m_uuid entry
        else weakdeps := D.set weakdeps m_uuid entry
      -- Extensions
      let deps_pkg ← getDictAny D a pkg_info (lit "extensions")
      let mut deps_pkg_concrete : Dict Bytes (List Bytes) := D.empty
      for ext in D.keys deps_pkg do
        deps_pkg_concrete := D.set deps_pkg_concrete ext (← triggerList a (← getindex D deps_pkg ext))
      extensions := D.set extensions m_uuid deps_pkg_concrete
      -- Determine strategy to find package
      let lookup_strat ← match ← getOpt D a.asString pkg_info (lit "path") with
        | some path => pure (LookupStrategy.path path)
        | none => match ← getOpt D a.asString pkg_info (lit "git-tree-sha1") with
          | some git_tree_sha_str => LookupStrategy.sha1 <$> e.parseSHA1 git_tree_sha_str
          | none => pure .stdlib
      lookup_strategy := D.set lookup_strategy m_uuid lookup_strat
  -- No matter if the deps were stored compressed or not in the manifest,
  -- we internally store them expanded
  let mut deps_expanded : Dict UUID (List UUID) := D.empty
  let mut weakdeps_expanded : Dict UUID (List UUID) := D.empty
  let mut extensions_expanded : Dict UUID (Dict Bytes (List UUID)) := D.empty
  if let (some _, some proj_uuid) := (proj_name, proj_uuid) then
    let vals ← (D.keys project_deps).mapM fun k => getindex D project_deps k
    deps_expanded := D.set deps_expanded proj_uuid (vals.filter (· != proj_uuid))
    extensions_expanded := D.set extensions_expanded proj_uuid project_extensions
    let path ← getOpt D a.asString project_d (lit "path")
    let entry_point ← match path with
      | some p => pure p
      | none => e.dirname envpath
    lookup_strategy := D.set lookup_strategy proj_uuid (.path entry_point)
  for key in [lit "deps", lit "weakdeps"] do
    let d := if key == lit "deps" then deps else weakdeps
    let mut d_expanded := if key == lit "deps" then deps_expanded else weakdeps_expanded
    for pkg in D.keys d do
      match ← getindex D d pkg with
      -- dependencies was already expanded so use it directly:
      | .uuids ds =>
        d_expanded := D.set d_expanded pkg ds
        for dep in ds do
          name_to_uuid := D.set name_to_uuid (← getindex D names dep) dep
      -- find the (unique) UUID associated with the name
      | .names ds =>
        let mut deps_pkg : List UUID := []
        for dep in ds do
          deps_pkg := deps_pkg ++ [← getindex D name_to_uuid dep]
        d_expanded := D.set d_expanded pkg deps_pkg
    if key == lit "deps" then deps_expanded := d_expanded else weakdeps_expanded := d_expanded
  for pkg in D.keys extensions do
    let exts ← getindex D extensions pkg
    let mut exts_expanded : Dict Bytes (List UUID) := D.empty
    for ext in D.keys exts do
      let mut triggers_expanded : List UUID := []
      for trigger in (← getindex D exts ext) do
        triggers_expanded := triggers_expanded ++ [← getindex D name_to_uuid trigger]
      exts_expanded := D.set exts_expanded ext triggers_expanded
    extensions_expanded := D.set extensions_expanded pkg exts_expanded
  let s ← fixup_stdlib_deps D a e ⟨deps_expanded, weakdeps_expanded, extensions_expanded, names, lookup_strategy⟩
  lookup_strategy := s.lookup_strategy
  -- Everything that does not yet have a lookup_strategy is missing from the manifest
  for name in D.keys project_deps do
    let uuid ← getindex D project_deps name
    if !haskey D lookup_strategy uuid then
      lookup_strategy := D.set lookup_strategy uuid .missing
  let workspace_deps ← collect_workspace_deps D a e envpath
  return ⟨envpath, project_deps, project_weakdeps, project_extras, project_extensions, workspace_deps,
    s.deps, s.weakdeps, s.extensions, s.names, lookup_strategy⟩

/--
Julia source: base/precompilation.jl:567-567 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ExplicitEnv() = ExplicitEnv(Base.active_project())
```
-/
def ExplicitEnv_0 [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] {A SHA1 : Type}
    (D : DictOps Dict) (a : AnyOps Dict A) (e : EnvOps m Dict A SHA1) : m (ExplicitEnv Dict SHA1) := do
  match ← e.active_project with
  | none => pure (ExplicitEnv_Nothing D [])
  | some p => ExplicitEnv_String D a e p

end env

section graph
variable {m : Type → Type} [Monad m] [MonadExceptOf PError m] {Dict : Type → Type → Type}

/--
Julia source: base/precompilation.jl:912-923 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

## Dependency graph

# name or parent → ext
function full_name(ext_to_parent::Dict{PkgId, PkgId}, pkg::PkgId)
    if haskey(ext_to_parent, pkg)
        return string(ext_to_parent[pkg].name, " → ", pkg.name)
    else
        return pkg.name
    end
end

```
-/
/- `full_name(ext_to_parent, pkg)`. -/
def full_name (D : DictOps Dict) (ext_to_parent : Dict PkgId PkgId) (pkg : PkgId) : m Bytes := do
  if haskey D ext_to_parent pkg then
    return (← getindex D ext_to_parent pkg).name ++ lit " → " ++ pkg.name
  else
    return pkg.name

/--
Julia source: base/precompilation.jl:924-958 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function excluded_circular_deps_explanation(io::IOContext, ext_to_parent::Dict{PkgId, PkgId}, circular_deps, cycles)
    outer_deps = copy(circular_deps)
    cycles_names = ""
    hascolor = get(io, :color, false)::Bool
    for cycle in cycles
        filter!(!in(cycle), outer_deps)
        cycle_str = ""
        for (i, pkg) in enumerate(cycle)
            j = max(0, i - 1)
            if length(cycle) == 1
                line = " ─ "
            elseif i == 1
                line = " ┌ "
            elseif i < length(cycle)
                line = " │ " * " " ^j
            else
                line = " └" * "─" ^j * " "
            end
            line = color_string(line, :light_black, hascolor) * full_name(ext_to_parent, pkg) * "\n"
            cycle_str *= line
        end
        cycles_names *= cycle_str
    end
    plural1 = length(cycles) > 1 ? "these cycles" : "this cycle"
    plural2 = length(cycles) > 1 ? "cycles" : "cycle"
    msg = """Circular dependency detected.
    Precompilation will be skipped for dependencies in $plural1:
    $cycles_names"""
    if !isempty(outer_deps)
        msg *= "Precompilation will also be skipped for the following, which depend on the above $plural2:\n"
        msg *= join(("  " * full_name(ext_to_parent, pkg) for pkg in outer_deps), "\n")
    end
    return msg
end

```
-/
def spacesN (n : Nat) (s : String) : Bytes := lit (String.join (List.replicate n s))

/-- `excluded_circular_deps_explanation(io, ext_to_parent, circular_deps, cycles)`; `hascolor` is
`get(io, :color, false)::Bool`. -/
def excluded_circular_deps_explanation (D : DictOps Dict) (hascolor : m Bool) (ext_to_parent : Dict PkgId PkgId)
    (circular_deps : List PkgId) (cycles : List (List PkgId)) : m Bytes := do
  let mut outer_deps := circular_deps
  let mut cycles_names : Bytes := []
  let hascolor ← hascolor
  for cycle in cycles do
    outer_deps := outer_deps.filter fun p => !cycle.contains p
    let mut cycle_str : Bytes := []
    for (pkg, idx) in cycle.zipIdx do
      let i := idx + 1
      let j := max 0 (i - 1)
      let line : Bytes :=
        if cycle.length == 1 then lit " ─ "
        else if i == 1 then lit " ┌ "
        else if i < cycle.length then lit " │ " ++ spacesN j " "
        else lit " └" ++ spacesN j "─" ++ lit " "
      let line := (← color_string line (.symbol "light_black") hascolor) ++ (← full_name D ext_to_parent pkg) ++ lit "\n"
      cycle_str := cycle_str ++ line
    cycles_names := cycles_names ++ cycle_str
  let plural1 := if cycles.length > 1 then "these cycles" else "this cycle"
  let plural2 := if cycles.length > 1 then "cycles" else "cycle"
  let mut msg := lit ("Circular dependency detected.\nPrecompilation will be skipped for dependencies in " ++
    plural1 ++ ":\n") ++ cycles_names
  if !outer_deps.isEmpty then
    msg := msg ++ lit ("Precompilation will also be skipped for the following, which depend on the above " ++
      plural2 ++ ":\n")
    let parts ← outer_deps.mapM fun pkg => do return lit "  " ++ (← full_name D ext_to_parent pkg)
    msg := msg ++ (lit "\n").intercalate parts
  return msg

/--
Julia source: base/precompilation.jl:959-993 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function scan_pkg!(stack, could_be_cycle, cycles, pkg, dmap)
    if haskey(could_be_cycle, pkg)
        return could_be_cycle[pkg]
    else
        return scan_deps!(stack, could_be_cycle, cycles, pkg, dmap)
    end
end
function scan_deps!(stack, could_be_cycle, cycles, pkg, dmap)
    push!(stack, pkg)
    cycle = nothing
    for dep in dmap[pkg]
        if dep in stack
            # Created fresh cycle
            cycle′ = stack[findlast(==(dep), stack):end]
            if cycle === nothing || length(cycle′) < length(cycle)
                cycle = cycle′ # try to report smallest cycle possible
            end
        elseif scan_pkg!(stack, could_be_cycle, cycles, dep, dmap)
            # Reaches an existing cycle
            could_be_cycle[pkg] = true
            pop!(stack)
            return true
        end
    end
    pop!(stack)
    if cycle !== nothing
        push!(cycles, cycle)
        could_be_cycle[pkg] = true
        return true
    end
    could_be_cycle[pkg] = false
    return false
end

```
-/
/- The mutable arguments of `scan_pkg!`/`scan_deps!`. -/
structure ScanState (Dict : Type → Type → Type) where
  stack : List PkgId
  could_be_cycle : Dict PkgId Bool
  cycles : List (List PkgId)

mutual
/-- `scan_pkg!(stack, could_be_cycle, cycles, pkg, dmap)`. -/
def scan_pkg [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (D : DictOps Dict)
    (dmap : Dict PkgId (List PkgId)) (st : ScanState Dict) (pkg : PkgId) : m (Bool × ScanState Dict) := do
  match D.get st.could_be_cycle pkg with
  | some b => pure (b, st)
  | none => scan_deps D dmap st pkg
partial_fixpoint

/-- `scan_deps!(stack, could_be_cycle, cycles, pkg, dmap)`. -/
def scan_deps [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (D : DictOps Dict)
    (dmap : Dict PkgId (List PkgId)) (st : ScanState Dict) (pkg : PkgId) : m (Bool × ScanState Dict) := do
  let st := { st with stack := st.stack ++ [pkg] }
  let deps ← getindex D dmap pkg
  scan_deps_loop D dmap pkg none deps st
partial_fixpoint

/-- The `for dep in dmap[pkg]` loop of `scan_deps!` and what follows it. -/
def scan_deps_loop [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (D : DictOps Dict)
    (dmap : Dict PkgId (List PkgId)) (pkg : PkgId) (cycle : Option (List PkgId)) :
    List PkgId → ScanState Dict → m (Bool × ScanState Dict)
  | dep :: rest, st => do
    if st.stack.contains dep then
      -- Created fresh cycle: `stack[findlast(==(dep), stack):end]`
      let i := st.stack.length - 1 - (st.stack.reverse.idxOf dep)
      let cycle' := st.stack.drop i
      let cycle := match cycle with
        | none => some cycle'
        | some c => if cycle'.length < c.length then some cycle' else some c -- try to report smallest cycle possible
      scan_deps_loop D dmap pkg cycle rest st
    else
      let (b, st) ← scan_pkg D dmap st dep
      if b then
        -- Reaches an existing cycle
        return (true, { st with could_be_cycle := D.set st.could_be_cycle pkg true, stack := st.stack.dropLast })
      scan_deps_loop D dmap pkg cycle rest st
  | [], st => do
    let st := { st with stack := st.stack.dropLast }
    match cycle with
    | some c =>
      return (true, { st with cycles := st.cycles ++ [c], could_be_cycle := D.set st.could_be_cycle pkg true })
    | none =>
      return (false, { st with could_be_cycle := D.set st.could_be_cycle pkg false })
partial_fixpoint
end

/--
Julia source: base/precompilation.jl:994-1004 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# restrict to dependencies of given packages
function collect_all_deps(direct_deps, dep, alldeps=Set{Base.PkgId}())
    for _dep in direct_deps[dep]
        if !(_dep in alldeps)
            push!(alldeps, _dep)
            collect_all_deps(direct_deps, _dep, alldeps)
        end
    end
    return alldeps
end

```
-/
/- The `for _dep in direct_deps[dep]` loop of `collect_all_deps`, recursing into each new dependency. -/
def collect_all_deps_loop [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (D : DictOps Dict)
    (direct_deps : Dict PkgId (List PkgId)) : List PkgId → Dict PkgId Unit → m (Dict PkgId Unit)
  | [], alldeps => pure alldeps
  | d :: rest, alldeps => do
    if !setIn D alldeps d then
      let alldeps ← collect_all_deps_loop D direct_deps (← getindex D direct_deps d) (setPush D alldeps d)
      collect_all_deps_loop D direct_deps rest alldeps
    else collect_all_deps_loop D direct_deps rest alldeps
partial_fixpoint

/-- `collect_all_deps(direct_deps, dep, alldeps)`. -/
def collect_all_deps (D : DictOps Dict) [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (direct_deps : Dict PkgId (List PkgId)) (dep : PkgId) (alldeps : Dict PkgId Unit) : m (Dict PkgId Unit) := do
  collect_all_deps_loop D direct_deps (← getindex D direct_deps dep) alldeps

/--
Julia source: base/precompilation.jl:1005-1019 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function visit_indirect_deps!(direct_deps::Dict{PkgId, Vector{PkgId}}, visited::Set{PkgId},
                               node::PkgId, all_deps::Set{PkgId})
    if node in visited
        return
    end
    push!(visited, node)
    for dep in get(Set{PkgId}, direct_deps, node)
        if !(dep in all_deps)
            push!(all_deps, dep)
            visit_indirect_deps!(direct_deps, visited, dep, all_deps)
        end
    end
    return
end

```
-/
/- The `for dep in get(Set{PkgId}, direct_deps, node)` loop of `visit_indirect_deps!`, recursing
into each new dependency; returns `(visited, all_deps)`. -/
def visit_indirect_loop [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (D : DictOps Dict)
    (direct_deps : Dict PkgId (List PkgId)) (visited all_deps : Dict PkgId Unit) :
    List PkgId → m (Dict PkgId Unit × Dict PkgId Unit)
  | [] => pure (visited, all_deps)
  | dep :: rest => do
    if !setIn D all_deps dep then
      let all_deps := setPush D all_deps dep
      -- `visit_indirect_deps!(direct_deps, visited, dep, all_deps)`
      let r ← if setIn D visited dep then pure (visited, all_deps)
        else visit_indirect_loop D direct_deps (setPush D visited dep) all_deps (getD D direct_deps dep [])
      visit_indirect_loop D direct_deps r.1 r.2 rest
    else visit_indirect_loop D direct_deps visited all_deps rest
partial_fixpoint

/-- `visit_indirect_deps!(direct_deps, visited, node, all_deps)`: returns `(visited, all_deps)`. -/
def visit_indirect_deps [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (D : DictOps Dict)
    (direct_deps : Dict PkgId (List PkgId)) (visited : Dict PkgId Unit) (node : PkgId) (all_deps : Dict PkgId Unit) :
    m (Dict PkgId Unit × Dict PkgId Unit) := do
  if setIn D visited node then return (visited, all_deps)
  visit_indirect_loop D direct_deps (setPush D visited node) all_deps (getD D direct_deps node [])

/--
Julia source: base/precompilation.jl:1964-1972 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function _collect_reachable!(pkg_uuids::Set{UUID}, deps::Dict{UUID, Vector{UUID}}, uuid::UUID)
    uuid in pkg_uuids && return
    push!(pkg_uuids, uuid)
    for dep_uuid in get(Vector{UUID}, deps, uuid)
        _collect_reachable!(pkg_uuids, deps, dep_uuid)
    end
end

```
-/
/- The `for dep_uuid in get(Vector{UUID}, deps, uuid)` loop of `_collect_reachable!`, recursing into each
dependency. -/
def collect_reachable_loop [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (D : DictOps Dict)
    (pkg_uuids : Dict UUID Unit) (deps : Dict UUID (List UUID)) : List UUID → m (Dict UUID Unit)
  | [] => pure pkg_uuids
  | d :: rest => do
    -- `_collect_reachable!(pkg_uuids, deps, dep_uuid)`
    let pkg_uuids ← if setIn D pkg_uuids d then pure pkg_uuids
      else collect_reachable_loop D (setPush D pkg_uuids d) deps (getD D deps d [])
    collect_reachable_loop D pkg_uuids deps rest
partial_fixpoint

/-- `_collect_reachable!(pkg_uuids, deps, uuid)`. -/
def _collect_reachable [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (D : DictOps Dict)
    (pkg_uuids : Dict UUID Unit) (deps : Dict UUID (List UUID)) (uuid : UUID) : m (Dict UUID Unit) := do
  if setIn D pkg_uuids uuid then return pkg_uuids
  collect_reachable_loop D (setPush D pkg_uuids uuid) deps (getD D deps uuid [])

/--
Julia source: base/precompilation.jl:1020-1142 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Build dependency graph from an ExplicitEnv.
# Returns a NamedTuple of (direct_deps, ext_to_parent, parent_to_exts, triggers, project_deps, serial_deps).
function build_dep_graph(env::ExplicitEnv, manifest::Bool, _from_loading::Bool, requested_pkgids::Vector{PkgId})
    direct_deps = Dict{PkgId, Vector{PkgId}}()
    parent_to_exts = Dict{PkgId, Vector{PkgId}}()
    ext_to_parent = Dict{PkgId, PkgId}()
    triggers = Dict{PkgId, Vector{PkgId}}()

    # Determine which packages to consider for precompilation by walking
    # transitive dependencies from the appropriate roots.
    # `manifest` controls the scope: workspace_deps (all members) vs project_deps (current project).
    root_uuids = manifest ? keys(env.workspace_deps) : values(env.project_deps)
    pkg_uuids = Set{UUID}()
    for uuid in root_uuids
        _collect_reachable!(pkg_uuids, env.deps, uuid)
    end

    for dep in pkg_uuids
        haskey(env.deps, dep) || continue
        pkg = PkgId(dep, env.names[dep])
        Base.in_sysimage(pkg) && continue
        deps = [PkgId(x, env.names[x]) for x in env.deps[dep]]
        direct_deps[pkg] = filter!(!Base.in_sysimage, deps)
        for (ext_name, trigger_uuids) in get(Dict{String, Vector{UUID}}, env.extensions, dep)
            ext_uuid = Base.uuid5(pkg.uuid, ext_name)
            ext = PkgId(ext_uuid, ext_name)
            triggers[ext] = PkgId[pkg]
            all_triggers_available = true
            for trigger_uuid in trigger_uuids
                trigger_name = PkgId(trigger_uuid, env.names[trigger_uuid])
                if trigger_uuid in pkg_uuids || Base.in_sysimage(trigger_name)
                    push!(triggers[ext], trigger_name)
                else
                    all_triggers_available = false
                    break
                end
            end
            all_triggers_available || continue
            ext_to_parent[ext] = pkg
            direct_deps[ext] = filter(!Base.in_sysimage, triggers[ext])
            if !haskey(parent_to_exts, pkg)
                parent_to_exts[pkg] = PkgId[ext]
            else
                push!(parent_to_exts[pkg], ext)
            end
        end
    end

    project_deps = PkgId[]
    if manifest
        for (uuid, name) in env.workspace_deps
            push!(project_deps, PkgId(uuid, name))
        end
    else
        for (name, uuid) in env.project_deps
            push!(project_deps, PkgId(uuid, name))
        end
    end
    filter!(!Base.in_sysimage, project_deps)
    # consider exts of project deps to be project deps so that errors are reported
    append!(project_deps, keys(filter(d -> last(d) in project_deps, ext_to_parent)))

    # An extension effectively depends on another extension if it has a strict superset of its triggers
    for ext_a in keys(ext_to_parent)
        for ext_b in keys(ext_to_parent)
            if triggers[ext_a] ⊋ triggers[ext_b]
                push!(triggers[ext_a], ext_b)
                push!(direct_deps[ext_a], ext_b)
            end
        end
    end

    # A package depends on an extension if it (indirectly) depends on all extension triggers
    # Iterate to a fixed point because adding an extension edge (e.g. ExtA → TopPkg)
    # may cause another extension (e.g. ExtAB, which depends on ExtA) to become
    # loadable in TopPkg on the next iteration.
    changed = true
    while changed
        changed = false
        indirect_deps = Dict{PkgId, Set{PkgId}}()
        for package in keys(direct_deps)
            all_deps = Set{PkgId}()
            visited = Set{PkgId}()
            visit_indirect_deps!(direct_deps, visited, package, all_deps)
            indirect_deps[package] = all_deps
        end
        for ext in keys(ext_to_parent)
            ext_loadable_in_pkg = Dict{PkgId,Bool}()
            for pkg in keys(direct_deps)
                is_trigger = in(pkg, direct_deps[ext])
                is_extension = in(pkg, keys(ext_to_parent))
                has_triggers = issubset(direct_deps[ext], indirect_deps[pkg])
                ext_loadable_in_pkg[pkg] = !is_extension && has_triggers && !is_trigger
            end
            for (pkg, ext_loadable) in ext_loadable_in_pkg
                if ext_loadable && !any((dep)->ext_loadable_in_pkg[dep], direct_deps[pkg])
                    if ext ∉ direct_deps[pkg]
                        # add an edge if the extension is loadable by pkg, and was not loadable in any
                        # of the pkg's dependencies
                        push!(direct_deps[pkg], ext)
                        changed = true
                    end
                end
            end
        end
    end

    serial_deps = PkgId[]
    if _from_loading
        for pkgid in requested_pkgids
            pkgid === nothing && continue
            if !haskey(direct_deps, pkgid)
                @debug "precompile: package `$(pkgid)` is outside of the environment, so adding as single package serial job"
                direct_deps[pkgid] = PkgId[]
                push!(project_deps, pkgid)
                push!(serial_deps, pkgid)
            end
        end
    end

    return (; direct_deps, ext_to_parent, parent_to_exts, triggers, project_deps, serial_deps)
end

```
-/
/- Callees of `build_dep_graph`. -/
structure GraphOps (n : Type → Type) where
  /-- `Base.in_sysimage(pkg)`. -/
  in_sysimage : PkgId → n Bool
  /-- `Base.uuid5(ns, name)` (the `base/loading.jl` model). -/
  uuid5 : UUID → Bytes → UUID
  /-- `@debug "precompile: package `$(pkgid)` is outside of the environment, so adding as single
  package serial job"`. -/
  debugOutside : PkgId → n Unit

/-- The named tuple returned by `build_dep_graph`. -/
structure DepGraph (Dict : Type → Type → Type) where
  direct_deps : Dict PkgId (List PkgId)
  ext_to_parent : Dict PkgId PkgId
  parent_to_exts : Dict PkgId (List PkgId)
  triggers : Dict PkgId (List PkgId)
  project_deps : List PkgId
  serial_deps : List PkgId

/-- `a ⊋ b` of vectors: `Set(b) ⊊ Set(a)`. -/
def supsetStrict (a b : List PkgId) : Bool :=
  a.eraseDups.length > b.eraseDups.length && b.all (a.contains ·)

/-- One pass of the `while changed` loop that adds package → extension edges. -/
def ext_edges_pass [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (D : DictOps Dict)
    (ext_to_parent : Dict PkgId PkgId) (direct_deps : Dict PkgId (List PkgId)) :
    m (Dict PkgId (List PkgId) × Bool) := do
  let mut changed := false
  let mut indirect_deps : Dict PkgId (Dict PkgId Unit) := D.empty
  for package in D.keys direct_deps do
    let (_, all_deps) ← visit_indirect_deps D direct_deps D.empty package D.empty
    indirect_deps := D.set indirect_deps package all_deps
  let mut direct_deps := direct_deps
  for ext in D.keys ext_to_parent do
    let mut ext_loadable_in_pkg : Dict PkgId Bool := D.empty
    for pkg in D.keys direct_deps do
      let ext_deps ← getindex D direct_deps ext
      let is_trigger := ext_deps.contains pkg
      let is_extension := haskey D ext_to_parent pkg
      let ind ← getindex D indirect_deps pkg
      let has_triggers := ext_deps.all (setIn D ind ·)
      ext_loadable_in_pkg := D.set ext_loadable_in_pkg pkg (!is_extension && has_triggers && !is_trigger)
    for pkg in D.keys ext_loadable_in_pkg do
      let ext_loadable ← getindex D ext_loadable_in_pkg pkg
      if ext_loadable then
        let pdeps ← getindex D direct_deps pkg
        let mut anyLoadable := false
        for dep in pdeps do
          if ← getindex D ext_loadable_in_pkg dep then
            anyLoadable := true
            break
        if !anyLoadable then
          if !pdeps.contains ext then
            -- add an edge if the extension is loadable by pkg, and was not loadable in any
            -- of the pkg's dependencies
            direct_deps := D.set direct_deps pkg (pdeps ++ [ext])
            changed := true
  return (direct_deps, changed)

/-- `while changed ... end`. -/
def ext_edges_loop [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (D : DictOps Dict)
    (ext_to_parent : Dict PkgId PkgId) (direct_deps : Dict PkgId (List PkgId)) : m (Dict PkgId (List PkgId)) := do
  let (direct_deps, changed) ← ext_edges_pass D ext_to_parent direct_deps
  if changed then ext_edges_loop D ext_to_parent direct_deps else pure direct_deps
partial_fixpoint

/-- `build_dep_graph(env, manifest, _from_loading, requested_pkgids)`. -/
def build_dep_graph [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] {SHA1 : Type} (D : DictOps Dict)
    (g : GraphOps m) (env : ExplicitEnv Dict SHA1) (manifest _from_loading : Bool) (requested_pkgids : List PkgId) :
    m (DepGraph Dict) := do
  let mut direct_deps : Dict PkgId (List PkgId) := D.empty
  let mut parent_to_exts : Dict PkgId (List PkgId) := D.empty
  let mut ext_to_parent : Dict PkgId PkgId := D.empty
  let mut triggers : Dict PkgId (List PkgId) := D.empty
  -- Determine which packages to consider for precompilation by walking
  -- transitive dependencies from the appropriate roots.
  let root_uuids ← if manifest then pure (D.keys env.workspace_deps)
    else (D.keys env.project_deps).mapM fun k => getindex D env.project_deps k
  let mut pkg_uuids : Dict UUID Unit := D.empty
  for uuid in root_uuids do
    pkg_uuids ← _collect_reachable D pkg_uuids env.deps uuid
  for dep in D.keys pkg_uuids do
    if !haskey D env.deps dep then continue
    let pkg := mkPkgId dep (← getindex D env.names dep)
    if ← g.in_sysimage pkg then continue
    let deps ← (← getindex D env.deps dep).mapM fun x => do return mkPkgId x (← getindex D env.names x)
    direct_deps := D.set direct_deps pkg (← deps.filterM fun d => do return !(← g.in_sysimage d))
    let exts := getD D env.extensions dep D.empty
    for ext_name in D.keys exts do
      let trigger_uuids ← getindex D exts ext_name
      let ext_uuid := g.uuid5 (← match pkg.uuid with
        | some u => pure u
        | none => throwP .methodError) ext_name
      let ext : PkgId := ⟨some ext_uuid, ext_name⟩
      triggers := D.set triggers ext [pkg]
      let mut all_triggers_available := true
      for trigger_uuid in trigger_uuids do
        let trigger_name := mkPkgId trigger_uuid (← getindex D env.names trigger_uuid)
        if setIn D pkg_uuids trigger_uuid || (← g.in_sysimage trigger_name) then
          triggers := D.set triggers ext ((← getindex D triggers ext) ++ [trigger_name])
        else
          all_triggers_available := false
          break
      if !all_triggers_available then continue
      ext_to_parent := D.set ext_to_parent ext pkg
      direct_deps := D.set direct_deps ext (← (← getindex D triggers ext).filterM fun d => do return !(← g.in_sysimage d))
      if !haskey D parent_to_exts pkg then
        parent_to_exts := D.set parent_to_exts pkg [ext]
      else
        parent_to_exts := D.set parent_to_exts pkg ((← getindex D parent_to_exts pkg) ++ [ext])
  let mut project_deps : List PkgId := []
  if manifest then
    for uuid in D.keys env.workspace_deps do
      project_deps := project_deps ++ [mkPkgId uuid (← getindex D env.workspace_deps uuid)]
  else
    for name in D.keys env.project_deps do
      project_deps := project_deps ++ [mkPkgId (← getindex D env.project_deps name) name]
  project_deps ← project_deps.filterM fun d => do return !(← g.in_sysimage d)
  -- consider exts of project deps to be project deps so that errors are reported
  let pd := project_deps
  project_deps := project_deps ++ D.keys (filterDict D (fun _ parent => pd.contains parent) ext_to_parent)
  -- An extension effectively depends on another extension if it has a strict superset of its triggers
  for ext_a in D.keys ext_to_parent do
    for ext_b in D.keys ext_to_parent do
      if supsetStrict (← getindex D triggers ext_a) (← getindex D triggers ext_b) then
        triggers := D.set triggers ext_a ((← getindex D triggers ext_a) ++ [ext_b])
        direct_deps := D.set direct_deps ext_a ((← getindex D direct_deps ext_a) ++ [ext_b])
  -- A package depends on an extension if it (indirectly) depends on all extension triggers
  direct_deps ← ext_edges_loop D ext_to_parent direct_deps
  let mut serial_deps : List PkgId := []
  if _from_loading then
    for pkgid in requested_pkgids do
      if !haskey D direct_deps pkgid then
        -- `pkgid === nothing && continue` cannot fire: the vector holds `PkgId`s only
        g.debugOutside pkgid
        direct_deps := D.set direct_deps pkgid []
        project_deps := project_deps ++ [pkgid]
        serial_deps := serial_deps ++ [pkgid]
  return ⟨direct_deps, ext_to_parent, parent_to_exts, triggers, project_deps, serial_deps⟩

/--
Julia source: base/precompilation.jl:1143-1165 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Detect circular dependencies and notify their Events so waiting tasks can skip them.
# Returns the list of packages involved in or dependent on cycles.
function detect_circular_deps!(direct_deps, serial_deps, was_processed, io, ext_to_parent)
    cycles = Vector{PkgId}[]
    could_be_cycle = Dict{PkgId, Bool}()
    stack = PkgId[]
    circular_deps = PkgId[]
    for pkg in keys(direct_deps)
        @assert isempty(stack)
        pkg in serial_deps && continue
        if scan_pkg!(stack, could_be_cycle, cycles, pkg, direct_deps)
            push!(circular_deps, pkg)
            for (pkg_config, evt) in was_processed
                pkg_config[1] == pkg && notify(evt)
            end
        end
    end
    if !isempty(circular_deps)
        printpkgstyle(io, :Warning, excluded_circular_deps_explanation(io, ext_to_parent, circular_deps, cycles), color=Base.warn_color())
    end
    return circular_deps
end

```
-/
/- `detect_circular_deps!(direct_deps, serial_deps, was_processed, io, ext_to_parent)`:
`notifyProcessed pkg` notifies the event of every `(pkg_config, evt)` in `was_processed` with
`pkg_config[1] == pkg`, and `warnCycles msg` is
`printpkgstyle(io, :Warning, msg, color=Base.warn_color())`. -/
def detect_circular_deps [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (D : DictOps Dict)
    (direct_deps : Dict PkgId (List PkgId)) (serial_deps : List PkgId) (notifyProcessed : PkgId → m Unit)
    (hascolor : m Bool) (warnCycles : Bytes → m Unit) (ext_to_parent : Dict PkgId PkgId) : m (List PkgId) := do
  let mut st : ScanState Dict := ⟨[], D.empty, []⟩
  let mut circular_deps : List PkgId := []
  for pkg in D.keys direct_deps do
    if !st.stack.isEmpty then throwP .assertionError
    if serial_deps.contains pkg then continue
    let (b, st') ← scan_pkg D direct_deps st pkg
    st := st'
    if b then
      circular_deps := circular_deps ++ [pkg]
      notifyProcessed pkg
  if !circular_deps.isEmpty then
    warnCycles (← excluded_circular_deps_explanation D hascolor ext_to_parent circular_deps st.cycles)
  return circular_deps

/--
Julia source: base/precompilation.jl:1166-1191 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Filter the dependency graph to only include requested packages and their transitive deps.
# Returns true if the graph became empty (caller should return early).
function filter_dep_graph!(direct_deps, pkg_names, ext_to_parent, requested_pkgids)
    isempty(pkg_names) && return false
    keep = Set{PkgId}()
    for dep_pkgid in keys(direct_deps)
        if dep_pkgid.name in pkg_names
            push!(keep, dep_pkgid)
            collect_all_deps(direct_deps, dep_pkgid, keep)
        end
    end
    for requested_pkgid in requested_pkgids
        if haskey(direct_deps, requested_pkgid)
            push!(keep, requested_pkgid)
            collect_all_deps(direct_deps, requested_pkgid, keep)
        end
    end
    for ext in keys(ext_to_parent)
        if issubset(collect_all_deps(direct_deps, ext), keep)
            push!(keep, ext)
        end
    end
    filter!(d->in(first(d), keep), direct_deps)
    return isempty(direct_deps)
end

```
-/
/- `filter_dep_graph!(direct_deps, pkg_names, ext_to_parent, requested_pkgids)`: returns the
filtered `direct_deps` and whether it became empty. -/
def filter_dep_graph [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (D : DictOps Dict)
    (direct_deps : Dict PkgId (List PkgId)) (pkg_names : List Bytes) (ext_to_parent : Dict PkgId PkgId)
    (requested_pkgids : List PkgId) : m (Dict PkgId (List PkgId) × Bool) := do
  if pkg_names.isEmpty then return (direct_deps, false)
  let mut keep : Dict PkgId Unit := D.empty
  for dep_pkgid in D.keys direct_deps do
    if pkg_names.contains dep_pkgid.name then
      keep := setPush D keep dep_pkgid
      keep ← collect_all_deps D direct_deps dep_pkgid keep
  for requested_pkgid in requested_pkgids do
    if haskey D direct_deps requested_pkgid then
      keep := setPush D keep requested_pkgid
      keep ← collect_all_deps D direct_deps requested_pkgid keep
  for ext in D.keys ext_to_parent do
    let all ← collect_all_deps D direct_deps ext D.empty
    if (D.keys all).all (setIn D keep ·) then
      keep := setPush D keep ext
  let k := keep
  let direct_deps := filterBang D (fun p _ => setIn D k p) direct_deps
  return (direct_deps, (D.keys direct_deps).isEmpty)

end graph

/-! ## Session state and orchestration

The remaining methods coordinate concurrent tasks over shared mutable records. Runtime objects
(streams, locks, conditions, events, tasks, channels, buffers, pipes, timers, modules) are opaque
handles whose types are collected in `Rt`; every runtime call on them is an operation of `Ops`.
The mutable records `PrecompileSession` and `BackgroundPrecompileState` (the global `BG`) are
reached through `Ops.sget`/`Ops.smodify` and `Ops.bgget`/`Ops.bgmodify`: a field read `s.f` is
`(← o.sget s).f` and a field write `s.f = v` is `o.smodify s fun st => { st with f := v }`, so
each read and write happens where Julia performs it. A `PrecompileJob` is a mutable object stored
in `s.jobs` and never replaced there (`get!` only inserts a missing key), so a write to a job's field
is a write to its entry in `s.jobs`.
-/

/-- `string(n)` of an integer. -/
def istr {t : IntTy} (n : JInt t) : Bytes := lit (toString n.val)

/-- An `Int` literal. -/
def ji (n : Int) : JInt64 := JInt.wrap .i64 n

/-- Each element once, keeping first occurrences (the `_grow_filter!`/`_shrink_filter!` of
`base/array.jl`). -/
def uniq {α : Type} [BEq α] (l : List α) : List α :=
  l.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- `union!(v, itr)` of vectors (`base/array.jl`): `v` without repeats, then each element of `itr`
not yet present. -/
def vunion {α : Type} [BEq α] (v itr : List α) : List α := uniq (v ++ itr)

/-- `setdiff(itr, s)` (`base/array.jl`): the elements of `itr` not in `s`, each once, in order. -/
def vsetdiff {α : Type} [BEq α] (itr : List α) (inS : α → Bool) : List α := uniq (itr.filter (!inS ·))

/-- `isless` of `String`s: byte-wise lexicographic order. -/
def bytesLe : Bytes → Bytes → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a < b then true else if a == b then bytesLe as bs else false

/-- `sort!(v)` of a vector of `String`s. -/
def sortBytes (l : List Bytes) : List Bytes := l.mergeSort bytesLe

/-- `join(v, delim, last)`. -/
def joinLast (delim last : Bytes) : List Bytes → Bytes
  | [] => []
  | [a] => a
  | [a, b] => a ++ last ++ b
  | a :: rest => a ++ delim ++ joinLast delim last rest

/-- `join(v, delim)`. -/
def joinB (delim : Bytes) (l : List Bytes) : Bytes := delim.intercalate l

abbrev F64 := JuliaLean.base.float.FV .f64
def fl (bits : Nat) : F64 := JuliaLean.Promotion.Fl.ofBits bits
/-! `TimingFormatOps` binds the formatter to the installed Float64 rounding and Ryu string
models, String `lpad`, `length`, and `findfirst` models, and the PCRE-backed `match` model. -/
structure TimingFormatOps (m : Type → Type) where
  /-- `round(x; digits)` from the installed `floatfuncs.round_Real` model. -/
  roundFloatDigits : F64 → JInt64 → m F64
  /-- `string(::Float64)` from the installed `ryu.Ryu.string64` model. -/
  stringFloat64 : F64 → m Bytes
  /-- `lpad(::String, ::Integer)` from the installed `strings.util.lpadWrapper` model. -/
  lpadString : Bytes → JInt64 → m Bytes
  /-- `length(::String)` from the installed `strings.basic` model. -/
  stringLength : Bytes → m JInt64
  /-- `findfirst('.', s)` from the installed `strings.search` model; indices are Julia's 1-based
  string indices. -/
  findFirstDot : Bytes → m (Option JInt64)
  /-- `match(r"^(include|compilation|deps)_ns=(\d+)$", token)` from the PCRE-backed regex model;
  the pair contains capture 1 and capture 2. -/
  matchIncludeNs : Bytes → m (Option (Bytes × Bytes))
  /-- `match(r"^methods=(\d+)$", token)` from the PCRE-backed regex model; returns capture 1. -/
  matchMethods : Bytes → m (Option Bytes)

/--
Julia source: base/precompilation.jl:382-382 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
timing_string(t) = string(lpad(round(t, digits = 1), 6), " s")
```
-/
-- Source: base/precompilation.jl:382 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def timing_string_selected {m : Type → Type} [Monad m] {T Rounded Padded Result : Type}
    (roundDigits : T → JInt64 → m Rounded)
    (lpad : Rounded → JInt64 → m Padded)
    (string : Padded → Bytes → m Result) (t : T) : m Result := do
  let rounded ← roundDigits t (ji 1)
  let padded ← lpad rounded (ji 6)
  string padded (lit " s")

def timing_string {m : Type → Type} [Monad m] (ops : TimingFormatOps m) (t : F64) : m Bytes :=
  timing_string_selected ops.roundFloatDigits
    (fun value width => do ops.lpadString (← ops.stringFloat64 value) width)
    (fun padded suffix => pure (padded ++ suffix)) t

/--
Julia source: base/precompilation.jl:417-417 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    dim(s, isz) = isz ? color_string(s, :light_black, hascolor) : s
```
-/
def formatVerboseTimingDim {m : Type → Type} [Monad m] [MonadExceptOf PError m]
    (s : Bytes) (isz hascolor : Bool) : m Bytes :=
  if isz then color_string s (.symbol "light_black") hascolor else pure s

/--
Julia source: base/precompilation.jl:418-427 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function col(x)
        s = string(round(x, digits = 2))
        dot = findfirst('.', s)
        if dot === nothing
            s *= ".00"
        elseif length(s) - dot == 1
            s *= "0"
        end
        dim(string(lpad(s, 6), "s"), x < 0.005)
    end
```
-/
def formatVerboseTimingCol {m : Type → Type} [Monad m] [MonadExceptOf PError m]
    (ops : TimingFormatOps m) (x : F64) (hascolor : Bool) : m Bytes := do
  let rounded ← ops.roundFloatDigits x (ji 2)
  let rendered ← ops.stringFloat64 rounded
  let dot ← ops.findFirstDot rendered
  let rendered ← match dot with
    | none => pure (rendered ++ lit ".00")
    | some dot => do
        let length ← ops.stringLength rendered
        if length.val - dot.val == 1 then pure (rendered ++ lit "0") else pure rendered
  let padded ← ops.lpadString rendered (ji 6)
  formatVerboseTimingDim (padded ++ lit "s")
    (JuliaLean.base.float.lt_float x (JuliaLean.Promotion.Fl.ofBits 0x3F747AE147AE147B)) hascolor

/--
Julia source: base/precompilation.jl:383-438 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# Parse the marker payload emitted by `Base.include_package_for_output` and
# format an inline breakdown (include / compilation / image-gen seconds,
# cache file size and cached method count) appended to the per-package timing
# line in verbose mode. Column labels are emitted once via
# `format_verbose_timing_header`. Returns an empty string if the payload is
# missing or unparsable.
function format_verbose_timing(payload::AbstractString, total_seconds::Float64, cache_bytes::Int, peak_rss_bytes::UInt64, hascolor::Bool)
    isempty(payload) && return ""
    include_ns = compilation_ns = deps_ns = UInt64(0)
    methods = 0
    seen = false
    for tok in split(payload)
        m = match(r"^(include|compilation|deps)_ns=(\d+)$", tok)
        if m !== nothing
            v = parse(UInt64, m.captures[2])
            tag = m.captures[1]
            if tag == "include"
                include_ns = v; seen = true
            elseif tag == "compilation"
                compilation_ns = v
            else
                deps_ns = v
            end
            continue
        end
        m = match(r"^methods=(\d+)$", tok)
        m === nothing || (methods = parse(Int, m.captures[1]))
    end
    seen || return ""
    inc_s = include_ns / 1e9
    comp_s = compilation_ns / 1e9
    deps_s = deps_ns / 1e9
    img_s = max(total_seconds - inc_s, 0.0)
    dim(s, isz) = isz ? color_string(s, :light_black, hascolor) : s
    function col(x)
        s = string(round(x, digits = 2))
        dot = findfirst('.', s)
        if dot === nothing
            s *= ".00"
        elseif length(s) - dot == 1
            s *= "0"
        end
        dim(string(lpad(s, 6), "s"), x < 0.005)
    end
    cache_mb = cache_bytes / 1024^2
    cache_str = cache_bytes <= 0 ? dim(lpad("-", 8), true) :
                                   string(lpad(round(cache_mb, digits = 1), 6), "MB")
    peak_mb = peak_rss_bytes / 1024^2
    peak_str = peak_rss_bytes == 0 ? dim(lpad("-", 7), true) :
                                     string(lpad(round(Int, peak_mb), 5), "MB")
    methods_str = dim(lpad(methods, 7), methods == 0)
    bar = " │ "
    return string(bar, col(inc_s), "  ", col(deps_s), "  ", col(comp_s),
                  bar, methods_str, "  ", col(img_s), "  ", cache_str, "  ", peak_str)
end
```
-/
def format_verbose_timing {m : Type → Type} [Monad m] [MonadExceptOf PError m]
    (ops : TimingFormatOps m) (splitWS : Bytes → List Bytes)
    (parseUInt64 : Bytes → m (JInt .u64)) (parseInt : Bytes → m JInt64)
    (roundInt : F64 → m JInt64) (maxF : F64 → F64 → F64)
    (payload : Bytes) (totalSeconds : F64) (cacheBytes : JInt64)
    (peakRssBytes : JInt .u64) (hascolor : Bool) : m Bytes := do
  if payload.isEmpty then return []
  let mut includeNs := JInt.wrap .u64 0
  let mut compilationNs := JInt.wrap .u64 0
  let mut depsNs := JInt.wrap .u64 0
  let mut methods := JInt.wrap .i64 0
  let mut seen := false
  for token in splitWS payload do
    match ← ops.matchIncludeNs token with
    | some (tag, value) =>
        let parsed ← parseUInt64 value
        if tag == lit "include" then
          includeNs := parsed
          seen := true
        else if tag == lit "compilation" then
          compilationNs := parsed
        else
          depsNs := parsed
    | none =>
        match ← ops.matchMethods token with
        | some value => methods ← parseInt value
        | none => pure ()
  if !seen then return []
  let billion := fl 0x41CDCD6500000000
  let incS := JuliaLean.base.float.div_float (JuliaLean.base.float.uitofp .f64 includeNs) billion
  let compS := JuliaLean.base.float.div_float (JuliaLean.base.float.uitofp .f64 compilationNs) billion
  let depsS := JuliaLean.base.float.div_float (JuliaLean.base.float.uitofp .f64 depsNs) billion
  let imgS := maxF (JuliaLean.base.float.sub_float totalSeconds incS) (fl 0)
  let includeColumn ← formatVerboseTimingCol ops incS hascolor
  let depsColumn ← formatVerboseTimingCol ops depsS hascolor
  let compColumn ← formatVerboseTimingCol ops compS hascolor
  let imgColumn ← formatVerboseTimingCol ops imgS hascolor
  let cacheMb := JuliaLean.base.float.div_float
    (JuliaLean.base.float.floatOfInt .f64 cacheBytes) (fl 0x4130000000000000)
  let cacheString ← if cacheBytes.val ≤ 0 then do
    let padded ← ops.lpadString (lit "-") (ji 8)
    formatVerboseTimingDim padded true hascolor
  else do
    let rounded ← ops.roundFloatDigits cacheMb (ji 1)
    let rendered ← ops.stringFloat64 rounded
    let padded ← ops.lpadString rendered (ji 6)
    pure (padded ++ lit "MB")
  let peakMb := JuliaLean.base.float.div_float
    (JuliaLean.base.float.uitofp .f64 peakRssBytes) (fl 0x4130000000000000)
  let peakString ← if peakRssBytes.val == 0 then do
    let padded ← ops.lpadString (lit "-") (ji 7)
    formatVerboseTimingDim padded true hascolor
  else do
    let rounded ← roundInt peakMb
    let padded ← ops.lpadString (istr rounded) (ji 5)
    pure (padded ++ lit "MB")
  let methodsPadded ← ops.lpadString (istr methods) (ji 7)
  let methodsString ← formatVerboseTimingDim methodsPadded (methods.val == 0) hascolor
  let bar := lit " │ "
  return bar ++ includeColumn ++ lit "  " ++ depsColumn ++ lit "  " ++ compColumn ++
    bar ++ methodsString ++ lit "  " ++ imgColumn ++ lit "  " ++ cacheString ++
    lit "  " ++ peakString

/-- The `PkgId(uuid, name)` constructor applied to a key of an environment's tables. -/
def pkgOf (u : UUID) (name : Bytes) : PkgId := mkPkgId u name

/--
Julia source: base/precompilation.jl:212-345 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# A request to do precompilation work, either in a new session or merged into a running one.
struct PrecompileRequest
    pkgs::Union{Vector{String}, Vector{PkgId}}
    internal_call::Bool
    strict::Bool
    warn_loaded::Bool
    timing::Bool
    _from_loading::Bool
    reasons::Dict{Symbol,Int}
    configs::Vector{Config}
    io::IOContext
    fancyprint::Bool
    manifest::Bool
    ignore_loaded::Bool
    detachable::Bool
    skip_dependents::Bool
    force::Bool
    force_stdlibs::Bool
    result::Channel{Any}
end

# Shared mutable state for a precompilation session.
Base.@kwdef mutable struct PrecompileSession
    # Configuration (set once, read-only after construction)
    configs::Vector{Config}
    io::IOContext
    logio::IOContext
    logcalls::Union{Nothing, CoreLogging.LogLevel}
    fancyprint::Bool
    brief::Bool # only the header, reasons, failures and summary, without a line per package
    hascolor::Bool
    warn_loaded::Bool
    ignore_loaded::Bool
    internal_call::Bool
    strict::Bool
    _from_loading::Bool
    skip_dependents::Bool
    force::Bool
    force_stdlibs::Bool
    reasons::Dict{Symbol,Int} = Dict{Symbol,Int}() # why loading is precompiling, from its cache checks
    header_printed::Bool = false
    explained_pkgids::Set{PkgId} = Set{PkgId}() # requested packages whose reasons were explained
    explained_conflicts::Vector{String} = String[]
    flags_explained::Bool = false
    time_start::UInt64
    print_lock::ReentrantLock
    parallel_limiter::WorkerLimiter
    num_tasks::Int
    start_loaded_modules::Set{PkgId}
    requested_pkgids::Vector{PkgId}
    requested_all::Bool = false  # requested_pkgids was defaulted to the project deps

    # Dependency graph (built by setup, extended by drainer)
    direct_deps::Dict{PkgId, Vector{PkgId}}
    ext_to_parent::Dict{PkgId, PkgId}
    parent_to_exts::Dict{PkgId, Vector{PkgId}}
    triggers::Dict{PkgId, Vector{PkgId}}
    project_deps::Vector{PkgId}
    serial_deps::Vector{PkgId}
    circular_deps::Vector{PkgId}

    # Progress counters and flags
    n_done::Int                            = 0
    n_already_precomp::Int                 = 0
    n_loaded::Int                          = 0
    loaded_pkgs::Vector{PkgId}             = PkgId[]
    n_total::Int
    n_batches::Int                         = 1
    interrupted::Bool                      = false
    canceled::Bool                         = false
    interrupted_or_done::Bool              = false
    printloop_should_exit::Bool
    target::String
    pkg_liveprinted::Union{Nothing, PkgId} = nothing

    # Per-package tracking
    jobs::Dict{PkgConfig, PrecompileJob}                  = Dict{PkgConfig,PrecompileJob}()
    was_processed::Dict{PkgConfig, Base.Event}
    stale_cache::Dict{StaleCacheKey, Bool}         = Dict{StaleCacheKey,Bool}()
    cachepath_cache::Dict{PkgId, Vector{String}}   = Dict{PkgId,Vector{String}}()
    # cache files accepted without reading them, because their checksums passed earlier in this process
    unverified::Set{String}                        = Set{String}()
    pkg_queue::Vector{PkgConfig}                   = PkgConfig[]
    prev_cpu_times::Dict{Int32, UInt64}            = Dict{Int32,UInt64}()

    # Synchronization
    first_started::Base.Event                      = Base.Event()
    cache_lock::ReentrantLock                      = ReentrantLock()

    # Task tracking
    tasks::Vector{Task}                            = Task[]
    injected_tasks::Vector{Task}                   = Task[]
    result_waiters::Vector{Task}                   = Task[]
end

# Background precompilation state
#
# Lock ordering (outermost first): BG.lock → BG.pkg_done → BG.task_done
# All three have independent ReentrantLocks. Always acquire in this order to avoid deadlocks.
mutable struct BackgroundPrecompileState
    task::Union{Nothing, Task}
    interrupt_requested::Bool
    cancel_requested::Bool
    monitoring::Bool
    completed_at::Union{Nothing, Float64}
    result::Union{Nothing, String}
    return_value::Any
    exception::Any
    lock::ReentrantLock
    task_done::Threads.Condition
    signal_channels::Vector{Channel{Int32}}  # channels for broadcasting signals to all subprocesses
    pending_pkgids::Dict{PkgId, Int}  # packages queued and currently being precompiled (refcount for multi-config)
    completed_pkgids::Set{PkgId}  # packages that have finished precompiling (for fast-finish detection)
    pkg_done::Threads.Condition  # notified when a package finishes precompiling
    work_channel::Channel{PrecompileRequest}  # channel for injecting requests into running task
    verbose::Bool  # show PIDs and CPU% for each worker
    detachable::Bool  # whether the monitor can be detached
    confirming::Symbol  # :none, :cancel, or :info — action awaiting Enter to confirm
    confirm_deadline::Float64  # time() deadline for confirmation
    info_requested::Bool  # whether SIGINFO/SIGUSR1 has been broadcast at least once
    key_listening::Bool  # whether a key listener task is currently consuming stdin
    foreground_monitors::Int  # number of foreground tasks currently monitoring the run
    key_controls::Bool  # whether the current monitor offers key controls, set before its listener starts
end
Base.lock(f, bg::BackgroundPrecompileState) = lock(f, bg.lock)
Base.lock(bg::BackgroundPrecompileState) = lock(bg.lock)
Base.unlock(bg::BackgroundPrecompileState) = unlock(bg.lock)

const BG = BackgroundPrecompileState(nothing, false, false, false, nothing, nothing, nothing, nothing, ReentrantLock(), Threads.Condition(), Channel{Int32}[], Dict{PkgId, Int}(), Set{PkgId}(), Threads.Condition(), Channel{PrecompileRequest}(Inf), false, false, :none, 0.0, false, false, 0, false)

# Serializes the inject-vs-launch decision in `_precompilepkgs` with the launch
# itself. Lock ordering: acquired before (outside) BG.lock, never while holding it.
const launch_lock = ReentrantLock()

```
-/
/-
The runtime types. `Stream` is `IO`, `IOC` an `IOContext{IO}`, `Lock` a `ReentrantLock`, `Cond` a
`Threads.Condition`, `Ev` a `Base.Event`, `Tsk` a `Task`, `Buf` an `IOBuffer`, `SCK` a
`StaleCacheKey`, `SigChan` a `Channel{Int32}`, `ResChan` the `Channel{Any}` of a request, `ReqChan` a
`Channel{PrecompileRequest}`, `Sess` a `PrecompileSession` object, `Spec` a `Base.PkgLoadSpec`,
`Mod` a `Module`, `Version` a `VersionNumber`, `Pipe` a `Pipe`, `Tmr` a `Timer`, `A` a TOML value,
`SHA1` a `Base.SHA1`, `P` a `Ptr{UInt8}`, `Prio` a `SchedulePriorities`, `PidChan` a `Channel{Int32}`
carrying a worker's process id, `BRef` a `Ref{Bool}`, `U8Vec` a `Vector{UInt8}`, `Term` a
`Base.Terminals.TTYTerminal`, and `Dict` Julia's `Dict`.
-/
structure Rt where
  Dict : Type → Type → Type
  Cmd : Type
  CF : Type
  Stream : Type
  IOC : Type
  LogLevel : Type
  Lock : Type
  Cond : Type
  Ev : Type
  Tsk : Type
  Buf : Type
  SCK : Type
  SigChan : Type
  ResChan : Type
  ReqChan : Type
  Sess : Type
  Spec : Type
  Mod : Type
  Version : Type
  Pipe : Type
  Tmr : Type
  A : Type
  SHA1 : Type
  P : Type
  Prio : Type
  PidChan : Type
  BRef : Type
  U8Vec : Type
  Term : Type
  cmdBEq : BEq Cmd
  cfBEq : BEq CF
  sckBEq : BEq SCK
  versionBEq : BEq Version
  logLevelBEq : BEq LogLevel

instance (T : Rt) : BEq T.Cmd := T.cmdBEq
instance (T : Rt) : BEq T.CF := T.cfBEq
instance (T : Rt) : BEq T.SCK := T.sckBEq
instance (T : Rt) : BEq T.Version := T.versionBEq
instance (T : Rt) : BEq T.LogLevel := T.logLevelBEq

/-- `Config = Pair{Cmd, Base.CacheFlags}`. -/
abbrev Config (T : Rt) := T.Cmd × T.CF
/-- `PkgConfig = Tuple{PkgId,Config}`. -/
abbrev PkgConfig (T : Rt) := PkgId × Config T

/-- `pkgs::Union{Vector{String}, Vector{PkgId}}`. -/
inductive Pkgs where
  | names (ns : List Bytes)
  | ids (ps : List PkgId)

def Pkgs.length : Pkgs → Nat
  | .names ns => ns.length
  | .ids ps => ps.length

def Pkgs.isEmpty (p : Pkgs) : Bool := p.length == 0

/-- `PrecompileRequest`. -/
structure PrecompileRequest (T : Rt) where
  pkgs : Pkgs
  internal_call : Bool
  strict : Bool
  warn_loaded : Bool
  timing : Bool
  _from_loading : Bool
  reasons : T.Dict Bytes JInt64
  configs : List (Config T)
  io : T.IOC
  fancyprint : Bool
  manifest : Bool
  ignore_loaded : Bool
  detachable : Bool
  skip_dependents : Bool
  force : Bool
  force_stdlibs : Bool
  result : T.ResChan

/-- A value put on a request's `result::Channel{Any}`: the cache paths, or an exception. -/
inductive RequestResult where
  | paths (ps : List Bytes)
  | exc (e : PError)

/-- `PrecompileSession`; the `Base.@kwdef` defaults are written out where it is constructed. -/
structure PrecompileSession (T : Rt) where
  configs : List (Config T)
  io : T.IOC
  logio : T.IOC
  logcalls : Option T.LogLevel
  fancyprint : Bool
  brief : Bool
  hascolor : Bool
  warn_loaded : Bool
  ignore_loaded : Bool
  internal_call : Bool
  strict : Bool
  _from_loading : Bool
  skip_dependents : Bool
  force : Bool
  force_stdlibs : Bool
  reasons : T.Dict Bytes JInt64
  header_printed : Bool
  explained_pkgids : T.Dict PkgId Unit
  explained_conflicts : List Bytes
  flags_explained : Bool
  time_start : JInt .u64
  print_lock : T.Lock
  parallel_limiter : WorkerLimiter T.Cond
  num_tasks : JInt64
  start_loaded_modules : T.Dict PkgId Unit
  requested_pkgids : List PkgId
  requested_all : Bool
  direct_deps : T.Dict PkgId (List PkgId)
  ext_to_parent : T.Dict PkgId PkgId
  parent_to_exts : T.Dict PkgId (List PkgId)
  triggers : T.Dict PkgId (List PkgId)
  project_deps : List PkgId
  serial_deps : List PkgId
  circular_deps : List PkgId
  n_done : JInt64
  n_already_precomp : JInt64
  n_loaded : JInt64
  loaded_pkgs : List PkgId
  n_total : JInt64
  n_batches : JInt64
  interrupted : Bool
  canceled : Bool
  interrupted_or_done : Bool
  printloop_should_exit : Bool
  target : Bytes
  pkg_liveprinted : Option PkgId
  jobs : T.Dict (PkgConfig T) (PrecompileJob T.Buf)
  was_processed : T.Dict (PkgConfig T) T.Ev
  stale_cache : T.Dict T.SCK Bool
  cachepath_cache : T.Dict PkgId (List Bytes)
  unverified : T.Dict Bytes Unit
  pkg_queue : List (PkgConfig T)
  prev_cpu_times : T.Dict (JInt .i32) (JInt .u64)
  first_started : T.Ev
  cache_lock : T.Lock
  tasks : List T.Tsk
  injected_tasks : List T.Tsk
  result_waiters : List T.Tsk

/-- `BackgroundPrecompileState`. `confirming` is a `Symbol` (`:none`, `:cancel` or `:info`);
`return_value::Any` holds what `do_precompile` returned (`nothing` or the cache paths). -/
structure BackgroundPrecompileState (T : Rt) where
  task : Option T.Tsk
  interrupt_requested : Bool
  cancel_requested : Bool
  monitoring : Bool
  completed_at : Option F64
  result : Option Bytes
  return_value : Option (List Bytes)
  exception : Option PError
  lock : T.Lock
  task_done : T.Cond
  signal_channels : List T.SigChan
  pending_pkgids : T.Dict PkgId JInt64
  completed_pkgids : T.Dict PkgId Unit
  pkg_done : T.Cond
  work_channel : T.ReqChan
  verbose : Bool
  detachable : Bool
  confirming : Bytes
  confirm_deadline : F64
  info_requested : Bool
  key_listening : Bool
  foreground_monitors : JInt64
  key_controls : Bool

/-- `const BG = BackgroundPrecompileState(...)`, given its new lock, conditions and channel. -/
def BG_init {T : Rt} (D : DictOps T.Dict) (lock : T.Lock) (task_done pkg_done : T.Cond) (work_channel : T.ReqChan) :
    BackgroundPrecompileState T :=
  ⟨none, false, false, false, none, none, none, none, lock, task_done, [], D.empty, D.empty, pkg_done,
    work_channel, false, false, lit "none", fl 0, false, false, ji 0, false⟩

/-- The arguments of `Base.compilecache_freshest_path(pkg; ...)` (`base/loading.jl`); `none` is an
omitted keyword, which takes its default. -/
structure FreshestArgs (T : Rt) where
  ignore_loaded : Bool
  stale_cache : T.Dict T.SCK Bool
  cachepath_cache : T.Dict PkgId (List Bytes)
  cachepaths : Option (List Bytes) := none
  sourcespec : Option (Option T.Spec) := none
  flags : Option T.CF := none
  verify_checksums : Bool := true
  unverified : Option (T.Dict Bytes Unit) := none
  reasons : Option (T.Dict Bytes JInt64) := none

/-- What `compilecache_freshest_path` returns or throws, and the contents of the dictionaries and
set it mutates in place, as they are after the call. -/
structure FreshestResult (T : Rt) where
  result : Except PError (Option Bytes)
  stale_cache : T.Dict T.SCK Bool
  unverified : Option (T.Dict Bytes Unit)
  reasons : Option (T.Dict Bytes JInt64)

/-- What `Base.compilecache` returns: `nothing` (a cache already existed), the paths it wrote, or an
`Exception` value. -/
inductive CompileResult where
  | nothing
  | paths (jl : Bytes) (so : Option Bytes)
  | exc (e : PError)

/-- The keyword arguments `precompile_task` passes to `Base.compilecache`. -/
structure CompileArgs (T : Rt) where
  flags : T.Cmd
  cacheflags : T.CF
  loadable_exts : Option (List PkgId)
  signal_channel : T.SigChan
  pid_channel : T.PidChan
  report_timing : Bool
  preresolved : List (PkgId × Bytes)

/-- `SchedulePriorities`: its dictionaries and set are mutated in place, so the object is reached
through `Ops.prioGet`/`Ops.prioModify`. -/
structure SchedulePriorities (T : Rt) where
  lock : T.Lock
  dependents : T.Dict PkgId (List PkgId)
  sourcespecs : T.Dict PkgId (Option T.Spec)
  cost : T.Dict PkgId F64
  height : T.Dict PkgId F64
  visiting : T.Dict PkgId Unit

/-- Cumulative CPU time and resident set size of a process. -/
structure ProcStats where
  cpu_ns : JInt .u64
  rss_bytes : JInt .u64

/-- The runtime operations of the session code. Unless stated, each is the Julia call of the
same name. -/
structure Ops (m : Type → Type) (T : Rt) where
  D : DictOps T.Dict
  any : AnyOps T.Dict T.A
  env : EnvOps m T.Dict T.A T.SHA1
  graph : GraphOps m
  jobserver : JobserverOps m T.P
  /-- The mutable state of the session's `parallel_limiter` and its condition. -/
  limiter : LimiterOps m T.Cond
  baseline : BaselineOps m
  -- the mutable records
  sget : T.Sess → m (PrecompileSession T)
  smodify : T.Sess → (PrecompileSession T → PrecompileSession T) → m Unit
  /-- `PrecompileSession(; ...)`: a new session object holding the record. -/
  snew : PrecompileSession T → m T.Sess
  bgget : m (BackgroundPrecompileState T)
  bgmodify : (BackgroundPrecompileState T → BackgroundPrecompileState T) → m Unit
  -- locks, conditions and events
  /-- `@lock l body`. -/
  withLock : {α : Type} → T.Lock → m α → m α
  lock : T.Lock → m Unit
  unlock : T.Lock → m Unit
  trylock : T.Lock → m Bool
  newLock : m T.Lock
  /-- `const launch_lock = ReentrantLock()`. -/
  launch_lock : T.Lock
  /-- `Base.require_lock`. -/
  require_lock : T.Lock
  /-- `@lock cond body` of a `Threads.Condition`. -/
  condLock : {α : Type} → T.Cond → m α → m α
  condWait : T.Cond → m Unit
  condNotify : T.Cond → m Unit
  newCondition : m T.Cond
  newEvent : m T.Ev
  notifyEv : T.Ev → m Unit
  waitEv : T.Ev → m Unit
  -- tasks
  /-- `Threads.@spawn :samepool body`. -/
  spawn : m Unit → m T.Tsk
  istaskdone : T.Tsk → m Bool
  istaskfailed : T.Tsk → m Bool
  /-- `wait(t)`, which throws when the task failed. -/
  waitTask : T.Tsk → m Unit
  /-- `wait(t; throw=false)`. -/
  waitTaskNoThrow : T.Tsk → m Unit
  /-- `waitall(ts; failfast=false, throw=false)`. -/
  waitall : List T.Tsk → m Unit
  errormonitor : T.Tsk → m Unit
  current_task : m T.Tsk
  /-- `current_task() === something(Base.foreground_task(), Base.roottask)`. -/
  isForegroundTask : m Bool
  /-- `Base.OncePerProcess` of `register_atexit_hook`: on the first call in the process, registers
  the hook with `Base.atexit`; later calls do nothing. -/
  atexitOnce : m Unit → m Unit
  /-- `Base.OncePerProcess` of `_mach_timebase`: runs the initializer on the first call in the
  process and returns its stored result on every call. -/
  timebaseOnce : m (JInt .u64 × JInt .u64) → m (JInt .u64 × JInt .u64)
  -- channels
  newSigChannel : JInt64 → m T.SigChan
  sigIsopen : T.SigChan → m Bool
  sigPut : T.SigChan → JInt .i32 → m Unit
  sigClose : T.SigChan → m Unit
  /-- `Channel{PrecompileRequest}(Inf)`. -/
  newReqChannel : m T.ReqChan
  reqIsopen : T.ReqChan → m Bool
  reqPut : T.ReqChan → PrecompileRequest T → m Unit
  reqTake : T.ReqChan → m (PrecompileRequest T)
  reqIsready : T.ReqChan → m Bool
  reqClose : T.ReqChan → m Unit
  /-- `Channel{Any}(1)`. -/
  newResChannel : m T.ResChan
  resPut : T.ResChan → RequestResult → m Unit
  resTake : T.ResChan → m RequestResult
  resIsready : T.ResChan → m Bool
  -- printing
  /-- An `IOContext` as an `IO`. -/
  ctx : T.IOC → T.Stream
  /-- `IOContext{IO}(io)` of a stream that is not an `IOContext{IO}`, and the test for one. -/
  wrapIO : T.Stream → T.IOC
  asContext : T.Stream → Option T.IOC
  stderr : T.Stream
  print : T.Stream → Bytes → m Unit
  /-- `@lock io body`. -/
  lockIO : {α : Type} → T.Stream → m α → m α
  /-- `printstyled(io, header; color, bold=true)`. -/
  printstyledBold : T.Stream → Bytes → JuliaLean.base.util.Color → m Unit
  /-- `sprint(f; context=io)`, and what `f` returned. -/
  sprintCtx : {α : Type} → T.IOC → (T.Stream → m α) → m (Bytes × α)
  /-- The callees of `show_progress`; their `print` and `time` are `Ops.print` and `Ops.time`. -/
  progress : ProgressOps m T.Stream
  /-- `_truncate_at_width_or_chars(true, s, width)` (`base/show.jl`). -/
  truncate_at_width : Bytes → JInt64 → Bytes
  /-- `Base.format_bytes(n)` (`base/timing.jl`). -/
  formatBytes : JInt .u64 → m Bytes
  /-- `Int(s[1])`: the code point of the first character (`BoundsError` when empty). -/
  firstCharCode : Bytes → m JInt64
  /-- `strip(s)`. -/
  strip : Bytes → Bytes
  /-- The typed operations used by `timing_string` and `format_verbose_timing`. -/
  timingFormat : TimingFormatOps m
  /-- `sprint(showerror, e)`. -/
  showerror : PError → m Bytes
  /-- `string(pkg)` and `repr(MIME"text/plain"(), pkg)` of a `PkgId`. -/
  stringPkg : PkgId → Bytes
  reprPkg : PkgId → Bytes
  -- logging
  /-- `Base.@logmsg level msg`. -/
  logmsg : Option T.LogLevel → Bytes → m Unit
  /-- `CoreLogging.Debug` and `CoreLogging.Info`. -/
  logDebug : T.LogLevel
  logInfo : T.LogLevel
  /-- `@debug "Precompiling $(repr(MIME"text/plain"(), pkg))"`. -/
  debugPrecompiling : PkgId → m Unit
  -- timers, pipes and buffers
  /-- `Timer(delay; interval)`. -/
  newTimer : F64 → F64 → m T.Tmr
  waitTimer : T.Tmr → m Unit
  closeTimer : T.Tmr → m Unit
  /-- `Base.link_pipe!(Pipe(); reader_supports_async=true, writer_supports_async=true)`. -/
  link_pipe : m T.Pipe
  eofPipe : T.Pipe → m Bool
  /-- `readline(pipe, keep=true)`. -/
  readlineKeep : T.Pipe → m Bytes
  /-- `close(pipe.in)` and `isopen(pipe.in)`. -/
  closePipeIn : T.Pipe → m Unit
  pipeInIsopen : T.Pipe → m Bool
  bufWrite : T.Buf → Bytes → m Unit
  /-- `buf.size`. -/
  bufSize : T.Buf → m JInt64
  /-- `String(take!(buf))`. -/
  bufTake : T.Buf → m Bytes
  /-- `truncate(buf, 0)`. -/
  truncate0 : T.Buf → m T.Buf
  newBuf : m T.Buf
  -- scheduling priorities
  prioNew : SchedulePriorities T → m T.Prio
  prioGet : T.Prio → m (SchedulePriorities T)
  prioModify : T.Prio → (SchedulePriorities T → SchedulePriorities T) → m Unit
  /-- `max(x::Float64, y::Float64)`. -/
  maxF : F64 → F64 → F64
  /-- `get(io, :force_fancyprint, nothing)`: absent, or the value (`some none` for one that is not
  a `Bool`). -/
  forceFancyprint : T.Stream → m (Option (Option Bool))
  /-- `Base.unwrapcontext(io)[1] isa Base.TTY`. -/
  unwrappedIsTTY : T.Stream → m Bool
  /-- `get(io, :color, false)`, or `none` when the value is not a `Bool`. -/
  getColor : T.IOC → m (Option Bool)
  /-- `displaysize(io)`. -/
  displaysize : T.IOC → m (JInt64 × JInt64)
  info_color : m JuliaLean.base.util.Color
  warn_color : m JuliaLean.base.util.Color
  error_color : m JuliaLean.base.util.Color
  -- environment and platform
  getENV : Bytes → m (Option Bytes)
  islinux : Bool
  isapple : Bool
  iswindows : Bool
  time : m F64
  time_ns : m (JInt .u64)
  /-- `round(Int, x)`. -/
  roundInt : F64 → m JInt64
  /-- `ceil(Int, x)`. -/
  ceilInt : F64 → m JInt64
  /-- `min(x::Float64, y::Float64)`. -/
  minF : F64 → F64 → F64
  -- files and processes
  /-- `read(path, String)`. -/
  readString : Bytes → m Bytes
  /-- `split(s)` on whitespace. -/
  splitWS : Bytes → List Bytes
  /-- `parse(UInt64, s)`. -/
  parseUInt64 : Bytes → m (JInt .u64)
  /-- `ccall(:getpagesize, Cint, ())`. -/
  getpagesize : m (JInt .i32)
  /-- `ccall((:proc_pidinfo, "libproc"), Cint, ..., pid, flavor, arg, buf, size)` with a new
  `size`-byte buffer: the result and the buffer's contents afterwards. -/
  proc_pidinfo : JInt .i32 → JInt .i32 → JInt .u64 → JInt .i32 → m (JInt .i32 × List UInt8)
  /-- `ccall(:mach_timebase_info, Cvoid, (Ptr{UInt32},), buf)` with `buf = zeros(UInt32, 2)`: the
  buffer's contents afterwards. -/
  mach_timebase_info : m (JInt .u32 × JInt .u32)
  -- loading
  /-- `get(Base.loaded_modules, pkg, nothing)`. -/
  loadedModule : PkgId → m (Option T.Mod)
  /-- `keys(Base.loaded_modules)`. -/
  loadedModuleKeys : m (List PkgId)
  locate_package : PkgId → m (Option Bytes)
  /-- `Base.locate_package_env(pkg)`. -/
  locate_package_env : PkgId → m (Option (T.Spec × Bytes))
  locate_package_load_spec : PkgId → m (Option T.Spec)
  /-- `spec.path`. -/
  specPath : T.Spec → Bytes
  /-- `Base.manifest_uuid_load_spec(env, pkg)` when it is a `PkgLoadSpec`. -/
  manifest_uuid_load_spec : Bytes → PkgId → m (Option T.Spec)
  pkgversion : T.Mod → m (Option T.Version)
  get_pkgversion_from_path : Bytes → m (Option T.Version)
  /-- `Base.reject_reason(key)`: the category and the description. -/
  reject_reason : Bytes → m (Bytes × Bytes)
  load_path_expand : Bytes → m (Option Bytes)
  checksums_valid_now : Bytes → m Bool
  compilecache_freshest_path : PkgId → FreshestArgs T → m (FreshestResult T)
  DEPOT_PATH : m (List Bytes)
  normpath : Bytes → m Bytes
  basename : Bytes → m Bytes
  contractuser : Bytes → m Bytes
  /-- The exec words of a `Cmd` (what iterating it yields). -/
  cmdArgs : T.Cmd → List Bytes
  translate_cache_flags : T.CF → T.CF → m (List Bytes)
  /-- `Base.DefaultCacheFlags`. -/
  DefaultCacheFlags : T.CF
  -- the monitor's references and stdin
  newBRef : Bool → m T.BRef
  bget : T.BRef → m Bool
  bset : T.BRef → Bool → m Unit
  newU8Vec : m T.U8Vec
  u8Push : T.U8Vec → UInt8 → m Unit
  u8Get : T.U8Vec → m (List UInt8)
  /-- `stdin isa Base.TTY`. -/
  stdinIsTTY : m Bool
  /-- `trylock(stdin.raw_lock)` and `unlock(stdin.raw_lock)`. -/
  stdinTrylockRaw : m Bool
  stdinUnlockRaw : m Unit
  /-- `Base.Terminals.TTYTerminal(term, stdin, stdout, stderr)` and `Base.Terminals.raw!(t, b)`. -/
  ttyTerminal : Bytes → m T.Term
  rawMode : T.Term → Bool → m Unit
  /-- `Base.start_reading(stdin)` and `yield()`. -/
  stdinStartReading : m Unit
  yieldTask : m Unit
  stdinBytesavailable : m JInt64
  /-- `read(stdin, UInt8)`, and `read(stdin, Char)` as the character's bytes. -/
  stdinReadByte : m UInt8
  stdinReadChar : m Bytes
  /-- `Base.wait_readnb(stdin, n)`. -/
  stdinWaitReadnb : JInt64 → m Unit
  /-- `lock(stdin.cond)`, `unlock(stdin.cond)`, `notify(stdin.cond)`. -/
  stdinLockCond : m Unit
  stdinUnlockCond : m Unit
  stdinNotifyCond : m Unit
  /-- `write(stdin.buffer, bytes)`, `Base.reseteof(stdin)`, `stdin.status = Base.StatusEOF`. -/
  stdinBufferWrite : List UInt8 → m Unit
  stdinReseteof : m Unit
  stdinSetStatusEOF : m Unit
  /-- `Timer(f, delay)`. -/
  newTimerOnce : F64 → m Unit → m T.Tmr
  -- look-ahead loading
  /-- `Base.JLOptions().use_compiled_modules`. -/
  use_compiled_modules : m (JInt .i8)
  generating_output : m Bool
  /-- `Base.disable_parallel_precompile`. -/
  disable_parallel_precompile : m Bool
  /-- `Base.identify_package(into, name)`. -/
  identify_package_in : T.Mod → Bytes → m (Option PkgId)
  root_module_exists : PkgId → m Bool
  /-- `Base.pkg_log_name(pkg)` and `Base.pkg_log_name(ext, parent)`. -/
  pkg_log_name : PkgId → m Bytes
  pkg_log_name2 : PkgId → PkgId → m Bytes
  /-- `Base.list_reasons(reasons; full=true)`. -/
  list_reasons_full : T.Dict Bytes JInt64 → m Bytes
  /-- `@debug msg`: `msg` is evaluated only when debug logging is enabled. -/
  debugLazy : m Bytes → m Unit
  /-- `@debug "Look-ahead precompilation failed, leaving it to `require`" exception=(err, catch_backtrace())`. -/
  debugLookAhead : PError → m Unit
  /-- `@debug "precompilepkgs called with" pkgs internal_call ... force_stdlibs`, given the values. -/
  debugCalled : Pkgs → List (Bytes × Bool) → (Config T ⊕ List (Config T)) → List (Bytes × Bool) → m Unit
  /-- ``` `` ``` and `Base.CacheFlags()`. -/
  emptyCmd : T.Cmd
  newCacheFlags : m T.CF
  /-- `Base.identify_package(name)`. -/
  identify_package : Bytes → m (Option PkgId)
  /-- `Sys.EFFECTIVE_CPU_THREADS::Int`. -/
  EFFECTIVE_CPU_THREADS : m JInt64
  /-- `tryparse(Int, s)`. -/
  tryparseInt : Bytes → Option JInt64
  /-- `parse(Int, s)`. -/
  parseInt : Bytes → m JInt64
  isinteractive : m Bool
  /-- `Base.JLOptions().quiet`. -/
  jlQuiet : m (JInt .i8)
  devnull : T.Stream
  /-- `io.io.lock::ReentrantLock` when `io.io isa Base.LibuvStream`, else `none`. -/
  streamLock : T.IOC → m (Option T.Lock)
  /-- `string(pkgs)` of the package vector. -/
  showPkgs : Pkgs → Bytes
  /-- `Timer(f, delay; interval, spawn=true)`. -/
  newTimerCb : F64 → F64 → m Unit → m T.Tmr
  /-- `Base.LOADING_CACHE[] = Base.LoadingCache()` and `Base.LOADING_CACHE[] = nothing`. -/
  newLoadingCache : m Unit
  clearLoadingCache : m Unit
  /-- `@debug "precompile: starting precompilation loop" direct_deps project_deps`. -/
  debugStartingLoop : T.Dict PkgId (List PkgId) → List PkgId → m Unit
  /-- The `Cmd` with exec words `args` (a backtick command interpolating them). -/
  cmdOfArgs : List Bytes → T.Cmd
  /-- `walkdir(dir)`: its `(root, dirs, files)` triples in iteration order; an exception raised while
  iterating ends the list as an `.error` element. -/
  walkdir : Bytes → m (List (Except PError (Bytes × List Bytes × List Bytes)))
  filesize : Bytes → m JInt64
  find_all_in_cache_path : PkgId → m (List Bytes)
  /-- `Base.CACHE_FETCH_HOOK[] !== nothing`. -/
  cacheFetchHookSet : m Bool
  maybe_fetch_cache : PkgId → Bytes → m Bool
  /-- `Base.compilecache(pkg, spec, internal_stderr, internal_stdout, keep_loaded_modules; kwargs...)`. -/
  compilecache : PkgId → T.Spec → T.Pipe → T.Pipe → Bool → CompileArgs T → m CompileResult
  newPidChannel : JInt64 → m T.PidChan
  pidTake : T.PidChan → m (JInt .i32)
  pidClose : T.PidChan → m Unit
  /-- The build id, the first value of `Base.parse_cache_buildid(path)`. -/
  parse_cache_buildid : Bytes → m (JInt .u128)
  module_build_id : T.Mod → m (JInt .u128)
  /-- `(pkg, build_id, sourcespec, cachefile, ignore_loaded, cacheflags)::StaleCacheKey`. -/
  mkStaleCacheKey : PkgId → JInt .u128 → T.Spec → Bytes → Bool → T.CF → T.SCK
  /-- `occursin(r"\b__precompile__\(\s*false\s*\)", text)`. -/
  hasPrecompileFalse : Bytes → Bool
  /-- `isdefined(Base, :mkpidlock_hook) && isdefined(Base, :trymkpidlock_hook) &&
  Base.isdefined(Base, :parse_pidfile_hook)`. -/
  pidlockHooksDefined : m Bool
  /-- `@invokelatest Base.trymkpidlock_hook(f, pidfile; stale_age)`: `none` for `false`. -/
  trymkpidlock_hook : m CompileResult → Bytes → JInt64 → m (Option CompileResult)
  mkpidlock_hook : m CompileResult → Bytes → JInt64 → m CompileResult
  /-- The process id and host name of `@invokelatest Base.parse_pidfile_hook(pidfile)`. -/
  parse_pidfile_hook : Bytes → m (JInt64 × Bytes)
  gethostname : m Bytes
  getpid : m (JInt .i32)
  /-- `Base.compilecache_pidfile_path(pkg, flags=cacheflags)`. -/
  compilecache_pidfile_path : PkgId → T.CF → m Bytes

section session
variable {m : Type → Type} [Monad m] [MonadExceptOf PError m] {T : Rt}
open JuliaLean.base.float (sub_float add_float mul_float div_float lt_float le_float uitofp sitofp)

/-- `Base.lock(f, bg)`. -/
def lock_BG (o : Ops m T) {α : Type} (f : m α) : m α := do o.withLock (← o.bgget).lock f
/-- `Base.lock(bg)`. -/
def lock_BG_ (o : Ops m T) : m Unit := do o.lock (← o.bgget).lock
/-- `Base.unlock(bg)`. -/
def unlock_BG (o : Ops m T) : m Unit := do o.unlock (← o.bgget).lock

/-- `printpkgstyle(io, header, msg; color)`. -/
def pps (o : Ops m T) (io : T.Stream) (header : String) (msg : Bytes)
    (color : JuliaLean.base.util.Color := .symbol "green") : m Unit :=
  printpkgstyle o.lockIO o.printstyledBold o.print io (lit header) msg color

/-- `println(io, xs...)`. -/
def println (o : Ops m T) (io : T.Stream) (s : Bytes) : m Unit := o.print io (s ++ lit "\n")

/-- Updates the job `s.jobs[pc]` in place. -/
def modifyJob (o : Ops m T) (s : T.Sess) (pc : PkgConfig T) (f : PrecompileJob T.Buf → PrecompileJob T.Buf) :
    m Unit :=
  o.smodify s fun st => match o.D.get st.jobs pc with
    | some j => { st with jobs := o.D.set st.jobs pc (f j) }
    | none => st

/-- The job `s.jobs[pc]` (a `KeyError` if absent). -/
def getJob (o : Ops m T) (s : T.Sess) (pc : PkgConfig T) : m (PrecompileJob T.Buf) := do
  getindex o.D (← o.sget s).jobs pc

/-- `can_fancyprint(io)` where its value is used as a `Bool` (a `TypeError` otherwise). -/
def can_fancyprint_bool (o : Ops m T) (io : T.Stream) : m Bool := do
  match ← can_fancyprint o.forceFancyprint o.unwrappedIsTTY o.getENV io with
  | .inl (some b) => return b
  | .inl none => throwP .typeError
  | .inr b => return b

/--
Julia source: base/precompilation.jl:1198-1205 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Workers and loading trust these paths without checks, so check a file the scan did not read.
function checked_now!(s::PrecompileSession, path::String)
    (@lock s.cache_lock path in s.unverified) || return true
    Base.checksums_valid_now(path) || return false
    @lock s.cache_lock delete!(s.unverified, path)
    return true
end

```
-/
def checked_now (o : Ops m T) (s : T.Sess) (path : Bytes) : m Bool := do
  let cache_lock := (← o.sget s).cache_lock
  if !(← o.withLock cache_lock do return setIn o.D (← o.sget s).unverified path) then return true
  if !(← o.checksums_valid_now path) then return false
  o.withLock cache_lock (o.smodify s fun st => { st with unverified := o.D.delete st.unverified path })
  return true

/--
Julia source: base/precompilation.jl:1192-1197 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Include only cache files that are ready for workers.
function preresolved_snapshot(s::PrecompileSession)
    paths = @lock s.cache_lock Pair{Base.PkgId,String}[k => first(v) for (k, v) in s.cachepath_cache if !isempty(v)]
    return filter!(kv -> checked_now!(s, kv.second), paths)
end

```
-/
def preresolved_snapshot (o : Ops m T) (s : T.Sess) : m (List (PkgId × Bytes)) := do
  let paths ← o.withLock (← o.sget s).cache_lock do
    let cc := (← o.sget s).cachepath_cache
    let mut ps : List (PkgId × Bytes) := []
    for k in o.D.keys cc do
      match ← getindex o.D cc k with
      | v :: _ => ps := ps ++ [(k, v)]
      | [] => pure ()
    return ps
  paths.filterM fun kv => checked_now o s kv.2

/--
Julia source: base/precompilation.jl:1457-1462 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
## Background lifecycle

function is_precompiling_in_background()
    @lock BG (BG.task !== nothing && !istaskdone(BG.task))
end

```
-/
def is_precompiling_in_background (o : Ops m T) : m Bool :=
  lock_BG o do
    match (← o.bgget).task with
    | none => return false
    | some t => return !(← o.istaskdone t)

/--
Julia source: base/precompilation.jl:1463-1473 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Check if `pkg` is currently being precompiled by a background task.
# This should be called while holding require_lock to avoid races.
# Returns true if the package is pending.
function is_package_pending(pkg::PkgId)
    @lock BG begin
        BG.task === nothing && return false
        istaskdone(BG.task) && return false
        return get(BG.pending_pkgids, pkg, 0) > 0
    end
end

```
-/
def is_package_pending (o : Ops m T) (pkg : PkgId) : m Bool :=
  lock_BG o do
    let some t := (← o.bgget).task | return false
    if ← o.istaskdone t then return false
    return (getD o.D (← o.bgget).pending_pkgids pkg (ji 0)).val > 0

/--
Julia source: base/precompilation.jl:1483-1492 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Broadcast a signal to all active precompilation subprocesses.
function broadcast_signal(sig::Int32)
    @lock BG begin
        for ch in BG.signal_channels
            try; isopen(ch) && put!(ch, sig); catch e; e isa InvalidStateException || rethrow(); end
        end
    end
end
broadcast_signal(sig::Integer) = broadcast_signal(Int32(sig))

```
-/
def broadcast_signal (o : Ops m T) (sig : JInt .i32) : m Unit :=
  lock_BG o do
    for ch in (← o.bgget).signal_channels do
      tryCatchThe PError (do if ← o.sigIsopen ch then o.sigPut ch sig) fun e =>
        match e with
        | .invalidStateException => pure ()
        | e => throwThe PError e

/-- `broadcast_signal(sig::Integer)`: `Int32(sig)` throws `InexactError` outside the `Int32` range. -/
def broadcast_signal_Integer (o : Ops m T) (sig : Int) : m Unit := do
  if sig < IntTy.min .i32 || sig > IntTy.max .i32 then throwP .inexactError
  broadcast_signal o (JInt.wrap .i32 sig)

/--
Julia source: base/precompilation.jl:1493-1502 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Record that `pkg` will not be precompiled by this session (e.g. missing source,
# `__precompile__(false)`), so watchers waiting for it are released promptly.
function mark_completed_pkgid!(pkg::PkgId)
    @lock BG @lock BG.pkg_done begin
        push!(BG.completed_pkgids, pkg)
        notify(BG.pkg_done)
    end
    return nothing
end

```
-/
def mark_completed_pkgid (o : Ops m T) (pkg : PkgId) : m Unit := do
  lock_BG o do
    o.condLock (← o.bgget).pkg_done do
      o.bgmodify fun bg => { bg with completed_pkgids := setPush o.D bg.completed_pkgids pkg }
      o.condNotify (← o.bgget).pkg_done
  return ()

/--
Julia source: base/precompilation.jl:1503-1518 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function stop_background_precompile(; graceful::Bool = true)
    @lock BG begin
        if BG.task !== nothing && !istaskdone(BG.task)
            if graceful
                BG.interrupt_requested = true
            else
                BG.cancel_requested = true
                broadcast_signal(Base.SIGKILL) # re-entrant: broadcast_signal also @lock's BG
            end
            try; close(BG.work_channel); catch; end
            return true
        end
        return false
    end
end

```
-/
/- `Base.SIGKILL` is `9`. -/
def stop_background_precompile (o : Ops m T) (graceful : Bool := true) : m Bool :=
  lock_BG o do
    match (← o.bgget).task with
    | some t =>
      if !(← o.istaskdone t) then
        if graceful then
          o.bgmodify fun bg => { bg with interrupt_requested := true }
        else
          o.bgmodify fun bg => { bg with cancel_requested := true }
          broadcast_signal_Integer o 9 -- re-entrant: broadcast_signal also @lock's BG
        tryCatchThe PError (do o.reqClose (← o.bgget).work_channel) fun _ => pure ()
        return true
      return false
    | none => return false

/--
Julia source: base/precompilation.jl:1519-1529 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const register_atexit_hook = Base.OncePerProcess{Nothing}() do
    Base.atexit() do
        task = @lock BG BG.task
        task === nothing && return
        istaskdone(task) && return
        stop_background_precompile(; graceful=false)
        wait(task)
    end
    nothing
end

```
-/
/- The hook `register_atexit_hook` registers with `Base.atexit`. -/
def atexit_hook (o : Ops m T) : m Unit := do
  let task ← lock_BG o do return (← o.bgget).task
  let some task := task | return
  if ← o.istaskdone task then return
  discard (stop_background_precompile o false)
  o.waitTask task

/-- `register_atexit_hook()`. -/
def register_atexit_hook (o : Ops m T) : m Unit := o.atexitOnce (atexit_hook o)

/--
Julia source: base/precompilation.jl:1530-1534 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const _confirm_messages = Dict{Symbol, String}(
    :cancel => "cancel precompilation",
    :info   => "send profiling signal",
)

```
-/
def _confirm_messages (k : Bytes) : Option Bytes :=
  if k == lit "cancel" then some (lit "cancel precompilation")
  else if k == lit "info" then some (lit "send profiling signal")
  else none

/--
Julia source: base/precompilation.jl:1535-1549 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function keyboard_tip(s::BackgroundPrecompileState)
    s.monitoring || return "", :default
    s.key_listening || return "", :default
    if s.confirming !== :none
        remaining = max(0, ceil(Int, s.confirm_deadline - time()))
        msg = get(_confirm_messages, s.confirming, string(s.confirming))
        return "Press Enter to $(msg) (ignoring in $(remaining)s)", Base.info_color()
    end
    if s.detachable
        return "Press `?` for help, `c` to cancel, `d` to detach.", :default
    else
        return "Press `?` for help, `c` to cancel.", :default
    end
end

```
-/
def keyboard_tip (o : Ops m T) (s : BackgroundPrecompileState T) : m (Bytes × JuliaLean.base.util.Color) := do
  if !s.monitoring then return ([], .symbol "default")
  if !s.key_listening then return ([], .symbol "default")
  if s.confirming != lit "none" then
    let remaining := ji (max 0 (← o.ceilInt (sub_float s.confirm_deadline (← o.time))).val)
    -- `string(s.confirming)` of a `Symbol` is its name
    let msg := (_confirm_messages s.confirming).getD s.confirming
    return (lit "Press Enter to " ++ msg ++ lit " (ignoring in " ++ istr remaining ++ lit "s)", ← o.info_color)
  if s.detachable then
    return (lit "Press `?` for help, `c` to cancel, `d` to detach.", .symbol "default")
  else
    return (lit "Press `?` for help, `c` to cancel.", .symbol "default")

/--
Julia source: base/precompilation.jl:1849-1859 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Turn output off, unless a foreground task other than this monitor's is still waiting on
# the run. Checked and written under one lock, so a foreground request merging in meanwhile
# cannot be left with output off. Returns whether output stays on.
function stop_monitoring_unless_waited_on(counted::Bool)
    @lock BG begin
        others = BG.foreground_monitors > (counted ? 1 : 0)
        others || (BG.monitoring = false)
        others
    end
end

```
-/
def stop_monitoring_unless_waited_on (o : Ops m T) (counted : Bool) : m Bool :=
  lock_BG o do
    let others := (← o.bgget).foreground_monitors.val > (if counted then 1 else 0)
    if !others then o.bgmodify fun bg => { bg with monitoring := false }
    return others

/--
Julia source: base/precompilation.jl:2065-2076 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
## Session implementation

# Mach timebase info for converting Mach absolute time → nanoseconds on macOS.
# Queried once per process at runtime (not at sysimage build time).
@static if Sys.isapple()
    const _mach_timebase = Base.OncePerProcess{Tuple{UInt64,UInt64}}() do
        buf = zeros(UInt32, 2)
        ccall(:mach_timebase_info, Cvoid, (Ptr{UInt32},), buf)
        (UInt64(buf[1]), UInt64(buf[2]))
    end
end

```
-/
/- `_mach_timebase()` (defined on Apple platforms). -/
def _mach_timebase (o : Ops m T) : m (JInt .u64 × JInt .u64) :=
  o.timebaseOnce do
    let (numer, denom) ← o.mach_timebase_info
    return (JInt.wrap .u64 numer.val, JInt.wrap .u64 denom.val)

/--
Julia source: base/precompilation.jl:2077-2123 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Read cumulative CPU time (user+system) in nanoseconds and RSS in bytes for a process.
# Returns (cpu_ns=0, rss_bytes=0) if the process no longer exists or on unsupported platforms.
function process_stats(pid::Int32)
    @static if Sys.islinux()
        try
            stat = read("/proc/$(pid)/stat", String)
            # Field 2 (comm) is in parens and may contain spaces; skip past it
            i = findlast(')', stat)
            i === nothing && return (cpu_ns=UInt64(0), rss_bytes=UInt64(0))
            fields = split(@view(stat[nextind(stat, i):end]))
            # fields[1] = state (field 3), so utime=field 14 is at index 12,
            # stime=field 15 at index 13, rss=field 24 at index 22
            length(fields) >= 22 || return (cpu_ns=UInt64(0), rss_bytes=UInt64(0))
            utime = parse(UInt64, fields[12])
            stime = parse(UInt64, fields[13])
            rss_pages = parse(UInt64, fields[22])
            # CLK_TCK is almost always 100 on Linux; 1 tick = 10ms = 10_000_000 ns
            cpu_ns = (utime + stime) * UInt64(10_000_000)
            rss_bytes = rss_pages * UInt64(ccall(:getpagesize, Cint, ()))
            return (; cpu_ns, rss_bytes)
        catch
            return (cpu_ns=UInt64(0), rss_bytes=UInt64(0))
        end
    elseif Sys.isapple()
        try
            buf = Vector{UInt8}(undef, 96)  # sizeof(struct proc_taskinfo)
            ret = ccall((:proc_pidinfo, "libproc"), Cint,
                        (Cint, Cint, UInt64, Ptr{UInt8}, Cint),
                        pid, Cint(4), UInt64(0), buf, Cint(96))
            ret <= 0 && return (cpu_ns=UInt64(0), rss_bytes=UInt64(0))
            # pti_resident_size at offset 8 (bytes)
            rss_bytes = GC.@preserve buf unsafe_load(Ptr{UInt64}(pointer(buf) + 8))
            # pti_total_user at offset 16, pti_total_system at offset 24 (Mach absolute time)
            user = GC.@preserve buf unsafe_load(Ptr{UInt64}(pointer(buf) + 16))
            sys  = GC.@preserve buf unsafe_load(Ptr{UInt64}(pointer(buf) + 24))
            # Convert Mach absolute time to nanoseconds via mach_timebase_info
            numer, denom = _mach_timebase()
            cpu_ns = div((user + sys) * numer, denom)
            return (; cpu_ns, rss_bytes)
        catch
            return (cpu_ns=UInt64(0), rss_bytes=UInt64(0))
        end
    else
        return (cpu_ns=UInt64(0), rss_bytes=UInt64(0))
    end
end

```
-/
def zeroStats : ProcStats := ⟨JInt.wrap .u64 0, JInt.wrap .u64 0⟩

/-- `unsafe_load(Ptr{UInt64}(pointer(buf) + off))` on a little-endian platform. -/
def loadU64LE (buf : List UInt8) (off : Nat) : JInt .u64 :=
  JInt.wrap .u64 ((List.range 8).foldl (fun acc i => acc + ((buf.getD (off + i) 0).toNat * 256 ^ i : Nat)) 0)

/-- `findlast(c, s)` of an ASCII character: its byte index (0-based). -/
def lastIdxOf (c : UInt8) (s : Bytes) : Option Nat :=
  (s.zipIdx.filter (·.1 == c)).getLast?.map (·.2)

/-- `process_stats(pid)`; `@static` platform branches select on `Sys.islinux()`/`Sys.isapple()`. -/
def process_stats (o : Ops m T) (pid : JInt .i32) : m ProcStats := do
  if o.islinux then
    tryCatchThe PError (do
      let stat ← o.readString (lit "/proc/" ++ istr pid ++ lit "/stat")
      -- Field 2 (comm) is in parens and may contain spaces; skip past it
      match lastIdxOf (')'.toNat.toUInt8) stat with
      | none => return zeroStats
      | some i =>
        -- `')'` is one byte, so `nextind(stat, i)` is the next byte
        let fields := o.splitWS (stat.drop (i + 1))
        -- fields[1] = state (field 3), so utime=field 14 is at index 12,
        -- stime=field 15 at index 13, rss=field 24 at index 22
        if fields.length < 22 then return zeroStats
        let utime ← o.parseUInt64 (fields.getD 11 [])
        let stime ← o.parseUInt64 (fields.getD 12 [])
        let rss_pages ← o.parseUInt64 (fields.getD 21 [])
        -- CLK_TCK is almost always 100 on Linux; 1 tick = 10ms = 10_000_000 ns
        let cpu_ns := JInt.wrap .u64 ((JInt.wrap .u64 (utime.val + stime.val)).val * 10000000)
        -- `UInt64(::Cint)` throws `InexactError` for a negative value
        let ps ← o.getpagesize
        if ps.val < 0 then throwP .inexactError
        let rss_bytes := JInt.wrap .u64 (rss_pages.val * ps.val)
        return ⟨cpu_ns, rss_bytes⟩) fun _ => pure zeroStats
  else if o.isapple then
    tryCatchThe PError (do
      -- sizeof(struct proc_taskinfo)
      let (ret, buf) ← o.proc_pidinfo pid (JInt.wrap .i32 4) (JInt.wrap .u64 0) (JInt.wrap .i32 96)
      if ret.val ≤ 0 then return zeroStats
      -- pti_resident_size at offset 8 (bytes)
      let rss_bytes := loadU64LE buf 8
      -- pti_total_user at offset 16, pti_total_system at offset 24 (Mach absolute time)
      let user := loadU64LE buf 16
      let sys := loadU64LE buf 24
      -- Convert Mach absolute time to nanoseconds via mach_timebase_info
      let (numer, denom) ← _mach_timebase o
      if denom.val == 0 then throwP .divideError
      let prod := JInt.wrap .u64 ((JInt.wrap .u64 (user.val + sys.val)).val * numer.val)
      return ⟨JInt.wrap .u64 (prod.val / denom.val), rss_bytes⟩) fun _ => pure zeroStats
  else
    return zeroStats

/--
Julia source: base/precompilation.jl:2124-2155 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Compute CPU% and RSS for all active PIDs since last poll.
# Mutates cpu_pcts and rss in place.
function poll_process_stats!(cpu_pcts::Dict{Int32, Float64}, rss::Dict{Int32, UInt64},
                             prev_cpu_times::Dict{Int32, UInt64}, jobs::Dict{PkgConfig, PrecompileJob}, dt::Float64)
    empty!(cpu_pcts)
    empty!(rss)
    @static if !(Sys.islinux() || Sys.isapple())
        return
    end
    for (_, job) in jobs
        has_pid(job) || continue
        pid = job.pid
        haskey(cpu_pcts, pid) && continue
        stats = process_stats(pid)
        stats.cpu_ns == 0 && continue
        prev = get(prev_cpu_times, pid, stats.cpu_ns)
        delta = stats.cpu_ns >= prev ? stats.cpu_ns - prev : UInt64(0)
        prev_cpu_times[pid] = stats.cpu_ns
        pct = dt > 0 ? (delta / 1.0e9) / dt * 100.0 : 0.0
        cpu_pcts[pid] = min(pct, 999.9)
        if stats.rss_bytes > 0
            rss[pid] = stats.rss_bytes
            stats.rss_bytes > job.peak_rss_bytes && (job.peak_rss_bytes = stats.rss_bytes)
        end
    end
    pids_set = Set(job.pid for (_, job) in jobs if has_pid(job))
    for pid in keys(prev_cpu_times)
        pid in pids_set || delete!(prev_cpu_times, pid)
    end
    return
end

```
-/
/- `poll_process_stats!(cpu_pcts, rss, prev_cpu_times, jobs, dt)`: returns the four updated
arguments (`jobs` with the raised `peak_rss_bytes`). -/
def poll_process_stats (o : Ops m T) (_cpu_pcts : T.Dict (JInt .i32) F64) (_rss : T.Dict (JInt .i32) (JInt .u64))
    (prev_cpu_times : T.Dict (JInt .i32) (JInt .u64)) (jobs : T.Dict (PkgConfig T) (PrecompileJob T.Buf)) (dt : F64) :
    m (T.Dict (JInt .i32) F64 × T.Dict (JInt .i32) (JInt .u64) × T.Dict (JInt .i32) (JInt .u64) ×
      T.Dict (PkgConfig T) (PrecompileJob T.Buf)) := do
  -- `empty!(cpu_pcts)`, `empty!(rss)`
  let mut cpu_pcts : T.Dict (JInt .i32) F64 := o.D.empty
  let mut rss : T.Dict (JInt .i32) (JInt .u64) := o.D.empty
  if !(o.islinux || o.isapple) then return (cpu_pcts, rss, prev_cpu_times, jobs)
  let mut prev_cpu_times := prev_cpu_times
  let mut jobs := jobs
  for k in o.D.keys jobs do
    let job ← getindex o.D jobs k
    if !has_pid job then continue
    let pid := job.pid
    if haskey o.D cpu_pcts pid then continue
    let stats ← process_stats o pid
    if stats.cpu_ns.val == 0 then continue
    let prev := getD o.D prev_cpu_times pid stats.cpu_ns
    let delta := if stats.cpu_ns.val ≥ prev.val then JInt.wrap .u64 (stats.cpu_ns.val - prev.val) else JInt.wrap .u64 0
    prev_cpu_times := o.D.set prev_cpu_times pid stats.cpu_ns
    let pct := if lt_float (fl 0) dt then
        mul_float (div_float (div_float (uitofp .f64 delta) (fl 0x41CDCD6500000000)) dt) (fl 0x4059000000000000)
      else fl 0
    cpu_pcts := o.D.set cpu_pcts pid (o.minF pct (fl 0x408F3F3333333333))
    if stats.rss_bytes.val > 0 then
      rss := o.D.set rss pid stats.rss_bytes
      if stats.rss_bytes.val > job.peak_rss_bytes.val then
        jobs := o.D.set jobs k { job with peak_rss_bytes := stats.rss_bytes }
  let mut pids_set : T.Dict (JInt .i32) Unit := o.D.empty
  for k in o.D.keys jobs do
    let job ← getindex o.D jobs k
    if has_pid job then pids_set := setPush o.D pids_set job.pid
  for pid in o.D.keys prev_cpu_times do
    if !setIn o.D pids_set pid then prev_cpu_times := o.D.delete prev_cpu_times pid
  return (cpu_pcts, rss, prev_cpu_times, jobs)

/--
Julia source: base/precompilation.jl:2156-2176 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Lightweight peak-RSS-only sampler used in non-fancy verbose timing mode,
# where the live progress UI (which would otherwise drive `poll_process_stats!`)
# is not running but the per-package verbose timing column still wants peak RSS.
function sample_peak_rss!(jobs::Dict{PkgConfig, PrecompileJob})
    @static if !(Sys.islinux() || Sys.isapple())
        return
    end
    seen = Set{Int32}()
    for (_, job) in jobs
        has_pid(job) || continue
        pid = job.pid
        pid in seen && continue
        push!(seen, pid)
        stats = process_stats(pid)
        if stats.rss_bytes > job.peak_rss_bytes
            job.peak_rss_bytes = stats.rss_bytes
        end
    end
    return
end

```
-/
/- `sample_peak_rss!(jobs)`: returns `jobs` with the raised `peak_rss_bytes`. -/
def sample_peak_rss (o : Ops m T) (jobs : T.Dict (PkgConfig T) (PrecompileJob T.Buf)) :
    m (T.Dict (PkgConfig T) (PrecompileJob T.Buf)) := do
  if !(o.islinux || o.isapple) then return jobs
  let mut seen : T.Dict (JInt .i32) Unit := o.D.empty
  let mut jobs := jobs
  for k in o.D.keys jobs do
    let job ← getindex o.D jobs k
    if !has_pid job then continue
    let pid := job.pid
    if setIn o.D seen pid then continue
    seen := setPush o.D seen pid
    let stats ← process_stats o pid
    if stats.rss_bytes.val > job.peak_rss_bytes.val then
      jobs := o.D.set jobs k { job with peak_rss_bytes := stats.rss_bytes }
  return jobs

/--
Julia source: base/precompilation.jl:2177-2195 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function should_stop(s::PrecompileSession)
    ir, cr = @lock BG begin
        BG.interrupt_requested, BG.cancel_requested
    end
    if ir || cr
        @lock s.print_lock begin
            s.interrupted = s.interrupted || ir
            s.canceled = s.canceled || cr
            if !s.interrupted_or_done
                s.interrupted_or_done = true
                foreach(notify, values(s.was_processed))
                notify(s.first_started)
            end
        end
        return true
    end
    return s.interrupted_or_done
end

```
-/
def should_stop (o : Ops m T) (s : T.Sess) : m Bool := do
  let (ir, cr) ← lock_BG o do
    let bg ← o.bgget
    return (bg.interrupt_requested, bg.cancel_requested)
  if ir || cr then
    o.withLock (← o.sget s).print_lock do
      o.smodify s fun st => { st with interrupted := st.interrupted || ir }
      o.smodify s fun st => { st with canceled := st.canceled || cr }
      if !(← o.sget s).interrupted_or_done then
        o.smodify s fun st => { st with interrupted_or_done := true }
        let st ← o.sget s
        for k in o.D.keys st.was_processed do
          o.notifyEv (← getindex o.D st.was_processed k)
        o.notifyEv st.first_started
    return true
  return (← o.sget s).interrupted_or_done

/--
Julia source: base/precompilation.jl:2196-2201 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function make_signal_channel()
    ch = Channel{Int32}(32)
    @lock BG push!(BG.signal_channels, ch)
    return ch
end

```
-/
def make_signal_channel (o : Ops m T) : m T.SigChan := do
  let ch ← o.newSigChannel (ji 32)
  lock_BG o (o.bgmodify fun bg => { bg with signal_channels := bg.signal_channels ++ [ch] })
  return ch

/--
Julia source: base/precompilation.jl:2202-2218 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function describe_pkg(s::PrecompileSession, pkg::PkgId, is_project_dep::Bool, is_serial_dep::Bool, flags::Cmd, cacheflags::Base.CacheFlags)
    name = full_name(s.ext_to_parent, pkg)
    name = is_project_dep ? name : color_string(name, :light_black, s.hascolor)
    if is_serial_dep
        name *= color_string(" (serial)", :light_black, s.hascolor)
    end
    if length(s.configs) > 1 && !isempty(flags)
        config_str = join(flags, " ")
        name *= color_string(" `$config_str`", :light_black, s.hascolor)
    end
    if length(s.configs) > 1
        config_str = join(Base.translate_cache_flags(cacheflags, Base.DefaultCacheFlags), " ")
        name *= color_string(" $config_str", :light_black, s.hascolor)
    end
    return name
end

```
-/
def describe_pkg (o : Ops m T) (s : T.Sess) (pkg : PkgId) (is_project_dep is_serial_dep : Bool) (flags : T.Cmd)
    (cacheflags : T.CF) : m Bytes := do
  let st ← o.sget s
  let name ← full_name o.D st.ext_to_parent pkg
  let mut name ← if is_project_dep then pure name else color_string name (.symbol "light_black") st.hascolor
  if is_serial_dep then
    name := name ++ (← color_string (lit " (serial)") (.symbol "light_black") st.hascolor)
  if st.configs.length > 1 && !(o.cmdArgs flags).isEmpty then
    let config_str := joinB (lit " ") (o.cmdArgs flags)
    name := name ++ (← color_string (lit " `" ++ config_str ++ lit "`") (.symbol "light_black") st.hascolor)
  if st.configs.length > 1 then
    let config_str := joinB (lit " ") (← o.translate_cache_flags cacheflags o.DefaultCacheFlags)
    name := name ++ (← color_string (lit " " ++ config_str) (.symbol "light_black") st.hascolor)
  return name

/--
Julia source: base/precompilation.jl:2219-2226 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Up to five names, then how many more, as in "A, B, C, D, E, and 3 more".
function format_names_list(names::Vector{String}; max_names::Int=5)
    if length(names) > max_names
        return string(join(first(names, max_names), ", "), ", and ", length(names) - max_names, " more")
    end
    return join(names, ", ", " and ")
end

```
-/
/- `format_names_list(names; max_names)`; `first(names, n)` throws `ArgumentError` for `n < 0`. -/
def format_names_list (names : List Bytes) (max_names : JInt64 := ji 5) : m Bytes := do
  if (names.length : Int) > max_names.val then
    if max_names.val < 0 then throwP .argumentError
    return joinB (lit ", ") (names.take max_names.val.toNat) ++ lit ", and " ++
      istr (ji (names.length - max_names.val)) ++ lit " more"
  return joinLast (lit ", ") (lit " and ") names

/--
Julia source: base/precompilation.jl:2259-2269 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Whether `pkg` is loaded at a different version than the active environment gives it.
function loaded_version_differs(pkg::PkgId)
    m = @lock Base.require_lock get(Base.loaded_modules, pkg, nothing)
    m === nothing && return false
    path = Base.locate_package(pkg)
    path === nothing && return false
    loaded_version = Base.pkgversion(m)
    env_version = Base.get_pkgversion_from_path(dirname(dirname(path)))
    return loaded_version !== nothing && env_version !== nothing && loaded_version != env_version
end

```
-/
def loaded_version_differs (o : Ops m T) (pkg : PkgId) : m Bool := do
  let md ← o.withLock o.require_lock (o.loadedModule pkg)
  let some md := md | return false
  let some path ← o.locate_package pkg | return false
  let loaded_version ← o.pkgversion md
  let env_version ← o.get_pkgversion_from_path (← o.env.dirname (← o.env.dirname path))
  return match loaded_version, env_version with
    | some a, some b => a != b
    | _, _ => false

/--
Julia source: base/precompilation.jl:2270-2281 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# The loaded dependencies of the requested packages whose version differs from the
# environment's. The loader's cache rejections cannot show this: an old cache built against
# another build of the same version is rejected too, and on first use there is no cache.
function loaded_version_conflicts(s::PrecompileSession, pkgs)
    deps = Set{PkgId}()
    for pkg in pkgs
        haskey(s.direct_deps, pkg) && collect_all_deps(s.direct_deps, pkg, deps)
    end
    conflicts = PkgId[pkg for pkg in deps if pkg in s.start_loaded_modules && loaded_version_differs(pkg)]
    return sort!([full_name(s.ext_to_parent, pkg) for pkg in conflicts])
end

```
-/
def loaded_version_conflicts [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T) (s : T.Sess)
    (pkgs : List PkgId) : m (List Bytes) := do
  let mut deps : T.Dict PkgId Unit := o.D.empty
  for pkg in pkgs do
    let st ← o.sget s
    if haskey o.D st.direct_deps pkg then
      deps ← collect_all_deps o.D st.direct_deps pkg deps
  let mut conflicts : List PkgId := []
  for pkg in o.D.keys deps do
    if setIn o.D (← o.sget s).start_loaded_modules pkg then
      if ← loaded_version_differs o pkg then conflicts := conflicts ++ [pkg]
  let ext_to_parent := (← o.sget s).ext_to_parent
  return sortBytes (← conflicts.mapM (full_name o.D ext_to_parent))

/--
Julia source: base/precompilation.jl:2282-2290 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# The version the loader uses for `pkg`: the loaded one, or else the one in the first
# environment in the load path that has it.
function resolved_version(pkg::PkgId)
    m = @lock Base.require_lock get(Base.loaded_modules, pkg, nothing)
    m === nothing || return Base.pkgversion(m)
    path = Base.locate_package(pkg)
    return path === nothing ? nothing : Base.get_pkgversion_from_path(dirname(dirname(path)))
end

```
-/
def resolved_version (o : Ops m T) (pkg : PkgId) : m (Option T.Version) := do
  match ← o.withLock o.require_lock (o.loadedModule pkg) with
  | some md => o.pkgversion md
  | none =>
    match ← o.locate_package pkg with
    | none => return none
    | some path => o.get_pkgversion_from_path (← o.env.dirname (← o.env.dirname path))

/--
Julia source: base/precompilation.jl:2291-2323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Requested packages from a later environment in the load path, such as the default
# environment, whose dependencies have other versions in the active environment. The
# loader takes each package from the first environment that has it, so these packages
# are built against those versions. Grouped by the environment they come from.
function stacked_version_conflicts(s::PrecompileSession, pkgs)
    found = Dict{String, Tuple{Set{String}, Set{String}}}()
    for pkg in pkgs
        (pkg in s.serial_deps && pkg.uuid !== nothing) || continue
        specenv = @lock Base.require_lock Base.locate_package_env(pkg)
        specenv === nothing && continue
        env = specenv[2]
        project_file = Base.env_project_file(env)
        project_file isa String || continue
        penv = ExplicitEnv(project_file)
        uuids = Set{UUID}()
        _collect_reachable!(uuids, penv.deps, pkg.uuid)
        for uuid in uuids
            uuid == pkg.uuid && continue
            dep = PkgId(uuid, get(penv.names, uuid, ""))
            Base.in_sysimage(dep) && continue
            spec = Base.manifest_uuid_load_spec(env, dep)
            spec isa Base.PkgLoadSpec || continue
            env_version = Base.get_pkgversion_from_path(dirname(dirname(spec.path)))
            version = resolved_version(dep)
            (env_version === nothing || version === nothing || env_version == version) && continue
            dependents, deps = get!(() -> (Set{String}(), Set{String}()), found, dirname(project_file))
            push!(dependents, pkg.name)
            push!(deps, dep.name)
        end
    end
    return [(sort!(collect(dependents)), sort!(collect(deps)), envdir) for (envdir, (dependents, deps)) in found]
end

```
-/
/- `stacked_version_conflicts(s, pkgs)`: the `(dependents, deps, envdir)` triples. -/
def stacked_version_conflicts [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T) (s : T.Sess)
    (pkgs : List PkgId) : m (List (List Bytes × List Bytes × Bytes)) := do
  let mut found : T.Dict Bytes (T.Dict Bytes Unit × T.Dict Bytes Unit) := o.D.empty
  for pkg in pkgs do
    if !(← o.sget s).serial_deps.contains pkg then continue
    let some puuid := pkg.uuid | continue
    let some specenv ← o.withLock o.require_lock (o.locate_package_env pkg) | continue
    let env := specenv.2
    let some project_file ← o.env.env_project_file env | continue
    let penv ← ExplicitEnv_String o.D o.any o.env project_file
    let uuids ← _collect_reachable o.D o.D.empty penv.deps puuid
    for uuid in o.D.keys uuids do
      if uuid == puuid then continue
      let dep := pkgOf uuid (getD o.D penv.names uuid [])
      if ← o.graph.in_sysimage dep then continue
      let some spec ← o.manifest_uuid_load_spec env dep | continue
      let env_version ← o.get_pkgversion_from_path (← o.env.dirname (← o.env.dirname (o.specPath spec)))
      let version ← resolved_version o dep
      let same := match env_version, version with
        | some a, some b => a == b
        | _, _ => true
      if same then continue
      -- `get!(() -> (Set{String}(), Set{String}()), found, dirname(project_file))`
      let envdir ← o.env.dirname project_file
      let (dependents, deps) := getD o.D found envdir (o.D.empty, o.D.empty)
      found := o.D.set found envdir (setPush o.D dependents pkg.name, setPush o.D deps dep.name)
  let mut out : List (List Bytes × List Bytes × Bytes) := []
  for envdir in o.D.keys found do
    let (dependents, deps) ← getindex o.D found envdir
    out := out ++ [(sortBytes (o.D.keys dependents), sortBytes (o.D.keys deps), envdir)]
  return out

/--
Julia source: base/precompilation.jl:2324-2331 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# A depot environment by its `@name`, as the load path and the Pkg prompt show it.
function env_display_name(envdir::String)
    for depot in DEPOT_PATH
        normpath(dirname(envdir)) == normpath(joinpath(depot, "environments")) && return "@" * basename(envdir)
    end
    return Base.contractuser(envdir)
end

```
-/
def env_display_name (o : Ops m T) (envdir : Bytes) : m Bytes := do
  for depot in ← o.DEPOT_PATH do
    if (← o.normpath (← o.env.dirname envdir)) == (← o.normpath (← o.env.joinpath depot (lit "environments"))) then
      return lit "@" ++ (← o.basename envdir)
  o.contractuser envdir

/--
Julia source: base/precompilation.jl:2332-2343 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function stacked_conflicts_message(dependents::Vector{String}, deps::Vector{String}, envdir::String, hascolor::Bool)
    one_dependent = length(dependents) == 1
    one = length(deps) == 1
    string("  ", format_names_list(dependents), one_dependent ? " is" : " are", " from ", env_display_name(envdir),
        ", where ", format_names_list(deps), " ",
        color_string(one ? "has a different version" : "have different versions", Base.warn_color(), hascolor),
        " than in the active environment,\n  so ", one_dependent ? "it is" : "they are",
        " being precompiled against the active environment's version", one ? "" : "s", ".\n",
        "  Mixing versions may violate compat requirements and cause unexpected errors.\n",
        "  To avoid this, give ", format_names_list(deps), " the same version in both environments.")
end

```
-/
def stacked_conflicts_message (o : Ops m T) (dependents deps : List Bytes) (envdir : Bytes) (hascolor : Bool) :
    m Bytes := do
  let one_dependent := dependents.length == 1
  let one := deps.length == 1
  return lit "  " ++ (← format_names_list dependents) ++ lit (if one_dependent then " is" else " are") ++ lit " from " ++
    (← env_display_name o envdir) ++ lit ", where " ++ (← format_names_list deps) ++ lit " " ++
    (← color_string (lit (if one then "has a different version" else "have different versions")) (← o.warn_color) hascolor) ++
    lit " than in the active environment,\n  so " ++ lit (if one_dependent then "it is" else "they are") ++
    lit " being precompiled against the active environment's version" ++ lit (if one then "" else "s") ++ lit ".\n" ++
    lit "  Mixing versions may violate compat requirements and cause unexpected errors.\n" ++
    lit "  To avoid this, give " ++ (← format_names_list deps) ++ lit " the same version in both environments."

/--
Julia source: base/precompilation.jl:2344-2350 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# A cache left with other flags, such as one from `Pkg.test`, is also rejected when the
# real cause is something else, such as an edited source file, so require it to be alone.
function only_flags_mismatch(reasons::Dict{Symbol,Int})
    haskey(reasons, :flags_mismatch) || return false
    return all(k -> k === :flags_mismatch || first(Base.reject_reason(k)) !== :actionable, keys(reasons))
end

```
-/
def only_flags_mismatch (o : Ops m T) (reasons : T.Dict Bytes JInt64) : m Bool := do
  if !haskey o.D reasons (lit "flags_mismatch") then return false
  (o.D.keys reasons).allM fun k => do
    if k == lit "flags_mismatch" then return true
    return (← o.reject_reason k).1 != lit "actionable"

/--
Julia source: base/precompilation.jl:2351-2365 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Three lines: the cause, the risk of mixing versions, and how to get the manifest
# versions instead (cancel with `c` while the session is still running).
function loaded_conflicts_message(names::Vector{String}, hascolor::Bool; ongoing::Bool, cancelable::Bool,
                                  default_env::Bool=Base.active_project() == Base.load_path_expand("@v#.#"))
    one = length(names) == 1
    string("  ", format_names_list(names), " ",
        color_string(one ? "is loaded at a different version" : "are loaded at different versions", Base.warn_color(), hascolor),
        " than in the manifest, so ", one ? "its" : "their", " dependents ", ongoing ? "are being" : "were", " precompiled.\n",
        "  Mixing versions may violate compat requirements and cause unexpected errors.\n",
        "  To use the manifest version", one ? "" : "s", " instead, ",
        cancelable && ongoing ? "press `c` to cancel then " : "",
        # julia starts in the default environment, so it needs no `--project` to get back there
        default_env ? "restart julia." : "restart julia with `--project` set.")
end

```
-/
/- `loaded_conflicts_message(names, hascolor; ongoing, cancelable, default_env)`; `default_env = none`
takes the default `Base.active_project() == Base.load_path_expand("@v#.#")`. -/
def loaded_conflicts_message (o : Ops m T) (names : List Bytes) (hascolor ongoing cancelable : Bool)
    (default_env : Option Bool := none) : m Bytes := do
  let default_env ← match default_env with
    | some b => pure b
    | none => do pure ((← o.env.active_project) == (← o.load_path_expand (lit "@v#.#")))
  let one := names.length == 1
  return lit "  " ++ (← format_names_list names) ++ lit " " ++
    (← color_string (lit (if one then "is loaded at a different version" else "are loaded at different versions"))
      (← o.warn_color) hascolor) ++
    lit " than in the manifest, so " ++ lit (if one then "its" else "their") ++ lit " dependents " ++
    lit (if ongoing then "are being" else "were") ++ lit " precompiled.\n" ++
    lit "  Mixing versions may violate compat requirements and cause unexpected errors.\n" ++
    lit "  To use the manifest version" ++ lit (if one then "" else "s") ++ lit " instead, " ++
    lit (if cancelable && ongoing then "press `c` to cancel then " else "") ++
    -- julia starts in the default environment, so it needs no `--project` to get back there
    lit (if default_env then "restart julia." else "restart julia with `--project` set.")

/--
Julia source: base/precompilation.jl:2234-2258 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Explain, under the header, the reasons for precompiling during loading that a user
# can act on: a dependency loaded at another version, and compilation options that
# differ from the caches'. Printed while the session runs, so it can still be canceled,
# and again for requests merged in later, without repeating what was already said.
# Everything else is only in the loader's debug log.
function explain_reasons!(s::PrecompileSession, reasons::Dict{Symbol,Int}=s.reasons)
    s._from_loading || return
    pkgs = setdiff(s.requested_pkgids, s.explained_pkgids)
    union!(s.explained_pkgids, pkgs)
    conflicts = setdiff(loaded_version_conflicts(s, pkgs), s.explained_conflicts)
    if !isempty(conflicts)
        println(s.logio, loaded_conflicts_message(conflicts, s.hascolor; ongoing=true, cancelable=BG.key_controls))
        append!(s.explained_conflicts, conflicts)
    end
    for (dependents, deps, envdir) in stacked_version_conflicts(s, pkgs)
        println(s.logio, stacked_conflicts_message(dependents, deps, envdir, s.hascolor))
    end
    if !s.flags_explained && only_flags_mismatch(reasons)
        s.flags_explained = true
        println(s.logio, "  The existing caches were built with ",
            color_string("different compilation options", Base.warn_color(), s.hascolor),
            " (such as `--check-bounds` or `-O`), so packages are being precompiled for this session's options.")
    end
end

```
-/
def explain_reasons [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T) (s : T.Sess)
    (reasons : Option (T.Dict Bytes JInt64) := none) : m Unit := do
  let reasons := reasons.getD (← o.sget s).reasons
  if !(← o.sget s)._from_loading then return
  let st ← o.sget s
  let pkgs := vsetdiff st.requested_pkgids (setIn o.D st.explained_pkgids)
  o.smodify s fun st => { st with explained_pkgids := pkgs.foldl (setPush o.D) st.explained_pkgids }
  let lvc ← loaded_version_conflicts o s pkgs
  let conflicts := vsetdiff lvc (← o.sget s).explained_conflicts.contains
  let logio := o.ctx (← o.sget s).logio
  let hascolor := (← o.sget s).hascolor
  if !conflicts.isEmpty then
    let cancelable := (← o.bgget).key_controls
    println o logio (← loaded_conflicts_message o conflicts hascolor true cancelable)
    o.smodify s fun st => { st with explained_conflicts := st.explained_conflicts ++ conflicts }
  for (dependents, deps, envdir) in ← stacked_version_conflicts o s pkgs do
    println o logio (← stacked_conflicts_message o dependents deps envdir hascolor)
  if !(← o.sget s).flags_explained then
    if ← only_flags_mismatch o reasons then
      o.smodify s fun st => { st with flags_explained := true }
      println o logio (lit "  The existing caches were built with " ++
        (← color_string (lit "different compilation options") (← o.warn_color) hascolor) ++
        lit " (such as `--check-bounds` or `-O`), so packages are being precompiled for this session's options.")

/--
Julia source: base/precompilation.jl:2227-2233 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function print_header(s::PrecompileSession)
    printpkgstyle(s.logio, :Precompiling, s.target)
    s.header_printed = true
    explain_reasons!(s)
    BG.verbose && println(s.logio, format_verbose_timing_header())
end

```
-/
def print_header [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T) (s : T.Sess) : m Unit := do
  pps o (o.ctx (← o.sget s).logio) "Precompiling" (← o.sget s).target
  o.smodify s fun st => { st with header_printed := true }
  explain_reasons o s
  if (← o.bgget).verbose then println o (o.ctx (← o.sget s).logio) format_verbose_timing_header

end session

section tasks
variable {m : Type → Type} [Monad m] [MonadExceptOf PError m] {T : Rt}
open JuliaLean.base.float (sub_float add_float mul_float div_float lt_float le_float uitofp sitofp)

/-- Runs `x`, returning its exception as a value. -/
def catchE {α : Type} (x : m α) : m (Except PError α) :=
  tryCatchThe PError (Except.ok <$> x) fun e => pure (.error e)

/-- Runs `x`; an exception it throws is returned together with `cd`, the value of the local
`cursor_disabled` at that point (read by the print loop's `finally`). -/
def step {α : Type} (cd : Bool) (x : m α) : ExceptT (PError × Bool) m α :=
  ExceptT.mk do
    let r ← catchE x
    pure (match r with
      | .ok a => .ok a
      | .error e => .error (e, cd))

/-- `findfirst(pat, s)` of strings: the byte offset of the first match. -/
def findSub (pat s : Bytes) : Option Nat :=
  (List.range (s.length + 1)).find? fun i => pat.isPrefixOf (s.drop i)

def spaces12 : Bytes := lit "            "

/-- `Base.PRECOMPILE_VERBOSE_TIMING_MARKER` (`base/loading.jl`). -/
def PRECOMPILE_VERBOSE_TIMING_MARKER : Bytes := lit "__JL_PRECOMP_VERBOSE_TIMING__"

/-- `Base.loaded_modules[pkg]`. -/
def loadedModuleIndex [MonadFinally m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T) (pkg : PkgId) : m T.Mod := do
  match ← o.loadedModule pkg with
  | some md => return md
  | none => throwP .keyError

/-- `s.n_loaded += 1; push!(s.loaded_pkgs, pkg)`. -/
def note_loaded [MonadFinally m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T) (s : T.Sess) (pkg : PkgId) : m Unit :=
  o.smodify s fun st => { st with n_loaded := st.n_loaded + ji 1, loaded_pkgs := st.loaded_pkgs ++ [pkg] }

/-- `push!(freshpaths, path)`, where `freshpaths` is the vector stored at `s.cachepath_cache[pkg]`. -/
def push_freshpath [MonadFinally m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T) (s : T.Sess) (pkg : PkgId) (path : Bytes) : m Unit :=
  o.smodify s fun st => { st with cachepath_cache := o.D.set st.cachepath_cache pkg (getD o.D st.cachepath_cache pkg [] ++ [path]) }

/-- `@elapsed ex`: `(time_ns() -% t0) / 1e9` around `ex`, with its value. -/
def elapsed [MonadFinally m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] {α : Type} (o : Ops m T) (x : m α) : m (F64 × α) := do
  let t0 ← o.time_ns
  let a ← x
  let t1 ← o.time_ns
  return (div_float (uitofp .f64 (t1 - t0)) (fl 0x41CDCD6500000000), a)

/--
Julia source: base/precompilation.jl:2366-2514 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function spawn_print_loop!(s::PrecompileSession)
    Threads.@spawn :samepool begin
        cursor_disabled = false
        t = nothing
        try
            wait(s.first_started)
            (isempty(s.pkg_queue) || s.interrupted_or_done) && return
            @lock s.print_lock begin
                BG.monitoring && print_header(s)
            end
            t = Timer(0; interval=1/10)
            anim_chars = ["◐","◓","◑","◒"]
            i = 1
            bar = MiniProgressBar(; indent=0, header = "Precompiling packages ", color = :green, percentage=false, always_reprint=true)
            bar.max = s.n_total - s.n_already_precomp
            final_loop = false
            last_poll_time = time()
            cpu_pcts = Dict{Int32, Float64}()
            rss_bytes = Dict{Int32, UInt64}()
            while !s.printloop_should_exit
                # Propagate cancel/interrupt requested via BG into the session so the loop exits.
                should_stop(s)
                @lock s.print_lock begin
                    verbose = BG.verbose
                    now_time = time()
                    dt = now_time - last_poll_time
                    if verbose && dt >= 0.5
                        poll_process_stats!(cpu_pcts, rss_bytes, s.prev_cpu_times, s.jobs, dt)
                        last_poll_time = now_time
                    end
                    term_size = displaysize(s.logio)::Tuple{Int, Int}
                    num_deps_show = max(term_size[1] - 3, 2) # show at least 2 deps
                    pkg_queue_show = if !s.interrupted_or_done && length(s.pkg_queue) > num_deps_show
                        last(s.pkg_queue, num_deps_show)
                    else
                        s.pkg_queue
                    end
                    i_local = i
                    final_loop_local = final_loop
                    tip, tip_color = @lock BG begin
                        if BG.confirming !== :none && time() >= BG.confirm_deadline
                            BG.confirming = :none
                        end
                        keyboard_tip(BG)
                    end
                    str_ = sprint(; context=s.logio) do iostr
                        if i_local > 1
                            print(iostr, ansi_cleartoend)
                        end
                        bar.header = verbose ? "Precompiling ($(s.num_tasks) tasks) " : "Precompiling packages "
                        # max(0,...) guards against a race where the print loop runs after
                        # n_already_precomp is incremented but before n_done is incremented,
                        # which would otherwise produce a negative value and crash repeat().
                        bar.current = max(0, s.n_done - s.n_already_precomp)
                        bar.max = max(0, s.n_total - s.n_already_precomp)
                        termwidth = (displaysize(s.logio)::Tuple{Int,Int})[2]
                        if !final_loop_local
                            tip_width = isempty(tip) ? 0 : textwidth(tip) + 1
                            bar_termwidth = termwidth - tip_width
                            s_bar = sprint(io -> show_progress(io, bar; termwidth=bar_termwidth, carriagereturn=false); context=s.logio)
                            if !isempty(tip)
                                s_bar = string(s_bar, " ", color_string(tip, tip_color, s.hascolor))
                            end
                            print(iostr, Base._truncate_at_width_or_chars(true, s_bar, termwidth), "\n")
                        end
                        for pkg_config in pkg_queue_show
                            dep, config = pkg_config
                            loaded = s.warn_loaded && (dep in s.start_loaded_modules)
                            flags, cacheflags = config
                            name = describe_pkg(s, dep, dep in s.project_deps, dep in s.serial_deps, flags, cacheflags)
                            job = s.jobs[pkg_config]
                            line = if is_soft_error(job)
                                string(color_string("  ? ", Base.warn_color(), s.hascolor), name)
                            elseif is_failed(job)
                                string(color_string("  ✗ ", Base.error_color(), s.hascolor), name)
                            elseif is_dep_failed(job)
                                string(color_string("  ✗ ", Base.error_color(), s.hascolor), name,
                                       color_string(" (skipped, $(job.error_msg) failed to precompile)", :light_black, s.hascolor))
                            elseif is_recompiled(job)
                                !loaded && s.interrupted_or_done && continue
                                loaded || Base.errormonitor(Threads.@spawn :samepool begin
                                    sleep(1);
                                    @lock s.print_lock filter!(!isequal(pkg_config), s.pkg_queue)
                                end)
                                string(color_string("  ✓ ", loaded ? Base.warn_color() : :green, s.hascolor), name)
                            elseif is_started(job) && s.interrupted_or_done
                                # Cancel/interrupt: show a static marker for jobs that actually had
                                # a subprocess running, so the user sees what was in flight without
                                # it looking still-running. Skip jobs that hadn't reached subprocess
                                # spawn yet (e.g. still acquiring the parallel_limiter).
                                had_pid(job) || continue
                                string(color_string("  - ", :light_black, s.hascolor), name)
                            elseif is_started(job)
                                anim_char = anim_chars[(i_local + Int(dep.name[1])) % length(anim_chars) + 1]
                                anim_char_colored = dep in s.project_deps ? anim_char : color_string(anim_char, :light_black, s.hascolor)
                                waiting = if is_locked(job)
                                    color_string(" Being precompiled by $(job.lock_holder)", Base.info_color(), s.hascolor)
                                elseif is_waiting(job)
                                    color_string(" Waiting for background task / IO / timer. Interrupt to inspect", Base.warn_color(), s.hascolor)
                                else
                                    ""
                                end

                                pid_info = if verbose && has_pid(job)
                                    elapsed_str = string(round(Int, now_time - job.started_at), "s")
                                    pid = job.pid
                                    pct = get(cpu_pcts, pid, -1.0)
                                    pct_str = pct >= 0 ? string(" | cpu ", round(Int, pct), "%") : ""
                                    mem = get(rss_bytes, pid, UInt64(0))
                                    mem_str = mem > 0 ? string(" | ", Base.format_bytes(mem)) : ""
                                    color_string(" $(elapsed_str) | pid $(pid)$(pct_str)$(mem_str)", Base.info_color(), s.hascolor)
                                else
                                    ""
                                end
                                string("  ", anim_char_colored, " ", name, pid_info, waiting)
                            else
                                string("    ", name)
                            end
                            println(iostr, Base._truncate_at_width_or_chars(true, line, termwidth))
                        end
                    end
                    n_print_rows = count("\n", str_)
                    s.printloop_should_exit = s.interrupted_or_done && final_loop
                    final_loop = s.interrupted_or_done
                    i += 1
                    if BG.monitoring
                        if s.fancyprint && !cursor_disabled
                            print(s.logio, ansi_disablecursor)
                            cursor_disabled = true
                        end
                        if s.printloop_should_exit
                            print(s.logio, str_)
                        else
                            print(s.logio, str_, ansi_moveup(n_print_rows), ansi_movecol1)
                        end
                    elseif cursor_disabled
                        print(s.logio, ansi_enablecursor)
                        cursor_disabled = false
                    end
                end
                wait(t)
            end
        finally
            t === nothing || close(t)
            cursor_disabled && print(s.logio, ansi_enablecursor)
        end
    end
end

```
-/
/- The locals of the print loop. -/
structure PrintLoopState (T : Rt) where
  cursor_disabled : Bool
  i : JInt64
  bar : MiniProgressBar
  final_loop : Bool
  last_poll_time : F64
  cpu_pcts : T.Dict (JInt .i32) F64
  rss_bytes : T.Dict (JInt .i32) (JInt .u64)

def anim_chars : List Bytes := [lit "◐", lit "◓", lit "◑", lit "◒"]

/-- One line of the `for pkg_config in pkg_queue_show` loop; `none` is `continue`. -/
def queue_line [MonadFinally m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T) (s : T.Sess) (verbose : Bool) (now_time : F64) (i_local : JInt64)
    (cpu_pcts : T.Dict (JInt .i32) F64) (rss_bytes : T.Dict (JInt .i32) (JInt .u64)) (pkg_config : PkgConfig T) :
    m (Option Bytes) := do
  let (dep, config) := pkg_config
  let st ← o.sget s
  let loaded := st.warn_loaded && setIn o.D st.start_loaded_modules dep
  let (flags, cacheflags) := config
  let name ← describe_pkg o s dep (st.project_deps.contains dep) (st.serial_deps.contains dep) flags cacheflags
  let job ← getJob o s pkg_config
  let hascolor := st.hascolor
  if is_soft_error job then
    return some ((← color_string (lit "  ? ") (← o.warn_color) hascolor) ++ name)
  else if is_failed job then
    return some ((← color_string (lit "  ✗ ") (← o.error_color) hascolor) ++ name)
  else if is_dep_failed job then
    return some ((← color_string (lit "  ✗ ") (← o.error_color) hascolor) ++ name ++
      (← color_string (lit " (skipped, " ++ job.error_msg ++ lit " failed to precompile)") (.symbol "light_black") hascolor))
  else if is_recompiled job then
    if !loaded && (← o.sget s).interrupted_or_done then return none
    if !loaded then
      let t ← o.spawn do
        o.baseline.sleep (fl 0x3FF0000000000000)
        o.withLock (← o.sget s).print_lock
          (o.smodify s fun st => { st with pkg_queue := st.pkg_queue.filter (· != pkg_config) })
      o.errormonitor t
    let c ← if loaded then o.warn_color else pure (.symbol "green")
    return some ((← color_string (lit "  ✓ ") c hascolor) ++ name)
  else if is_started job && (← o.sget s).interrupted_or_done then
    -- Cancel/interrupt: show a static marker for jobs that actually had
    -- a subprocess running, so the user sees what was in flight without
    -- it looking still-running. Skip jobs that hadn't reached subprocess
    -- spawn yet (e.g. still acquiring the parallel_limiter).
    if !had_pid job then return none
    return some ((← color_string (lit "  - ") (.symbol "light_black") hascolor) ++ name)
  else if is_started job then
    let code ← o.firstCharCode dep.name
    -- `anim_chars[(i_local + Int(dep.name[1])) % length(anim_chars) + 1]`; `%` is `rem`
    let idx := (i_local + code).val.tmod 4 + 1
    let anim_char ← if idx < 1 then throwP .boundsError else
      match anim_chars[(idx - 1).toNat]? with
      | some a => pure a
      | none => throwP .boundsError
    let anim_char_colored ← if (← o.sget s).project_deps.contains dep then pure anim_char
      else color_string anim_char (.symbol "light_black") hascolor
    let waiting ← if is_locked job then
        color_string (lit " Being precompiled by " ++ job.lock_holder) (← o.info_color) hascolor
      else if is_waiting job then
        color_string (lit " Waiting for background task / IO / timer. Interrupt to inspect") (← o.warn_color) hascolor
      else pure []
    let pid_info ← if verbose && has_pid job then do
        let elapsed_str := istr (← o.roundInt (sub_float now_time job.started_at)) ++ lit "s"
        let pid := job.pid
        let pct := getD o.D cpu_pcts pid (fl 0xBFF0000000000000)
        let pct_str ← if le_float (fl 0) pct then do
            pure (lit " | cpu " ++ istr (← o.roundInt pct) ++ lit "%")
          else pure []
        let mem := getD o.D rss_bytes pid (JInt.wrap .u64 0)
        let mem_str ← if mem.val > 0 then do pure (lit " | " ++ (← o.formatBytes mem)) else pure []
        color_string (lit " " ++ elapsed_str ++ lit " | pid " ++ istr pid ++ pct_str ++ mem_str) (← o.info_color) hascolor
      else pure []
    return some (lit "  " ++ anim_char_colored ++ lit " " ++ name ++ pid_info ++ waiting)
  else
    return some (lit "    " ++ name)

/-- The body of `@lock s.print_lock begin ... end` in the print loop. -/
def print_loop_body [MonadFinally m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T) (s : T.Sess) (st : PrintLoopState T) : ExceptT (PError × Bool) m (PrintLoopState T) := do
  let cd := st.cursor_disabled
  let (str_, st) ← step cd (do
    let verbose := (← o.bgget).verbose
    let now_time ← o.time
    let dt := sub_float now_time st.last_poll_time
    let mut st := st
    if verbose && le_float (fl 0x3FE0000000000000) dt then
      let ss ← o.sget s
      let (c, r, prev, jobs) ← poll_process_stats o st.cpu_pcts st.rss_bytes ss.prev_cpu_times ss.jobs dt
      -- the poll writes `s.prev_cpu_times` and the jobs' `peak_rss_bytes` in place
      o.smodify s fun x => { x with prev_cpu_times := prev }
      for k in o.D.keys jobs do
        let j ← getindex o.D jobs k
        modifyJob o s k fun x => { x with peak_rss_bytes := j.peak_rss_bytes }
      st := { st with cpu_pcts := c, rss_bytes := r, last_poll_time := now_time }
    let term_size ← o.displaysize (← o.sget s).logio
    let num_deps_show := max (term_size.1 - ji 3).val 2 -- show at least 2 deps
    let ss ← o.sget s
    let pkg_queue_show :=
      if !ss.interrupted_or_done && (ss.pkg_queue.length : Int) > num_deps_show then
        ss.pkg_queue.drop (ss.pkg_queue.length - num_deps_show.toNat)
      else ss.pkg_queue
    let i_local := st.i
    let final_loop_local := st.final_loop
    let (tip, tip_color) ← lock_BG o do
      let bg ← o.bgget
      if bg.confirming != lit "none" then
        if le_float bg.confirm_deadline (← o.time) then
          o.bgmodify fun bg => { bg with confirming := lit "none" }
      keyboard_tip o (← o.bgget)
    let bar0 := st.bar
    let (str_, bar) ← o.sprintCtx (← o.sget s).logio fun iostr => do
      if i_local.val > 1 then o.print iostr ansi_cleartoend
      let ss ← o.sget s
      let header := if verbose then lit "Precompiling (" ++ istr ss.num_tasks ++ lit " tasks) "
        else lit "Precompiling packages "
      let mut bar := { bar0 with header := header }
      -- max(0,...) guards against a race where the print loop runs after
      -- n_already_precomp is incremented but before n_done is incremented,
      -- which would otherwise produce a negative value and crash repeat().
      bar := { bar with current := ji (max 0 (ss.n_done - ss.n_already_precomp).val) }
      bar := { bar with max := ji (max 0 (ss.n_total - ss.n_already_precomp).val) }
      let termwidth := (← o.displaysize (← o.sget s).logio).2
      if !final_loop_local then
        let tip_width : Int := if tip.isEmpty then 0 else (o.progress.textwidth tip).val + 1
        let bar_termwidth := JInt.wrap .i64 (termwidth.val - tip_width)
        let (s_bar, bar') ← o.sprintCtx (← o.sget s).logio fun io =>
          show_progress o.progress io bar (some bar_termwidth) false
        bar := bar'
        let mut s_bar := s_bar
        if !tip.isEmpty then
          s_bar := s_bar ++ lit " " ++ (← color_string tip tip_color ss.hascolor)
        o.print iostr (o.truncate_at_width s_bar termwidth ++ lit "\n")
      for pkg_config in pkg_queue_show do
        let line ← queue_line o s verbose now_time i_local st.cpu_pcts st.rss_bytes pkg_config
        match line with
        | none => continue
        | some line => println o iostr (o.truncate_at_width line termwidth)
      return bar
    let n_print_rows := ji (str_.filter (· == 10)).length
    let iod ← do pure (← o.sget s).interrupted_or_done
    o.smodify s fun x => { x with printloop_should_exit := iod && st.final_loop }
    let final_loop := (← o.sget s).interrupted_or_done
    return ((str_, n_print_rows), { st with bar, final_loop, i := st.i + ji 1 }))
  let (str_, n_print_rows) := str_
  let logio := o.ctx (← step cd (do return (← o.sget s).logio))
  let mut cd := cd
  if ← step cd (do return (← o.bgget).monitoring) then
    if (← step cd (do return (← o.sget s).fancyprint)) && !cd then
      step cd (o.print logio ansi_disablecursor)
      cd := true
    if ← step cd (do return (← o.sget s).printloop_should_exit) then
      step cd (o.print logio str_)
    else
      step cd (o.print logio (str_ ++ ansi_moveup istr n_print_rows ++ ansi_movecol1))
  else if cd then
    step cd (o.print logio ansi_enablecursor)
    cd := false
  return { st with cursor_disabled := cd }

/-- One iteration of `while !s.printloop_should_exit`. -/
def print_loop_iter [MonadFinally m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T) (s : T.Sess) (t : T.Tmr) (st : PrintLoopState T) :
    ExceptT (PError × Bool) m (PrintLoopState T) := do
  -- Propagate cancel/interrupt requested via BG into the session so the loop exits.
  discard <| step st.cursor_disabled (should_stop o s)
  let lk ← step st.cursor_disabled (do return (← o.sget s).print_lock)
  let st ← ExceptT.mk (o.withLock lk (print_loop_body o s st).run)
  step st.cursor_disabled (o.waitTimer t)
  return st

/-- The `while !s.printloop_should_exit` loop: the exception that ended it, if any, and the final
`cursor_disabled`. -/
def print_loop [MonadFinally m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T) (s : T.Sess) (t : T.Tmr) (st : PrintLoopState T) : m (Option PError × Bool) := do
  let ex ← catchE (do return (← o.sget s).printloop_should_exit)
  match ex with
  | .error e => pure (some e, st.cursor_disabled)
  | .ok b =>
    if b then pure (none, st.cursor_disabled)
    else do
      let r ← (print_loop_iter o s t st).run
      match r with
      | .error ecd => pure (some ecd.1, ecd.2)
      | .ok st' => print_loop o s t st'
partial_fixpoint

/-- `spawn_print_loop!(s)`. -/
def spawn_print_loop [MonadFinally m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T) (s : T.Sess) : m T.Tsk :=
  o.spawn do
    let pre ← catchE (do
      o.waitEv (← o.sget s).first_started
      let ss ← o.sget s
      if ss.pkg_queue.isEmpty || ss.interrupted_or_done then return none
      o.withLock ss.print_lock do
        if (← o.bgget).monitoring then print_header o s
      some <$> o.newTimer (fl 0) (div_float (fl 0x3FF0000000000000) (fl 0x4024000000000000)))
    match pre with
    | .error e => throwThe PError e -- `t === nothing` and `cursor_disabled == false`: the `finally` does nothing
    | .ok none => return ()
    | .ok (some t) =>
      let init ← catchE (do
        let ss ← o.sget s
        let bar : MiniProgressBar :=
          { indent := ji 0, header := lit "Precompiling packages ", color := lit "green", percentage := false,
            always_reprint := true }
        let bar := { bar with max := ss.n_total - ss.n_already_precomp }
        let last_poll_time ← o.time
        return (⟨false, ji 1, bar, false, last_poll_time, o.D.empty, o.D.empty⟩ : PrintLoopState T))
      let res ← match init with
        | .error e => pure (some e, false)
        | .ok st0 => print_loop o s t st0
      -- finally
      o.closeTimer t
      if res.2 then o.print (o.ctx (← o.sget s).logio) ansi_enablecursor
      match res.1 with
      | some e => throwThe PError e
      | none => return ()

/--
Julia source: base/precompilation.jl:2515-2553 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function precompilepkgs_monitor_std(s::PrecompileSession, pkg_config, job::PrecompileJob, pipe, single_requested_pkg::Bool)
    pkg, _ = pkg_config
    liveprinting = false
    thistaskwaiting = false
    while !eof(pipe)
        str = readline(pipe, keep=true)
        # the marker may follow package output that lacks a trailing newline
        i = findfirst(Base.PRECOMPILE_VERBOSE_TIMING_MARKER, str)
        if i !== nothing
            job.verbose_timing = strip(SubString(str, first(i)))
            str = str[1:prevind(str, first(i))]
            isempty(str) && continue
        end
        if single_requested_pkg && (liveprinting || !isempty(str))
            BG.monitoring && @lock s.print_lock begin
                if !liveprinting
                    liveprinting = true
                    s.pkg_liveprinted = pkg
                end
                # in fancy mode clear the progress bar residue from the line first
                print(s.io, s.fancyprint ? ansi_cleartoendofline : "", str)
            end
        end
        write(job.output, str)
        if !thistaskwaiting && occursin("Waiting for background task / IO / timer", str)
            thistaskwaiting = true
            !liveprinting && !s.fancyprint && BG.monitoring && @lock s.print_lock begin
                println(s.io, full_name(s.ext_to_parent, pkg), color_string(str, Base.warn_color(), s.hascolor))
            end
            job.waiting_for_bg = true
        elseif !thistaskwaiting
            # XXX: don't just re-enable IO for random packages without printing the context for them first
            !liveprinting && !s.fancyprint && BG.monitoring && @lock s.print_lock begin
                print(s.io, str)
            end
        end
    end
end

```
-/
/- One iteration of the `while !eof(pipe)` loop of `precompilepkgs_monitor_std`; returns
`(liveprinting, thistaskwaiting)`. The `job` argument is `s.jobs[pkg_config]`. -/
def monitor_std_step [MonadFinally m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T) (s : T.Sess) (pkg_config : PkgConfig T) (pipe : T.Pipe)
    (single_requested_pkg liveprinting thistaskwaiting : Bool) : m (Bool × Bool) := do
  let pkg := pkg_config.1
  let mut str ← o.readlineKeep pipe
  -- the marker may follow package output that lacks a trailing newline
  match findSub PRECOMPILE_VERBOSE_TIMING_MARKER str with
  | some i =>
    modifyJob o s pkg_config fun j => { j with verbose_timing := o.strip (str.drop i) }
    str := str.take i
    if str.isEmpty then return (liveprinting, thistaskwaiting)
  | none => pure ()
  let mut liveprinting := liveprinting
  if single_requested_pkg && (liveprinting || !str.isEmpty) then
    if (← o.bgget).monitoring then
      let lp := liveprinting
      liveprinting ← o.withLock (← o.sget s).print_lock do
        if !lp then
          o.smodify s fun st => { st with pkg_liveprinted := some pkg }
        -- in fancy mode clear the progress bar residue from the line first
        let ss ← o.sget s
        o.print (o.ctx ss.io) ((if ss.fancyprint then ansi_cleartoendofline else []) ++ str)
        return true
  o.bufWrite (← getJob o s pkg_config).output str
  let mut thistaskwaiting := thistaskwaiting
  if !thistaskwaiting && (findSub (lit "Waiting for background task / IO / timer") str).isSome then
    thistaskwaiting := true
    if !liveprinting && !(← o.sget s).fancyprint then
      if (← o.bgget).monitoring then
        o.withLock (← o.sget s).print_lock do
          let ss ← o.sget s
          println o (o.ctx ss.io) ((← full_name o.D ss.ext_to_parent pkg) ++ (← color_string str (← o.warn_color) ss.hascolor))
    modifyJob o s pkg_config fun j => { j with waiting_for_bg := true }
  else if !thistaskwaiting then
    -- XXX: don't just re-enable IO for random packages without printing the context for them first
    if !liveprinting && !(← o.sget s).fancyprint then
      if (← o.bgget).monitoring then
        o.withLock (← o.sget s).print_lock do
          o.print (o.ctx (← o.sget s).io) str
  return (liveprinting, thistaskwaiting)

/-- The `while !eof(pipe)` loop. -/
def monitor_std_loop [MonadFinally m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T) (s : T.Sess) (pkg_config : PkgConfig T) (pipe : T.Pipe)
    (single_requested_pkg liveprinting thistaskwaiting : Bool) : m Unit := do
  if ← o.eofPipe pipe then return ()
  let r ← monitor_std_step o s pkg_config pipe single_requested_pkg liveprinting thistaskwaiting
  monitor_std_loop o s pkg_config pipe single_requested_pkg r.1 r.2
partial_fixpoint

/-- `precompilepkgs_monitor_std(s, pkg_config, job, pipe, single_requested_pkg)`. -/
def precompilepkgs_monitor_std [MonadFinally m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T) (s : T.Sess) (pkg_config : PkgConfig T) (pipe : T.Pipe)
    (single_requested_pkg : Bool) : m Unit :=
  monitor_std_loop o s pkg_config pipe single_requested_pkg false false

/--
Julia source: base/precompilation.jl:2554-2598 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Can be merged with `maybe_cachefile_lock` in loading?
# Wraps the precompilation function `f` with cachefile lock handling.
# Returns the result from `f()`, which can be:
#   - `nothing`: cache already existed
#   - `Tuple{String, Union{Nothing, String}}`: this process just compiled
#   - `Exception`: compilation failed
function precompile_pkgs_maybe_cachefile_lock(f, s::PrecompileSession, pkg_config, job::PrecompileJob, fullname)
    if !(isdefined(Base, :mkpidlock_hook) && isdefined(Base, :trymkpidlock_hook) && Base.isdefined(Base, :parse_pidfile_hook))
        return f()
    end
    pkg, config = pkg_config
    _, cacheflags = config
    stale_age = Base.compilecache_pidlock_stale_age
    pidfile = Base.compilecache_pidfile_path(pkg, flags=cacheflags)
    cachefile = @invokelatest Base.trymkpidlock_hook(f, pidfile; stale_age)
    if cachefile === false
        pid, hostname, _ = @invokelatest Base.parse_pidfile_hook(pidfile)
        job.lock_holder = if isempty(hostname) || hostname == gethostname()
            if pid == getpid()
                "an async task in this process (pidfile: $pidfile)"
            else
                "another process (pid: $pid, pidfile: $pidfile)"
            end
        else
            "another machine (hostname: $hostname, pid: $pid, pidfile: $pidfile)"
        end
        !s.fancyprint && BG.monitoring && @lock s.print_lock begin
            println(s.io, "    ", fullname, color_string(" Being precompiled by $(job.lock_holder)", Base.info_color(), s.hascolor))
        end
        Base.release(s.parallel_limiter) # release so other work can be done while waiting
        try
            # wait until the lock is available
            cachefile = @invokelatest Base.mkpidlock_hook(() -> begin
                    job.lock_holder = ""
                    # this worker already had a slot before it waited for the lock, so take the next one
                    Base.acquire(f, s.parallel_limiter; priority=Inf, cancel=() -> should_stop(s))
                end,
                pidfile; stale_age)
        finally
            Base.acquire(s.parallel_limiter; priority=Inf, cancel=() -> should_stop(s)) # re-acquire so the outer release is balanced
        end
    end
    return cachefile
end

```
-/
/- `precompile_pkgs_maybe_cachefile_lock(f, s, pkg_config, job, fullname)`; the `job` is
`s.jobs[pkg_config]` and `Base.compilecache_pidlock_stale_age` is `10`. -/
def precompile_pkgs_maybe_cachefile_lock [MonadFinally m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T) (f : m CompileResult) (s : T.Sess)
    (pkg_config : PkgConfig T) (fullname : Bytes) : m CompileResult := do
  if !(← o.pidlockHooksDefined) then return ← f
  let (pkg, config) := pkg_config
  let (_, cacheflags) := config
  let stale_age := ji 10
  let pidfile ← o.compilecache_pidfile_path pkg cacheflags
  let cachefile ← o.trymkpidlock_hook f pidfile stale_age
  match cachefile with
  | some r => return r
  | none =>
    let (pid, hostname) ← o.parse_pidfile_hook pidfile
    let same_host ← if hostname.isEmpty then pure true else do pure (hostname == (← o.gethostname))
    let lock_holder ← if same_host then do
        if pid.val == (← o.getpid).val then
          pure (lit "an async task in this process (pidfile: " ++ pidfile ++ lit ")")
        else
          pure (lit "another process (pid: " ++ istr pid ++ lit ", pidfile: " ++ pidfile ++ lit ")")
      else
        pure (lit "another machine (hostname: " ++ hostname ++ lit ", pid: " ++ istr pid ++ lit ", pidfile: " ++
          pidfile ++ lit ")")
    modifyJob o s pkg_config fun j => { j with lock_holder := lock_holder }
    if !(← o.sget s).fancyprint then
      if (← o.bgget).monitoring then
        o.withLock (← o.sget s).print_lock do
          let ss ← o.sget s
          let holder := (← getJob o s pkg_config).lock_holder
          println o (o.ctx ss.io) (lit "    " ++ fullname ++
            (← color_string (lit " Being precompiled by " ++ holder) (← o.info_color) ss.hascolor))
    let w := (← o.sget s).parallel_limiter
    let inf : F64 := fl 0x7FF0000000000000
    release o.jobserver o.limiter w -- release so other work can be done while waiting
    -- wait until the lock is available
    tryFinally
      (o.mkpidlock_hook (do
          modifyJob o s pkg_config fun j => { j with lock_holder := [] }
          -- this worker already had a slot before it waited for the lock, so take the next one
          acquire_f o.jobserver o.limiter o.baseline f w inf (should_stop o s))
        pidfile stale_age)
      -- re-acquire so the outer release is balanced
      (acquire o.jobserver o.limiter o.baseline w inf (should_stop o s))

/--
Julia source: base/precompilation.jl:2599-2614 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Rough proxy for how long a package takes to precompile, used only to order
# scheduling: the bytes of Julia source next to its entry file.
function precompile_cost_estimate(spec::Union{Nothing,Base.PkgLoadSpec})
    spec === nothing && return 1.0
    total = 0
    try
        for (root, _, files) in walkdir(dirname(spec.path))
            for f in files
                endswith(f, ".jl") && (total += filesize(joinpath(root, f)))
            end
        end
    catch
    end
    return max(1.0, Float64(total))
end

```
-/
def precompile_cost_estimate [MonadFinally m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T) (spec : Option T.Spec) : m F64 := do
  let some spec := spec | return fl 0x3FF0000000000000
  let mut total : JInt64 := ji 0
  -- `try ... catch end`: an exception ends the walk, keeping the total so far
  let entries ← catchE (do o.walkdir (← o.env.dirname (o.specPath spec)))
  match entries with
  | .error _ => pure ()
  | .ok es =>
    for e in es do
      match e with
      | .error _ => break
      | .ok (root, _, files) =>
        let mut stop := false
        for f in files do
          if (lit ".jl").isSuffixOf f then
            let r ← catchE (do o.filesize (← o.env.joinpath root f))
            match r with
            | .ok n => total := total + n
            | .error _ =>
              stop := true
              break
        if stop then break
  return o.maxF (fl 0x3FF0000000000000) (sitofp .f64 total)

/--
Julia source: base/precompilation.jl:2615-2639 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Scheduling priority of each package: its own estimated cost plus that of the
# longest chain of packages that cannot start until it is done. Handing worker
# slots out in this order starts the environment's critical path as early as
# possible; in a cold precompile of a large environment the last package on that
# path, not the total amount of work, sets the wall-clock time.
# Computed on demand, so a run with little to compile doesn't read every package's source.
struct SchedulePriorities
    lock::ReentrantLock
    dependents::Dict{PkgId,Vector{PkgId}}
    sourcespecs::Dict{PkgId,Union{Nothing,Base.PkgLoadSpec}}
    cost::Dict{PkgId,Float64}
    height::Dict{PkgId,Float64}
    visiting::Set{PkgId}
end

function SchedulePriorities(direct_deps::Dict{PkgId,Vector{PkgId}},
                            sourcespecs::Dict{PkgId,Union{Nothing,Base.PkgLoadSpec}})
    dependents = Dict{PkgId,Vector{PkgId}}()
    for (pkg, deps) in direct_deps, dep in deps
        push!(get!(Vector{PkgId}, dependents, dep), pkg)
    end
    return SchedulePriorities(ReentrantLock(), dependents, sourcespecs,
                              Dict{PkgId,Float64}(), Dict{PkgId,Float64}(), Set{PkgId}())
end

```
-/
def SchedulePriorities_new [MonadFinally m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T) (direct_deps : T.Dict PkgId (List PkgId))
    (sourcespecs : T.Dict PkgId (Option T.Spec)) : m T.Prio := do
  let mut dependents : T.Dict PkgId (List PkgId) := o.D.empty
  for pkg in o.D.keys direct_deps do
    for dep in ← getindex o.D direct_deps pkg do
      dependents := o.D.set dependents dep (getD o.D dependents dep [] ++ [pkg])
  o.prioNew ⟨← o.newLock, dependents, sourcespecs, o.D.empty, o.D.empty, o.D.empty⟩

/--
Julia source: base/precompilation.jl:2642-2655 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# A top-level function rather than a local one so the recursion does not box it.
function schedule_height!(p::SchedulePriorities, pkg::PkgId)
    haskey(p.height, pkg) && return p.height[pkg]
    pkg in p.visiting && return 0.0 # circular dependency, reported elsewhere
    push!(p.visiting, pkg)
    best = 0.0
    for d in get(p.dependents, pkg, PkgId[])
        best = max(best, schedule_height!(p, d))
    end
    delete!(p.visiting, pkg)
    cost = get!(() -> precompile_cost_estimate(get(p.sourcespecs, pkg, nothing)), p.cost, pkg)
    return p.height[pkg] = cost + best
end

```
-/
/- `get!(() -> precompile_cost_estimate(get(p.sourcespecs, pkg, nothing)), p.cost, pkg)`. -/
def schedule_cost [MonadFinally m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T) (p : T.Prio) (pkg : PkgId) : m F64 := do
  let pr ← o.prioGet p
  match o.D.get pr.cost pkg with
  | some c => return c
  | none =>
    let c ← precompile_cost_estimate o (getD o.D pr.sourcespecs pkg none)
    o.prioModify p fun pr => { pr with cost := o.D.set pr.cost pkg c }
    return c

mutual
/-- `schedule_height!(p, pkg)`. -/
def schedule_height [MonadFinally m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T) (p : T.Prio) (pkg : PkgId) : m F64 := do
  let pr ← o.prioGet p
  if let some h := o.D.get pr.height pkg then return h
  if setIn o.D pr.visiting pkg then return fl 0 -- circular dependency, reported elsewhere
  o.prioModify p fun pr => { pr with visiting := setPush o.D pr.visiting pkg }
  let best ← schedule_height_loop o p (getD o.D pr.dependents pkg []) (fl 0)
  o.prioModify p fun pr => { pr with visiting := o.D.delete pr.visiting pkg }
  let cost ← schedule_cost o p pkg
  let h := add_float cost best
  o.prioModify p fun pr => { pr with height := o.D.set pr.height pkg h }
  return h
partial_fixpoint

/-- The `for d in get(p.dependents, pkg, PkgId[])` loop of `schedule_height!`. -/
def schedule_height_loop [MonadFinally m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T) (p : T.Prio) : List PkgId → F64 → m F64
  | [], best => pure best
  | d :: rest, best => do
    let h ← schedule_height o p d
    schedule_height_loop o p rest (o.maxF best h)
partial_fixpoint
end

/--
Julia source: base/precompilation.jl:2640-2641 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
schedule_priority(p::SchedulePriorities, pkg::PkgId) = @lock p.lock schedule_height!(p, pkg)

```
-/
def schedule_priority [MonadFinally m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T) (p : T.Prio) (pkg : PkgId) : m F64 := do
  o.withLock (← o.prioGet p).lock (schedule_height o p pkg)

/--
Julia source: base/precompilation.jl:2656-2659 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Standard libraries ship precompiled with julia, so `force` leaves them alone
# unless `force_stdlibs` is set.
is_stdlib_source(spec::Base.PkgLoadSpec) = startswith(spec.path, Sys.STDLIB)

```
-/
def is_stdlib_source [MonadFinally m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T) (spec : T.Spec) : Bool := o.env.STDLIB.isPrefixOf (o.specPath spec)

/--
Julia source: base/precompilation.jl:2660-2674 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Name of the package whose failure means `deps` cannot be loaded: the first
# dependency whose worker ran and failed, or the root cause recorded on one that
# was itself skipped. A job that failed without a worker (no source file, e.g. a
# stdlib an old manifest does not list) may still load through the stdlib
# fallback, so its dependents are left to try.
function failed_dependency(s::PrecompileSession, deps::Vector{PkgId}, config::Config)
    for dep in deps
        job = @lock s.print_lock get(s.jobs, (dep, config), nothing)
        job === nothing && continue
        is_failed(job) && had_pid(job) && return full_name(s.ext_to_parent, dep)
        is_dep_failed(job) && return job.error_msg
    end
    return nothing
end

```
-/
def failed_dependency [MonadFinally m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T) (s : T.Sess) (deps : List PkgId) (config : Config T) : m (Option Bytes) := do
  for dep in deps do
    let job ← o.withLock (← o.sget s).print_lock (do return o.D.get (← o.sget s).jobs (dep, config))
    let some job := job | continue
    if is_failed job && had_pid job then return some (← full_name o.D (← o.sget s).ext_to_parent dep)
    if is_dep_failed job then return some job.error_msg
  return none

/--
Julia source: base/precompilation.jl:2675-2677 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Loading asks only after rejecting a cache, so its requests always read the files.
unverified_set(s::PrecompileSession, from_loading::Bool) = from_loading ? nothing : s.unverified

```
-/
def unverified_set [MonadFinally m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T) (s : T.Sess) (from_loading : Bool) : m (Option (T.Dict Bytes Unit)) := do
  if from_loading then return none else return some (← o.sget s).unverified

/--
Julia source: base/precompilation.jl:2678-2926 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function spawn_precompile_tasks!(s::PrecompileSession;
        direct_deps, was_processed, configs, circular_deps,
        requested_pkgids, pkg_names, requested_pkgs, from_loading)
    batch_tasks = Task[]
    sourcespecs = Dict{PkgId,Union{Nothing,Base.PkgLoadSpec}}(pkg => Base.locate_package_load_spec(pkg) for pkg in keys(direct_deps))
    priorities = SchedulePriorities(direct_deps, sourcespecs)
    for (pkg, deps) in direct_deps
        cachepaths = Base.find_all_in_cache_path(pkg)
        freshpaths = String[]
        @lock s.cache_lock s.cachepath_cache[pkg] = freshpaths
        sourcespec = sourcespecs[pkg]
        single_requested_pkg = length(requested_pkgs) == 1 &&
            (pkg in requested_pkgids || pkg.name in pkg_names)
        for config in configs
            pkg_config = (pkg, config)
            # look up under print_lock (the drainer may insert into s.jobs concurrently)
            job = @lock s.print_lock s.jobs[pkg_config]
            if sourcespec === nothing
                mark_failed!(job, "Error: Missing source file for $(pkg)")
                mark_completed_pkgid!(pkg)
                @lock s.print_lock (s.n_done += 1)
                notify(was_processed[pkg_config])
                continue
            end
            if from_loading && single_requested_pkg && occursin(r"\b__precompile__\(\s*false\s*\)", read(sourcespec.path, String))
                @lock s.print_lock begin
                    Base.@logmsg s.logcalls "Disabled precompiling $(repr(MIME"text/plain"(), pkg)) since the text `__precompile__(false)` was found in file."
                end
                mark_completed_pkgid!(pkg)
                @lock s.print_lock (s.n_done += 1)
                notify(was_processed[pkg_config])
                continue
            end
            @lock BG @lock BG.pkg_done begin
                BG.pending_pkgids[pkg] = get(BG.pending_pkgids, pkg, 0) + 1
                notify(BG.pkg_done)
            end
            flags, cacheflags = config
            task = Threads.@spawn :samepool try
                loaded = s.warn_loaded && (pkg in s.start_loaded_modules)
                for dep in deps
                    wait(was_processed[(dep,config)])
                    if should_stop(s)
                        return
                    end
                end
                circular = pkg in circular_deps
                forced = s.force && !circular && (s.force_stdlibs || !is_stdlib_source(sourcespec))
                freshpath = @lock s.cache_lock Base.compilecache_freshest_path(pkg; ignore_loaded=s.ignore_loaded,
                    stale_cache=s.stale_cache, cachepath_cache=s.cachepath_cache, cachepaths, sourcespec, flags=cacheflags, unverified=unverified_set(s, from_loading))
                is_stale = forced || freshpath === nothing
                # Loading keeps using the version that is already loaded, so a build of the
                # environment's version could not be used in this session.
                skip_loaded = is_stale && !forced && from_loading && !s.ignore_loaded && pkg in s.start_loaded_modules
                if is_stale && !forced && !circular && !skip_loaded && Base.CACHE_FETCH_HOOK[] !== nothing
                    # a cache-fetch hook gets one chance to materialize a
                    # cachefile before we schedule a local compile; this runs
                    # after the dep waits above, so dependency cachefiles are
                    # in place for the hook to key against
                    if Base.maybe_fetch_cache(pkg, sourcespec.path)
                        local fetched_cachepaths = Base.find_all_in_cache_path(pkg)
                        freshpath = @lock s.cache_lock Base.compilecache_freshest_path(pkg; ignore_loaded=s.ignore_loaded,
                            stale_cache=s.stale_cache, cachepath_cache=s.cachepath_cache,
                            cachepaths=fetched_cachepaths, sourcespec, flags=cacheflags, unverified=unverified_set(s, from_loading))
                        is_stale = freshpath === nothing
                    end
                end
                if !is_stale
                    @lock s.cache_lock push!(freshpaths, freshpath)
                end
                if !circular && is_stale && !skip_loaded
                    is_serial_dep = pkg in s.serial_deps
                    is_project_dep = pkg in s.project_deps
                    # an extension always loads its parent and triggers, so it can never
                    # be attempted when one of them failed; that is not worth reporting
                    is_ext = haskey(s.ext_to_parent, pkg)
                    root = (s.skip_dependents || is_ext) ? failed_dependency(s, deps, config) : nothing
                    if root !== nothing
                        # loading `root` would fail again, so do not spend a worker on it
                        @lock s.print_lock mark_dep_failed!(job, root)
                        # only project deps get a line; a failure low in the graph would otherwise
                        # list most of the environment, and the count in the summary covers the rest
                        (is_ext || !is_project_dep) && return
                        name = describe_pkg(s, pkg, is_project_dep, is_serial_dep, flags, cacheflags)
                        @lock s.print_lock begin
                            !s.fancyprint && isempty(s.pkg_queue) && BG.monitoring && print_header(s)
                            push!(s.pkg_queue, pkg_config)
                            !s.fancyprint && BG.monitoring && println(s.logio, " "^12,
                                color_string("  ✗ ", Base.error_color(), s.hascolor), name,
                                color_string(" (skipped, $root failed to precompile)", :light_black, s.hascolor))
                        end
                        return
                    end
                    Base.acquire(s.parallel_limiter; priority=schedule_priority(priorities, pkg), cancel=() -> should_stop(s))

                    std_pipe = Base.link_pipe!(Pipe(); reader_supports_async=true, writer_supports_async=true)
                    t_monitor = Threads.@spawn :samepool precompilepkgs_monitor_std(s, pkg_config, job, std_pipe,
                        single_requested_pkg)

                    name = describe_pkg(s, pkg, is_project_dep, is_serial_dep, flags, cacheflags)
                    try
                        @lock s.print_lock begin
                            !s.fancyprint && isempty(s.pkg_queue) && BG.monitoring && print_header(s)
                            push!(s.pkg_queue, pkg_config)
                        end
                        mark_started!(job)
                        s.fancyprint && notify(s.first_started)
                        if should_stop(s)
                            return
                        end
                        loadable_exts = haskey(s.ext_to_parent, pkg) ? filter((dep)->haskey(s.ext_to_parent, dep), s.triggers[pkg]) : nothing

                        flags_ = if !isempty(deps)
                            `$flags --compiled-modules=strict`
                        else
                            flags
                        end

                        pid_ch = Channel{Int32}(1)
                        if from_loading && pkg in requested_pkgids
                            Base.errormonitor(Threads.@spawn :samepool begin
                                pid = try; take!(pid_ch); catch; Int32(0); end
                                pid > 0 && @lock s.print_lock set_pid!(job, pid)
                            end)
                            t = @elapsed ret = begin
                                Base.compilecache(pkg, sourcespec, std_pipe, std_pipe, !s.ignore_loaded;
                                                  flags=flags_, cacheflags, loadable_exts, signal_channel=make_signal_channel(),
                                                  pid_channel=pid_ch, report_timing=true,
                                                  preresolved=preresolved_snapshot(s))
                            end
                        else
                            fullname = full_name(s.ext_to_parent, pkg)
                            Base.errormonitor(Threads.@spawn :samepool begin
                                pid = try; take!(pid_ch); catch; Int32(0); end
                                pid > 0 && @lock s.print_lock set_pid!(job, pid)
                            end)
                            t = @elapsed ret = precompile_pkgs_maybe_cachefile_lock(s, pkg_config, job, fullname) do
                                if should_stop(s)
                                    return ErrorException("canceled")
                                end
                                local cachepaths = Base.find_all_in_cache_path(pkg)
                                local freshpath = @lock s.cache_lock Base.compilecache_freshest_path(pkg; ignore_loaded=s.ignore_loaded,
                                    stale_cache=s.stale_cache, cachepath_cache=s.cachepath_cache, cachepaths, sourcespec, flags=cacheflags, unverified=unverified_set(s, from_loading))
                                local is_stale = forced || freshpath === nothing
                                if !is_stale
                                    @lock s.cache_lock push!(freshpaths, freshpath)
                                    return nothing
                                end
                                s.logcalls === CoreLogging.Debug && @lock s.print_lock begin
                                    @debug "Precompiling $(repr(MIME"text/plain"(), pkg))"
                                end
                                Base.compilecache(pkg, sourcespec, std_pipe, std_pipe, !s.ignore_loaded;
                                                  flags=flags_, cacheflags, loadable_exts, signal_channel=make_signal_channel(),
                                                  pid_channel=pid_ch, report_timing=true,
                                                  preresolved=preresolved_snapshot(s))
                            end
                        end
                        if ret isa Exception
                            mark_soft_error!(job)
                            !s.fancyprint && !s.brief && BG.monitoring && @lock s.print_lock begin
                                println(s.logio, timing_string(t), color_string("  ? ", Base.warn_color(), s.hascolor), name)
                            end
                        else
                            cache_bytes = 0
                            if ret !== nothing
                                cf_jl, cf_so = ret::Tuple{String, Union{Nothing, String}}
                                cache_bytes = _precompile_cache_bytes(cf_jl, cf_so)
                            end
                            !s.fancyprint && !s.brief && BG.monitoring && @lock s.print_lock begin
                                verbose_prefix = BG.verbose ? format_verbose_timing(job.verbose_timing, t, cache_bytes, job.peak_rss_bytes, s.hascolor) : ""
                                println(s.logio, timing_string(t), verbose_prefix, color_string("  ✓ ", loaded ? Base.warn_color() : :green, s.hascolor), name)
                            end
                            if ret !== nothing
                                mark_recompiled!(job)
                                cachefile, _ = ret::Tuple{String, Union{Nothing, String}}
                                build_id, _ = Base.parse_cache_buildid(cachefile)
                                stale_cache_key = (pkg, build_id, sourcespec, cachefile, s.ignore_loaded, cacheflags)::StaleCacheKey
                                @lock s.cache_lock begin
                                    push!(freshpaths, cachefile)
                                    s.stale_cache[stale_cache_key] = false
                                end
                                if loaded && Base.module_build_id(Base.loaded_modules[pkg]) != build_id
                                    @lock s.print_lock begin
                                        s.n_loaded += 1
                                        push!(s.loaded_pkgs, pkg)
                                    end
                                end
                            elseif loaded
                                # another process compiled this package; conservatively warn
                                @lock s.print_lock begin
                                    s.n_loaded += 1
                                    push!(s.loaded_pkgs, pkg)
                                end
                            end
                        end
                    catch err
                        close(std_pipe.in)
                        wait(t_monitor)
                        err isa InterruptException && rethrow()
                        # If cancel was requested, this failure is almost certainly the
                        # subprocess being SIGKILL'd by the cancel; don't report it as
                        # a precompile failure.
                        if !(@lock BG BG.cancel_requested)
                            mark_failed!(job, sprint(showerror, err))
                            !s.fancyprint && BG.monitoring && @lock s.print_lock begin
                                println(s.logio, " "^12, color_string("  ✗ ", Base.error_color(), s.hascolor), name)
                            end
                        end
                    finally
                        isopen(std_pipe.in) && close(std_pipe.in)
                        wait(t_monitor)
                        try; close(pid_ch); catch; end
                        @lock s.print_lock clear_pid!(job)
                        Base.release(s.parallel_limiter)
                    end
                else
                    if !is_stale
                        @lock s.print_lock begin
                            s.n_already_precomp += 1
                            if loaded
                                fresh_build_id, _ = Base.parse_cache_buildid(freshpath)
                                if Base.module_build_id(Base.loaded_modules[pkg]) != fresh_build_id
                                    s.n_loaded += 1
                                    push!(s.loaded_pkgs, pkg)
                                end
                            end
                        end
                    end
                end
            finally
                @lock BG @lock BG.pkg_done begin
                    n = get(BG.pending_pkgids, pkg, 0) - 1
                    if n <= 0
                        delete!(BG.pending_pkgids, pkg)
                        push!(BG.completed_pkgids, pkg)
                    else
                        BG.pending_pkgids[pkg] = n
                    end
                    notify(BG.pkg_done)
                end
                @lock s.print_lock (s.n_done += 1)
                notify(was_processed[pkg_config])
            end
            push!(batch_tasks, task)
        end
    end
    return batch_tasks
end

```
-/
/- `@lock s.cache_lock Base.compilecache_freshest_path(pkg; ignore_loaded=s.ignore_loaded,
stale_cache=s.stale_cache, cachepath_cache=s.cachepath_cache, cachepaths, sourcespec, flags=cacheflags,
unverified=unverified_set(s, from_loading))`: the call updates `s.stale_cache` and the set it is given
in place. -/
def session_freshest_path [MonadFinally m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T) (s : T.Sess) (pkg : PkgId) (cachepaths : List Bytes) (sourcespec : T.Spec)
    (cacheflags : T.CF) (from_loading : Bool) : m (Option Bytes) := do
  o.withLock (← o.sget s).cache_lock do
    let st ← o.sget s
    let unverified ← unverified_set o s from_loading
    let args : FreshestArgs T :=
      { ignore_loaded := st.ignore_loaded, stale_cache := st.stale_cache, cachepath_cache := st.cachepath_cache,
        cachepaths := some cachepaths, sourcespec := some (some sourcespec), flags := some cacheflags,
        unverified := unverified }
    let r ← o.compilecache_freshest_path pkg args
    o.smodify s fun st => { st with stale_cache := r.stale_cache, unverified := r.unverified.getD st.unverified }
    match r.result with
    | .ok p => return p
    | .error e => throwThe PError e

/-- What one worker task closes over. -/
structure TaskCtx (T : Rt) where
  pkg : PkgId
  deps : List PkgId
  config : Config T
  sourcespec : T.Spec
  cachepaths : List Bytes
  circular_deps : List PkgId
  requested_pkgids : List PkgId
  single_requested_pkg : Bool
  from_loading : Bool
  priorities : T.Prio
  was_processed : T.Dict (PkgConfig T) T.Ev

/-- The precompilation in a worker slot (the `Base.acquire(s.parallel_limiter; ...)` through its
`try`/`catch`/`finally`). -/
def run_worker [MonadFinally m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T) (s : T.Sess) (c : TaskCtx T) (loaded forced is_project_dep is_serial_dep : Bool) :
    m Unit := do
  let pkg := c.pkg
  let pc : PkgConfig T := (pkg, c.config)
  let (flags, cacheflags) := c.config
  acquire o.jobserver o.limiter o.baseline (← o.sget s).parallel_limiter (← schedule_priority o c.priorities pkg)
    (should_stop o s)
  let std_pipe ← o.link_pipe
  let t_monitor ← o.spawn (precompilepkgs_monitor_std o s pc std_pipe c.single_requested_pkg)
  let name ← describe_pkg o s pkg is_project_dep is_serial_dep flags cacheflags
  -- the `try` block up to `pid_ch = Channel{Int32}(1)`; `none` is its `return`
  let stage1 : m (Option (Option (List PkgId) × T.Cmd)) := do
    o.withLock (← o.sget s).print_lock do
      if !(← o.sget s).fancyprint && (← o.sget s).pkg_queue.isEmpty then
        if (← o.bgget).monitoring then print_header o s
      o.smodify s fun st => { st with pkg_queue := st.pkg_queue ++ [pc] }
    let t ← o.time
    modifyJob o s pc (mark_started · t)
    if (← o.sget s).fancyprint then o.notifyEv (← o.sget s).first_started
    if ← should_stop o s then return none
    let st ← o.sget s
    let loadable_exts ← if haskey o.D st.ext_to_parent pkg then do
        let tr ← getindex o.D st.triggers pkg
        pure (some (tr.filter (haskey o.D st.ext_to_parent ·)))
      else pure none
    let flags_ := if !c.deps.isEmpty then o.cmdOfArgs (o.cmdArgs flags ++ [lit "--compiled-modules=strict"]) else flags
    return some (loadable_exts, flags_)
  -- the rest of the `try` block, given `pid_ch`
  let stage2 (loadable_exts : Option (List PkgId)) (flags_ : T.Cmd) (pid_ch : T.PidChan) : m Unit := do
    let pid_watcher : m Unit := do
      let pid ← tryCatchThe PError (o.pidTake pid_ch) fun _ => pure (JInt.wrap .i32 0)
      if pid.val > 0 then o.withLock (← o.sget s).print_lock (modifyJob o s pc (set_pid · pid))
    let compile : m CompileResult := do
      let keep := !(← o.sget s).ignore_loaded
      let sc ← make_signal_channel o
      let pre ← preresolved_snapshot o s
      o.compilecache pkg c.sourcespec std_pipe std_pipe keep ⟨flags_, cacheflags, loadable_exts, sc, pid_ch, true, pre⟩
    let (t, ret) ← if c.from_loading && c.requested_pkgids.contains pkg then do
        o.errormonitor (← o.spawn pid_watcher)
        elapsed o compile
      else do
        let fullname ← full_name o.D (← o.sget s).ext_to_parent pkg
        o.errormonitor (← o.spawn pid_watcher)
        elapsed o (precompile_pkgs_maybe_cachefile_lock o (do
            if ← should_stop o s then return .exc (.errorException (lit "canceled"))
            let cachepaths ← o.find_all_in_cache_path pkg
            let freshpath ← session_freshest_path o s pkg cachepaths c.sourcespec cacheflags c.from_loading
            if !forced then
              if let some p := freshpath then
                o.withLock (← o.sget s).cache_lock (push_freshpath o s pkg p)
                return .nothing
            let st ← o.sget s
            if st.logcalls == some o.logDebug then
              o.withLock st.print_lock (o.debugPrecompiling pkg)
            compile) s pc fullname)
    match ret with
    | .exc _ =>
      modifyJob o s pc mark_soft_error
      let st ← o.sget s
      if !st.fancyprint && !st.brief then
        if (← o.bgget).monitoring then
          o.withLock st.print_lock do
            println o (o.ctx (← o.sget s).logio) ((← timing_string o.timingFormat t) ++
              (← color_string (lit "  ? ") (← o.warn_color) (← o.sget s).hascolor) ++ name)
    | r =>
      let cache_bytes ← match r with
        | .paths cf_jl cf_so => _precompile_cache_bytes o.env.isfile o.filesize cf_jl cf_so
        | _ => pure (ji 0)
      let st ← o.sget s
      if !st.fancyprint && !st.brief then
        if (← o.bgget).monitoring then
          o.withLock st.print_lock do
            let job ← getJob o s pc
            let verbose_prefix ← if (← o.bgget).verbose then
                format_verbose_timing o.timingFormat o.splitWS o.parseUInt64 o.parseInt o.roundInt o.maxF
                  job.verbose_timing t cache_bytes job.peak_rss_bytes (← o.sget s).hascolor
              else pure []
            let c ← if loaded then o.warn_color else pure (.symbol "green")
            println o (o.ctx (← o.sget s).logio) ((← timing_string o.timingFormat t) ++ verbose_prefix ++
              (← color_string (lit "  ✓ ") c (← o.sget s).hascolor) ++ name)
      match r with
      | .paths cachefile _ =>
        modifyJob o s pc mark_recompiled
        let build_id ← o.parse_cache_buildid cachefile
        let stale_cache_key := o.mkStaleCacheKey pkg build_id c.sourcespec cachefile (← o.sget s).ignore_loaded cacheflags
        o.withLock (← o.sget s).cache_lock do
          push_freshpath o s pkg cachefile
          o.smodify s fun st => { st with stale_cache := o.D.set st.stale_cache stale_cache_key false }
        if loaded then
          if (← o.module_build_id (← loadedModuleIndex o pkg)) != build_id then
            o.withLock (← o.sget s).print_lock (note_loaded o s pkg)
      | _ =>
        if loaded then
          -- another process compiled this package; conservatively warn
          o.withLock (← o.sget s).print_lock (note_loaded o s pkg)
  -- `catch err`
  let handler (err : PError) : m Unit := do
    o.closePipeIn std_pipe
    o.waitTask t_monitor
    if err == .interruptException then throwThe PError err
    -- If cancel was requested, this failure is almost certainly the
    -- subprocess being SIGKILL'd by the cancel; don't report it as
    -- a precompile failure.
    if !(← lock_BG o do return (← o.bgget).cancel_requested) then
      let msg ← o.showerror err
      modifyJob o s pc (mark_failed · msg)
      let st ← o.sget s
      if !st.fancyprint then
        if (← o.bgget).monitoring then
          o.withLock st.print_lock do
            println o (o.ctx st.logio) (spaces12 ++ (← color_string (lit "  ✗ ") (← o.error_color) st.hascolor) ++ name)
  -- `finally`; `pid_ch` is unassigned (`none`) when the `try` block ended before creating it, and
  -- the `UndefVarError` of `close(pid_ch)` is caught
  let fin (pid_ch : Option T.PidChan) : m Unit := do
    if ← o.pipeInIsopen std_pipe then o.closePipeIn std_pipe
    o.waitTask t_monitor
    match pid_ch with
    | some ch => tryCatchThe PError (o.pidClose ch) fun _ => pure ()
    | none => pure ()
    o.withLock (← o.sget s).print_lock (modifyJob o s pc clear_pid)
    release o.jobserver o.limiter (← o.sget s).parallel_limiter
  let r1 ← catchE stage1
  let (outcome, pid_ch) ← match r1 with
    | .error e => pure ((Except.error e : Except PError Unit), (none : Option T.PidChan))
    | .ok none => pure (.ok (), none)
    | .ok (some (lx, flags_)) => do
      let r2 ← catchE (o.newPidChannel (ji 1))
      match r2 with
      | .error e => pure (.error e, none)
      | .ok ch => do
        let r3 ← catchE (stage2 lx flags_ ch)
        pure (r3, some ch)
  let after ← match outcome with
    | .ok () => pure (Except.ok ())
    | .error err => catchE (handler err)
  fin pid_ch
  match after with
  | .error e => throwThe PError e
  | .ok () => pure ()

/-- The `try` block of a worker task. -/
def precompile_task_body [MonadFinally m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T) (s : T.Sess) (c : TaskCtx T) : m Unit := do
  let pkg := c.pkg
  let config := c.config
  let (flags, cacheflags) := config
  let pc : PkgConfig T := (pkg, config)
  let st ← o.sget s
  let loaded := st.warn_loaded && setIn o.D st.start_loaded_modules pkg
  for dep in c.deps do
    o.waitEv (← getindex o.D c.was_processed (dep, config))
    if ← should_stop o s then return
  let circular := c.circular_deps.contains pkg
  let st ← o.sget s
  let forced := st.force && !circular && (st.force_stdlibs || !is_stdlib_source o c.sourcespec)
  let mut freshpath ← session_freshest_path o s pkg c.cachepaths c.sourcespec cacheflags c.from_loading
  let mut is_stale := forced || freshpath.isNone
  -- Loading keeps using the version that is already loaded, so a build of the
  -- environment's version could not be used in this session.
  let st ← o.sget s
  let skip_loaded := is_stale && !forced && c.from_loading && !st.ignore_loaded && setIn o.D st.start_loaded_modules pkg
  if is_stale && !forced && !circular && !skip_loaded then
    if ← o.cacheFetchHookSet then
      -- a cache-fetch hook gets one chance to materialize a
      -- cachefile before we schedule a local compile; this runs
      -- after the dep waits above, so dependency cachefiles are
      -- in place for the hook to key against
      if ← o.maybe_fetch_cache pkg (o.specPath c.sourcespec) then
        let fetched_cachepaths ← o.find_all_in_cache_path pkg
        freshpath ← session_freshest_path o s pkg fetched_cachepaths c.sourcespec cacheflags c.from_loading
        is_stale := freshpath.isNone
  if !is_stale then
    if let some p := freshpath then
      o.withLock (← o.sget s).cache_lock (push_freshpath o s pkg p)
  if !circular && is_stale && !skip_loaded then
    let st ← o.sget s
    let is_serial_dep := st.serial_deps.contains pkg
    let is_project_dep := st.project_deps.contains pkg
    -- an extension always loads its parent and triggers, so it can never
    -- be attempted when one of them failed; that is not worth reporting
    let is_ext := haskey o.D st.ext_to_parent pkg
    let root ← if st.skip_dependents || is_ext then failed_dependency o s c.deps config else pure none
    if let some root := root then
      -- loading `root` would fail again, so do not spend a worker on it
      o.withLock (← o.sget s).print_lock (modifyJob o s pc (mark_dep_failed · root))
      -- only project deps get a line; a failure low in the graph would otherwise
      -- list most of the environment, and the count in the summary covers the rest
      if is_ext || !is_project_dep then return
      let name ← describe_pkg o s pkg is_project_dep is_serial_dep flags cacheflags
      o.withLock (← o.sget s).print_lock do
        if !(← o.sget s).fancyprint && (← o.sget s).pkg_queue.isEmpty then
          if (← o.bgget).monitoring then print_header o s
        o.smodify s fun st => { st with pkg_queue := st.pkg_queue ++ [pc] }
        if !(← o.sget s).fancyprint then
          if (← o.bgget).monitoring then
            let st ← o.sget s
            println o (o.ctx st.logio) (spaces12 ++ (← color_string (lit "  ✗ ") (← o.error_color) st.hascolor) ++ name ++
              (← color_string (lit " (skipped, " ++ root ++ lit " failed to precompile)") (.symbol "light_black") st.hascolor))
      return
    run_worker o s c loaded forced is_project_dep is_serial_dep
  else
    if !is_stale then
      if let some fp := freshpath then
        o.withLock (← o.sget s).print_lock do
          o.smodify s fun st => { st with n_already_precomp := st.n_already_precomp + ji 1 }
          if loaded then
            let fresh_build_id ← o.parse_cache_buildid fp
            if (← o.module_build_id (← loadedModuleIndex o pkg)) != fresh_build_id then
              note_loaded o s pkg

/-- The `finally` block of a worker task. -/
def precompile_task_finally [MonadFinally m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T) (s : T.Sess) (c : TaskCtx T) : m Unit := do
  lock_BG o do
    o.condLock (← o.bgget).pkg_done do
      let n := getD o.D (← o.bgget).pending_pkgids c.pkg (ji 0) - ji 1
      if n.val ≤ 0 then
        o.bgmodify fun bg => { bg with pending_pkgids := o.D.delete bg.pending_pkgids c.pkg }
        o.bgmodify fun bg => { bg with completed_pkgids := setPush o.D bg.completed_pkgids c.pkg }
      else
        o.bgmodify fun bg => { bg with pending_pkgids := o.D.set bg.pending_pkgids c.pkg n }
      o.condNotify (← o.bgget).pkg_done
  o.withLock (← o.sget s).print_lock (o.smodify s fun st => { st with n_done := st.n_done + ji 1 })
  o.notifyEv (← getindex o.D c.was_processed (c.pkg, c.config))

/-- `n_done += 1` and the notification for a package/config skipped without a task. -/
def skip_job [MonadFinally m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T) (s : T.Sess) (pkg : PkgId) (ev : T.Ev) : m Unit := do
  mark_completed_pkgid o pkg
  o.withLock (← o.sget s).print_lock (o.smodify s fun st => { st with n_done := st.n_done + ji 1 })
  o.notifyEv ev

/-- One `(pkg, config)` of `spawn_precompile_tasks!` with a located source: the spawned task, or
`none` for `continue`. -/
def spawn_one [MonadFinally m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T) (s : T.Sess) (c : TaskCtx T) : m (Option T.Tsk) := do
  let pc : PkgConfig T := (c.pkg, c.config)
  if c.from_loading && c.single_requested_pkg then
    if o.hasPrecompileFalse (← o.readString (o.specPath c.sourcespec)) then
      o.withLock (← o.sget s).print_lock do
        o.logmsg (← o.sget s).logcalls (lit "Disabled precompiling " ++ o.reprPkg c.pkg ++
          lit " since the text `__precompile__(false)` was found in file.")
      skip_job o s c.pkg (← getindex o.D c.was_processed pc)
      return none
  lock_BG o do
    o.condLock (← o.bgget).pkg_done do
      o.bgmodify fun bg =>
        { bg with pending_pkgids := o.D.set bg.pending_pkgids c.pkg (getD o.D bg.pending_pkgids c.pkg (ji 0) + ji 1) }
      o.condNotify (← o.bgget).pkg_done
  some <$> o.spawn (tryFinally (precompile_task_body o s c) (precompile_task_finally o s c))

/-- `spawn_precompile_tasks!(s; direct_deps, was_processed, configs, circular_deps, requested_pkgids,
pkg_names, requested_pkgs, from_loading)`. -/
def spawn_precompile_tasks [MonadFinally m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T) (s : T.Sess) (direct_deps : T.Dict PkgId (List PkgId))
    (was_processed : T.Dict (PkgConfig T) T.Ev) (configs : List (Config T)) (circular_deps requested_pkgids : List PkgId)
    (pkg_names : List Bytes) (requested_pkgs : Pkgs) (from_loading : Bool) : m (List T.Tsk) := do
  let mut batch_tasks : List T.Tsk := []
  let mut sourcespecs : T.Dict PkgId (Option T.Spec) := o.D.empty
  for pkg in o.D.keys direct_deps do
    sourcespecs := o.D.set sourcespecs pkg (← o.locate_package_load_spec pkg)
  let priorities ← SchedulePriorities_new o direct_deps sourcespecs
  for pkg in o.D.keys direct_deps do
    let deps ← getindex o.D direct_deps pkg
    let cachepaths ← o.find_all_in_cache_path pkg
    -- `freshpaths = String[]`, stored as `s.cachepath_cache[pkg]`
    o.withLock (← o.sget s).cache_lock (o.smodify s fun st => { st with cachepath_cache := o.D.set st.cachepath_cache pkg [] })
    let sourcespec ← getindex o.D sourcespecs pkg
    let single_requested_pkg := requested_pkgs.length == 1 &&
      (requested_pkgids.contains pkg || pkg_names.contains pkg.name)
    for config in configs do
      let pc : PkgConfig T := (pkg, config)
      -- look up under print_lock (the drainer may insert into s.jobs concurrently)
      discard <| o.withLock (← o.sget s).print_lock (getJob o s pc)
      match sourcespec with
      | none =>
        modifyJob o s pc (mark_failed · (lit "Error: Missing source file for " ++ o.stringPkg pkg))
        skip_job o s pkg (← getindex o.D was_processed pc)
      | some spec =>
        let c : TaskCtx T := ⟨pkg, deps, config, spec, cachepaths, circular_deps, requested_pkgids,
          single_requested_pkg, from_loading, priorities, was_processed⟩
        if let some task ← spawn_one o s c then
          batch_tasks := batch_tasks ++ [task]
  return batch_tasks

end tasks

section results
variable {m : Type → Type} [Monad m] [MonadExceptOf PError m] {T : Rt}
open JuliaLean.base.float (sub_float add_float mul_float div_float lt_float le_float uitofp sitofp)

/-- `get(io, :color, false)::Bool`. -/
def ioHascolor (o : Ops m T) (io : T.IOC) : m Bool := do
  match ← o.getColor io with
  | some b => return b
  | none => throwP .typeError

/-- `detect_circular_deps!(direct_deps, serial_deps, was_processed, io, ext_to_parent)` over the
session's runtime: the events are `was_processed`'s and the warning goes to `io`. -/
def detect_circular_deps_io [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T)
    (direct_deps : T.Dict PkgId (List PkgId)) (serial_deps : List PkgId) (was_processed : T.Dict (PkgConfig T) T.Ev)
    (io : T.IOC) (ext_to_parent : T.Dict PkgId PkgId) : m (List PkgId) :=
  detect_circular_deps o.D direct_deps serial_deps
    (fun pkg => do
      for pc in o.D.keys was_processed do
        if pc.1 == pkg then o.notifyEv (← getindex o.D was_processed pc))
    (ioHascolor o io)
    (fun msg => do pps o (o.ctx io) "Warning" msg (← o.warn_color))
    ext_to_parent

/-- Writes the `peak_rss_bytes` of `jobs` (as returned by `sample_peak_rss!`/`poll_process_stats!`)
into the session's job objects. -/
def write_peaks (o : Ops m T) (s : T.Sess) (jobs : T.Dict (PkgConfig T) (PrecompileJob T.Buf)) : m Unit := do
  for k in o.D.keys jobs do
    let j ← getindex o.D jobs k
    modifyJob o s k fun x => { x with peak_rss_bytes := j.peak_rss_bytes }

/-- `split(s, "\n")`. -/
def splitNL (s : Bytes) : List Bytes :=
  (s.splitOn 10)

/-- `collect(String, Iterators.flatten((v for (pkgid, v) in s.cachepath_cache if pkgid in pkgids)))`. -/
def collect_paths (o : Ops m T) (cc : T.Dict PkgId (List Bytes)) (pkgids : List PkgId) : m (List Bytes) := do
  let mut out : List Bytes := []
  for k in o.D.keys cc do
    if pkgids.contains k then out := out ++ (← getindex o.D cc k)
  return out

/--
Julia source: base/precompilation.jl:2927-3049 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function drain_work_channel!(s::PrecompileSession, work_channel::Channel{PrecompileRequest})
    drainer = Threads.@spawn :samepool begin
        while true
            isopen(work_channel) || break
            should_stop(s) && break
            request = try; take!(work_channel); catch; break; end
            waiter_spawned = false
            try
                new_env = ExplicitEnv()
                req_pkgids = PkgId[]
                if request.pkgs isa Vector{PkgId}
                    append!(req_pkgids, request.pkgs)
                else
                    for name in request.pkgs
                        pkgid = Base.identify_package(name)
                        pkgid !== nothing && push!(req_pkgids, pkgid)
                    end
                end
                new_graph = build_dep_graph(new_env, request.manifest, request._from_loading, req_pkgids)
                # When no specific packages were requested, treat project deps as the requested set
                effective_pkgids = isempty(req_pkgids) ? new_graph.project_deps : req_pkgids
                @lock s.print_lock begin
                    merge!(s.direct_deps, new_graph.direct_deps)
                    merge!(s.ext_to_parent, new_graph.ext_to_parent)
                    merge!(s.parent_to_exts, new_graph.parent_to_exts)
                    merge!(s.triggers, new_graph.triggers)
                    union!(s.project_deps, new_graph.project_deps)
                    union!(s.serial_deps, new_graph.serial_deps)
                    union!(s.requested_pkgids, effective_pkgids)
                    mergewith!(+, s.reasons, request.reasons)
                    # a header already printed explained only the earlier requests
                    if request._from_loading && s.header_printed && BG.monitoring
                        # the cursor is at the top of the progress display, which is redrawn below
                        s.fancyprint && print(s.logio, ansi_cleartoend)
                        explain_reasons!(s, request.reasons)
                    end
                end
                new_pkg_names = String[pkg isa PkgId ? pkg.name : pkg for pkg in request.pkgs]
                new_dd = new_graph.direct_deps
                filter_dep_graph!(new_dd, new_pkg_names, new_graph.ext_to_parent, req_pkgids)
                skip_pkgs = Set{PkgId}()
                @lock BG begin
                    for pkgid in keys(new_dd)
                        if haskey(BG.pending_pkgids, pkgid)
                            push!(skip_pkgs, pkgid)
                        end
                    end
                end
                # Replace skip_pkgs with leaf nodes so circular dep detection
                # can traverse through them, but no tasks will be spawned.
                for pkgid in skip_pkgs
                    new_dd[pkgid] = PkgId[]
                end
                new_wp = Dict{PkgConfig, Base.Event}()
                for config in request.configs
                    for pkgid in keys(new_dd)
                        pkg_config = (pkgid, config)
                        if pkgid in skip_pkgs
                            # Wire existing event so new tasks wait for the already-compiling dep
                            if haskey(s.was_processed, pkg_config)
                                new_wp[pkg_config] = s.was_processed[pkg_config]
                            else
                                evt = Base.Event()
                                notify(evt)
                                new_wp[pkg_config] = evt
                            end
                        else
                            evt = Base.Event()
                            # workers read s.jobs and should_stop iterates s.was_processed under this lock
                            @lock s.print_lock begin
                                get!(PrecompileJob, s.jobs, pkg_config)
                                s.was_processed[pkg_config] = evt
                            end
                            new_wp[pkg_config] = evt
                        end
                    end
                end
                new_circular = detect_circular_deps!(new_dd, new_graph.serial_deps, new_wp, s.io, s.ext_to_parent)
                for pkgid in skip_pkgs
                    delete!(new_dd, pkgid)
                end
                if isempty(new_dd)
                    try; put!(request.result, String[]); catch; end
                    continue
                end
                @lock s.print_lock begin
                    s.n_total += length(new_dd) * length(request.configs)
                    s.n_batches += 1
                end
                new_tasks = spawn_precompile_tasks!(s;
                    direct_deps=new_dd, was_processed=new_wp, configs=request.configs,
                    circular_deps=new_circular, requested_pkgids=effective_pkgids,
                    pkg_names=new_pkg_names, requested_pkgs=request.pkgs,
                    from_loading=request._from_loading)
                append!(s.injected_tasks, new_tasks)
                waiter = Threads.@spawn :samepool begin
                    try
                        waitall(new_tasks; failfast=false, throw=false)
                        # also wait for skipped packages being compiled by another request
                        foreach(wait, values(new_wp))
                        paths = @lock s.cache_lock collect(String, Iterators.flatten((v for (pkgid, v) in s.cachepath_cache if pkgid in effective_pkgids)))
                        request._from_loading && filter!(p -> checked_now!(s, p), paths)
                        try; put!(request.result, paths); catch; end
                    finally
                        isready(request.result) || try; put!(request.result, String[]); catch; end
                    end
                end
                push!(s.result_waiters, waiter)
                waiter_spawned = true
            catch e
                try; put!(request.result, e); catch; end
            finally
                # Only write the fallback here if no waiter was spawned — the waiter
                # has its own finally that guarantees a result is written after tasks finish.
                if !waiter_spawned && !isready(request.result)
                    try; put!(request.result, String[]); catch; end
                end
            end
        end
    end
    return drainer
end

```
-/
/- The body of the drainer's `try` block for one request: whether the waiter was spawned
(`false` for its `continue`). -/
def drain_request [MonadFinally m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T) (s : T.Sess)
    (request : PrecompileRequest T) : m Bool := do
  let new_env ← ExplicitEnv_0 o.D o.any o.env
  let mut req_pkgids : List PkgId := []
  match request.pkgs with
  | .ids ps => req_pkgids := req_pkgids ++ ps
  | .names ns =>
    for name in ns do
      let pkgid ← o.identify_package name
      if let some p := pkgid then req_pkgids := req_pkgids ++ [p]
  let new_graph ← build_dep_graph o.D o.graph new_env request.manifest request._from_loading req_pkgids
  -- When no specific packages were requested, treat project deps as the requested set
  let effective_pkgids := if req_pkgids.isEmpty then new_graph.project_deps else req_pkgids
  o.withLock (← o.sget s).print_lock do
    o.smodify s fun st => { st with
      direct_deps := (o.D.keys new_graph.direct_deps).foldl (fun d k => match o.D.get new_graph.direct_deps k with
        | some v => o.D.set d k v
        | none => d) st.direct_deps }
    o.smodify s fun st => { st with
      ext_to_parent := (o.D.keys new_graph.ext_to_parent).foldl (fun d k => match o.D.get new_graph.ext_to_parent k with
        | some v => o.D.set d k v
        | none => d) st.ext_to_parent }
    o.smodify s fun st => { st with
      parent_to_exts := (o.D.keys new_graph.parent_to_exts).foldl (fun d k => match o.D.get new_graph.parent_to_exts k with
        | some v => o.D.set d k v
        | none => d) st.parent_to_exts }
    o.smodify s fun st => { st with
      triggers := (o.D.keys new_graph.triggers).foldl (fun d k => match o.D.get new_graph.triggers k with
        | some v => o.D.set d k v
        | none => d) st.triggers }
    o.smodify s fun st => { st with project_deps := vunion st.project_deps new_graph.project_deps }
    o.smodify s fun st => { st with serial_deps := vunion st.serial_deps new_graph.serial_deps }
    o.smodify s fun st => { st with requested_pkgids := vunion st.requested_pkgids effective_pkgids }
    -- `mergewith!(+, s.reasons, request.reasons)`
    o.smodify s fun st => { st with
      reasons := (o.D.keys request.reasons).foldl (fun d k => match o.D.get request.reasons k with
        | some v => o.D.set d k (match o.D.get d k with
          | some u => u + v
          | none => v)
        | none => d) st.reasons }
    -- a header already printed explained only the earlier requests
    if request._from_loading && (← o.sget s).header_printed then
      if (← o.bgget).monitoring then
        -- the cursor is at the top of the progress display, which is redrawn below
        if (← o.sget s).fancyprint then o.print (o.ctx (← o.sget s).logio) ansi_cleartoend
        explain_reasons o s (some request.reasons)
  let new_pkg_names := match request.pkgs with
    | .ids ps => ps.map (·.name)
    | .names ns => ns
  let (new_dd, _) ← filter_dep_graph o.D new_graph.direct_deps new_pkg_names new_graph.ext_to_parent req_pkgids
  let mut new_dd := new_dd
  let mut skip_pkgs : T.Dict PkgId Unit := o.D.empty
  let pending ← lock_BG o do
    let bg ← o.bgget
    return (o.D.keys new_dd).filter (haskey o.D bg.pending_pkgids ·)
  for pkgid in pending do skip_pkgs := setPush o.D skip_pkgs pkgid
  -- Replace skip_pkgs with leaf nodes so circular dep detection
  -- can traverse through them, but no tasks will be spawned.
  for pkgid in o.D.keys skip_pkgs do
    new_dd := o.D.set new_dd pkgid []
  let mut new_wp : T.Dict (PkgConfig T) T.Ev := o.D.empty
  for config in request.configs do
    for pkgid in o.D.keys new_dd do
      let pkg_config : PkgConfig T := (pkgid, config)
      if setIn o.D skip_pkgs pkgid then
        -- Wire existing event so new tasks wait for the already-compiling dep
        let wp := (← o.sget s).was_processed
        match o.D.get wp pkg_config with
        | some evt => new_wp := o.D.set new_wp pkg_config evt
        | none =>
          let evt ← o.newEvent
          o.notifyEv evt
          new_wp := o.D.set new_wp pkg_config evt
      else
        let evt ← o.newEvent
        -- workers read s.jobs and should_stop iterates s.was_processed under this lock
        o.withLock (← o.sget s).print_lock do
          if !haskey o.D (← o.sget s).jobs pkg_config then
            let buf ← o.newBuf
            o.smodify s fun st => { st with jobs := o.D.set st.jobs pkg_config (PrecompileJob.new buf) }
          o.smodify s fun st => { st with was_processed := o.D.set st.was_processed pkg_config evt }
        new_wp := o.D.set new_wp pkg_config evt
  let st ← o.sget s
  let new_circular ← detect_circular_deps_io o new_dd new_graph.serial_deps new_wp st.io st.ext_to_parent
  for pkgid in o.D.keys skip_pkgs do
    new_dd := o.D.delete new_dd pkgid
  if (o.D.keys new_dd).isEmpty then
    tryCatchThe PError (o.resPut request.result (.paths [])) fun _ => pure ()
    return false
  let n_new := (o.D.keys new_dd).length * request.configs.length
  o.withLock (← o.sget s).print_lock do
    o.smodify s fun st => { st with n_total := st.n_total + ji n_new }
    o.smodify s fun st => { st with n_batches := st.n_batches + ji 1 }
  let new_tasks ← spawn_precompile_tasks o s new_dd new_wp request.configs new_circular effective_pkgids new_pkg_names
    request.pkgs request._from_loading
  o.smodify s fun st => { st with injected_tasks := st.injected_tasks ++ new_tasks }
  let wp := new_wp
  let waiter ← o.spawn (tryFinally
    (do
      o.waitall new_tasks
      -- also wait for skipped packages being compiled by another request
      for k in o.D.keys wp do o.waitEv (← getindex o.D wp k)
      let mut paths ← o.withLock (← o.sget s).cache_lock (do collect_paths o (← o.sget s).cachepath_cache effective_pkgids)
      if request._from_loading then paths ← paths.filterM (checked_now o s)
      tryCatchThe PError (o.resPut request.result (.paths paths)) fun _ => pure ())
    (do
      if !(← o.resIsready request.result) then
        tryCatchThe PError (o.resPut request.result (.paths [])) fun _ => pure ()))
  o.smodify s fun st => { st with result_waiters := st.result_waiters ++ [waiter] }
  return true

/-- One iteration of the drainer's `while true` loop: `false` for `break`. -/
def drain_iter [MonadFinally m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T) (s : T.Sess)
    (work_channel : T.ReqChan) : m Bool := do
  if !(← o.reqIsopen work_channel) then return false
  if ← should_stop o s then return false
  let request ← catchE (o.reqTake work_channel)
  match request with
  | .error _ => return false
  | .ok request =>
    let r ← catchE (drain_request o s request)
    let waiter_spawned ← match r with
      | .ok b => pure b
      | .error e => do
        tryCatchThe PError (o.resPut request.result (.exc e)) fun _ => pure ()
        pure false
    -- Only write the fallback here if no waiter was spawned — the waiter
    -- has its own finally that guarantees a result is written after tasks finish.
    if !waiter_spawned then
      if !(← o.resIsready request.result) then
        tryCatchThe PError (o.resPut request.result (.paths [])) fun _ => pure ()
    return true

/-- The drainer's `while true` loop. -/
def drain_loop [MonadFinally m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T) (s : T.Sess)
    (work_channel : T.ReqChan) : m Unit := do
  let again ← drain_iter o s work_channel
  if again then drain_loop o s work_channel else pure ()
partial_fixpoint

/-- `drain_work_channel!(s, work_channel)`. -/
def drain_work_channel [MonadFinally m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T) (s : T.Sess)
    (work_channel : T.ReqChan) : m T.Tsk :=
  o.spawn (drain_loop o s work_channel)

/--
Julia source: base/precompilation.jl:3050-3274 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function report_precompile_results!(s::PrecompileSession)
    if !s._from_loading
        @lock Base.require_lock begin
            Base.LOADING_CACHE[] = nothing
        end
    end
    notify(s.first_started) # in cases of no-op or !fancyprint
    # a cancel that lands while the last job runs is not seen by the job loop
    should_stop(s)

    quick_exit = any(t -> !istaskdone(t) || istaskfailed(t), s.tasks) || s.interrupted || s.canceled
    seconds_elapsed = round(Int, (s.time_start > 0 ? (time_ns() -% s.time_start) : 0) / 1e9)
    ndeps = count(j -> is_recompiled(j), values(s.jobs))

    requested_errs = false
    for ((dep, _), job) in s.jobs
        if (is_failed(job) || is_dep_failed(job)) && dep in s.requested_pkgids
            requested_errs = true
            break
        end
    end
    if !s.strict && !requested_errs && !s.interrupted && !s.canceled
        for (_, job) in s.jobs
            (is_failed(job) || is_dep_failed(job)) && clear_failure!(job)
        end
    end
    if s.canceled && !(@lock BG BG.info_requested)
        # Drop captured stdout/stderr from jobs that didn't fail before cancel,
        # since their output is just truncated cancel-induced noise. If the user
        # asked for info (SIGINFO/SIGUSR1) at any point, keep the output so the
        # profiling info gets surfaced in the cancel report. Soft errors
        # (e.g. `?` packages) are completed jobs whose captured output is the
        # actual precompile error message, so preserve it as well.
        for (_, job) in s.jobs
            (is_failed(job) || is_soft_error(job)) && continue
            job.output.size > 0 && truncate(job.output, 0)
        end
    end
    n_failed = count(j -> is_failed(j), values(s.jobs))
    # skipped extensions are implied by their parent or trigger failing, so only count packages
    n_dep_failed = count(((k, j),) -> is_dep_failed(j) && !haskey(s.ext_to_parent, first(k)), s.jobs)
    if ndeps > 0 || n_failed > 0
        if !quick_exit
            logstr = sprint(context=s.logio) do iostr
                if s.fancyprint
                    what = if s.n_batches > 1
                        "done."
                    elseif isempty(s.requested_pkgids) || s.requested_all
                        "packages finished."
                    else
                        "$(join((full_name(s.ext_to_parent, p) for p in s.requested_pkgids), ", ", " and ")) finished."
                    end
                    printpkgstyle(iostr, :Precompiling, what)
                end
                plural = length(s.configs) > 1 ? "dependency configurations" : ndeps == 1 ? "dependency" : "dependencies"
                print(iostr, "  $(ndeps) $(plural) successfully precompiled in $(seconds_elapsed) seconds")
                if s.n_already_precomp > 0 || !isempty(s.circular_deps) || n_dep_failed > 0
                    s.n_already_precomp > 0 && (print(iostr, ". $(s.n_already_precomp) already precompiled"))
                    !isempty(s.circular_deps) && (print(iostr, ". $(length(s.circular_deps)) skipped due to circular dependency"))
                    n_dep_failed > 0 && (print(iostr, ". $(n_dep_failed) skipped because a dependency failed to precompile"))
                    print(iostr, ".")
                end
                if s.n_loaded > 0
                    loaded_names_vec = sort!([full_name(s.ext_to_parent, p) for p in s.loaded_pkgs])
                    if s._from_loading && !s.ignore_loaded
                        # loading compiles dependents for the loaded version, so the loaded
                        # package is the reason for this session rather than its result;
                        # say so here for those not already explained under the header
                        differing = sort!([full_name(s.ext_to_parent, p) for p in s.loaded_pkgs if loaded_version_differs(p)])
                        unexplained = setdiff(differing, s.explained_conflicts)
                        if !isempty(unexplained)
                            print(iostr, "\n", loaded_conflicts_message(unexplained, s.hascolor; ongoing=false, cancelable=false))
                        end
                    else
                        plural1 = length(s.configs) > 1 ? "dependency configurations" : s.n_loaded == 1 ? "dependency" : "dependencies"
                        plural2 = s.n_loaded == 1 ? "a different version is" : "different versions are"
                        plural3 = s.n_loaded == 1 ? "" : "s"
                        loaded_names = format_names_list(loaded_names_vec)
                        # compute how many precompiled packages transitively depend on the loaded packages
                        loaded_set = Set{PkgId}(s.loaded_pkgs)
                        n_affected = let reverse_deps = Dict{PkgId, Vector{PkgId}}()
                            for (p, deps) in s.direct_deps
                                for d in deps
                                    push!(get!(Vector{PkgId}, reverse_deps, d), p)
                                end
                            end
                            affected = Set{PkgId}()
                            frontier = PkgId[p for p in loaded_set]
                            while !isempty(frontier)
                                p = pop!(frontier)
                                for rdep in get(reverse_deps, p, PkgId[])
                                    if rdep ∉ affected && rdep ∉ loaded_set
                                        push!(affected, rdep)
                                        push!(frontier, rdep)
                                    end
                                end
                            end
                            length(affected)
                        end
                        print(iostr, "\n  ",
                            color_string(string(s.n_loaded), Base.warn_color(), s.hascolor),
                            " $(plural1) precompiled but ",
                            color_string("$(plural2) currently loaded", Base.warn_color(), s.hascolor),
                            " (", loaded_names, ")",
                            ". Restart julia to access the new version$(plural3)."
                        )
                        if n_affected > 0
                            affected_plural = length(s.configs) > 1 ? "dependency configurations" : n_affected == 1 ? "dependent" : "dependents"
                            print(iostr,
                                " Otherwise, $(n_affected) $(affected_plural) of ",
                                s.n_loaded == 1 ? "this package" : "these packages",
                                " may trigger further precompilation to work with the unexpected version$(plural3)."
                            )
                        end
                    end
                end
                n_soft_errors = count(j -> is_soft_error(j), values(s.jobs))
                if n_soft_errors > 0
                    pluralpc = length(s.configs) > 1 ? "dependency configurations" : n_soft_errors == 1 ? "dependency" : "dependencies"
                    print(iostr, "\n  ",
                        color_string(string(n_soft_errors), Base.warn_color(), s.hascolor),
                        " $(pluralpc) failed but may be precompilable after restarting julia"
                    )
                end
            end
            @lock BG BG.result = logstr
            BG.monitoring && @lock s.print_lock begin
                println(s.logio, logstr)
            end
        elseif s.interrupted || s.canceled
            istr = sprint(context=s.logio) do iostr
                if s.fancyprint
                    printpkgstyle(iostr, :Precompiling, s.canceled && !s.interrupted ? "canceled." : "interrupted.")
                end
                # On cancel we don't mark in-flight jobs as failed (their subprocesses
                # were killed by the cancel itself), so report them as the "canceled" count.
                # Use the sticky `had_pid` flag so we count jobs that actually spawned a
                # subprocess, not ones that were just past mark_started!. Soft errors are
                # completed jobs that errored before cancel; report them separately.
                n_soft_errors = count(j -> is_soft_error(j), values(s.jobs))
                n_canceled_i = s.canceled && !s.interrupted ?
                    count(j -> had_pid(j) && !is_recompiled(j) && !is_soft_error(j), values(s.jobs)) :
                    n_failed
                verb = s.canceled && !s.interrupted ? "canceled" : "interrupted"
                print(iostr, "  $(ndeps) dependenc$(ndeps == 1 ? "y" : "ies") precompiled, ",
                      color_string("$(n_canceled_i)", Base.error_color(), s.hascolor),
                      " $verb after $(seconds_elapsed) seconds")
                if n_soft_errors > 0
                    pluralpc = length(s.configs) > 1 ? "dependency configurations" : n_soft_errors == 1 ? "dependency" : "dependencies"
                    print(iostr, "\n  ",
                        color_string(string(n_soft_errors), Base.warn_color(), s.hascolor),
                        " $(pluralpc) failed but may be precompilable after restarting julia"
                    )
                end
            end
            @lock BG BG.result = istr
            BG.monitoring && @lock s.print_lock begin
                println(s.logio, istr)
            end
        end
    end
    if any(j -> j.output.size > 0, values(s.jobs))
        str = sprint(context=s.io) do iostr
            let std_outputs = Tuple{PkgConfig,SubString{String}}[(pc, strip(String(take!(job.output)))) for (pc, job) in s.jobs]
                filter!(!isempty∘last, std_outputs)
                if !isempty(std_outputs)
                    plural1 = length(std_outputs) == 1 ? "y" : "ies"
                    print(iostr, "  ", color_string("$(length(std_outputs))", Base.warn_color(), s.hascolor), " dependenc$(plural1) had output during precompilation:")
                    for (pkg_config, err) in std_outputs
                        pkg, _ = pkg_config
                        err = if pkg == s.pkg_liveprinted
                            "[Output was shown above]"
                        else
                            join(split(err, "\n"), color_string("\n│  ", Base.warn_color(), s.hascolor))
                        end
                        name = full_name(s.ext_to_parent, pkg)
                        print(iostr, color_string("\n┌ ", Base.warn_color(), s.hascolor), name, color_string("\n│  ", Base.warn_color(), s.hascolor), err, color_string("\n└  ", Base.warn_color(), s.hascolor))
                    end
                end
            end
        end
        !isempty(str) && BG.monitoring && @lock s.print_lock begin
            println(s.io, str)
        end
    end
    if n_failed > 0
        err_str = IOBuffer()
        for ((dep, config), job) in s.jobs
            is_failed(job) || continue
            write(err_str, "\n")
            print(err_str, "\n", full_name(s.ext_to_parent, dep), " ")
            join(err_str, config[1], " ")
            print(err_str, "\n", job.error_msg)
        end
        if n_dep_failed > 0
            # name only the skipped project deps; the rest are implied by them
            skipped = sort!(String[dep.name for ((dep, _), job) in s.jobs
                                   if is_dep_failed(job) && dep in s.project_deps && !haskey(s.ext_to_parent, dep)])
            print(err_str, "\n\n", n_dep_failed, n_dep_failed == 1 ? " package was" : " packages were",
                  " skipped because a dependency failed to precompile")
            if length(skipped) == n_dep_failed
                print(err_str, ": ", join(skipped, ", "))
            elseif !isempty(skipped)
                print(err_str, ", including ", join(skipped, ", "))
            end
            print(err_str, "\nTo attempt them anyway, pass `skip_dependents=false` (`pkg> precompile --noskip`).")
        end
        pluraled = n_failed == 1 ? "" : "s"
        err_msg = "The following $n_failed package$(pluraled) failed to precompile:$(String(take!(err_str)))\n"
        if s.internal_call
            print(s.io, err_msg)
        else
            throw(PkgPrecompileError(err_msg))
        end
    end
    if s.interrupted
        throw(InterruptException())
    end
    if s.canceled && s._from_loading
        # otherwise the loader would load the package from source without a cache
        throw(PkgPrecompileError("Precompilation was canceled, so the package was not loaded."))
    end
    return @lock s.cache_lock collect(String, Iterators.flatten((v for (pkgid, v) in s.cachepath_cache if pkgid in s.requested_pkgids)))
end

```
-/
/- The `while !isempty(frontier)` loop of the `n_affected` computation; returns `affected`. -/
def affected_loop [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T)
    (reverse_deps : T.Dict PkgId (List PkgId)) (loaded_set : T.Dict PkgId Unit) (affected : T.Dict PkgId Unit)
    (frontier : List PkgId) : m (T.Dict PkgId Unit) := do
  match frontier.getLast? with
  | none => pure affected
  | some p =>
    let frontier := frontier.dropLast
    let r := (getD o.D reverse_deps p []).foldl (fun (acc : T.Dict PkgId Unit × List PkgId) rdep =>
      if !setIn o.D acc.1 rdep && !setIn o.D loaded_set rdep then (setPush o.D acc.1 rdep, acc.2 ++ [rdep]) else acc)
      (affected, frontier)
    affected_loop o reverse_deps loaded_set r.1 r.2
partial_fixpoint

/-- The summary written by `sprint(context=s.logio) do iostr ... end` when not `quick_exit`. -/
def summary_text [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T) (s : T.Sess) (iostr : T.Stream)
    (ndeps n_dep_failed seconds_elapsed : JInt64) : m Unit := do
  let st ← o.sget s
  if st.fancyprint then
    let what ← if st.n_batches.val > 1 then pure (lit "done.")
      else if st.requested_pkgids.isEmpty || st.requested_all then pure (lit "packages finished.")
      else do
        let names ← st.requested_pkgids.mapM (full_name o.D st.ext_to_parent)
        pure (joinLast (lit ", ") (lit " and ") names ++ lit " finished.")
    pps o iostr "Precompiling" what
  let plural := if st.configs.length > 1 then "dependency configurations" else if ndeps.val == 1 then "dependency"
    else "dependencies"
  o.print iostr (lit "  " ++ istr ndeps ++ lit " " ++ lit plural ++ lit " successfully precompiled in " ++
    istr seconds_elapsed ++ lit " seconds")
  if st.n_already_precomp.val > 0 || !st.circular_deps.isEmpty || n_dep_failed.val > 0 then
    if st.n_already_precomp.val > 0 then o.print iostr (lit ". " ++ istr st.n_already_precomp ++ lit " already precompiled")
    if !st.circular_deps.isEmpty then
      o.print iostr (lit ". " ++ istr (ji st.circular_deps.length) ++ lit " skipped due to circular dependency")
    if n_dep_failed.val > 0 then
      o.print iostr (lit ". " ++ istr n_dep_failed ++ lit " skipped because a dependency failed to precompile")
    o.print iostr (lit ".")
  if st.n_loaded.val > 0 then
    let loaded_names_vec := sortBytes (← st.loaded_pkgs.mapM (full_name o.D st.ext_to_parent))
    if st._from_loading && !st.ignore_loaded then
      -- loading compiles dependents for the loaded version, so the loaded
      -- package is the reason for this session rather than its result;
      -- say so here for those not already explained under the header
      let differ ← st.loaded_pkgs.filterM (loaded_version_differs o)
      let differing := sortBytes (← differ.mapM (full_name o.D st.ext_to_parent))
      let unexplained := vsetdiff differing st.explained_conflicts.contains
      if !unexplained.isEmpty then
        o.print iostr (lit "\n" ++ (← loaded_conflicts_message o unexplained st.hascolor false false))
    else
      let plural1 := if st.configs.length > 1 then "dependency configurations" else if st.n_loaded.val == 1 then "dependency"
        else "dependencies"
      let plural2 := if st.n_loaded.val == 1 then "a different version is" else "different versions are"
      let plural3 := if st.n_loaded.val == 1 then "" else "s"
      let loaded_names ← format_names_list loaded_names_vec
      -- compute how many precompiled packages transitively depend on the loaded packages
      let loaded_set := st.loaded_pkgs.foldl (setPush o.D) o.D.empty
      let mut reverse_deps : T.Dict PkgId (List PkgId) := o.D.empty
      for p in o.D.keys st.direct_deps do
        for d in ← getindex o.D st.direct_deps p do
          reverse_deps := o.D.set reverse_deps d (getD o.D reverse_deps d [] ++ [p])
      let affected ← affected_loop o reverse_deps loaded_set o.D.empty (o.D.keys loaded_set)
      let n_affected := (o.D.keys affected).length
      o.print iostr (lit "\n  " ++ (← color_string (istr st.n_loaded) (← o.warn_color) st.hascolor) ++
        lit " " ++ lit plural1 ++ lit " precompiled but " ++
        (← color_string (lit plural2 ++ lit " currently loaded") (← o.warn_color) st.hascolor) ++
        lit " (" ++ loaded_names ++ lit ")" ++ lit ". Restart julia to access the new version" ++ lit plural3 ++ lit ".")
      if n_affected > 0 then
        let affected_plural := if st.configs.length > 1 then "dependency configurations" else if n_affected == 1 then "dependent"
          else "dependents"
        o.print iostr (lit " Otherwise, " ++ istr (ji n_affected) ++ lit " " ++ lit affected_plural ++ lit " of " ++
          lit (if st.n_loaded.val == 1 then "this package" else "these packages") ++
          lit " may trigger further precompilation to work with the unexpected version" ++ lit plural3 ++ lit ".")
  let jobs ← (o.D.keys st.jobs).mapM (getindex o.D st.jobs)
  let n_soft_errors := (jobs.filter is_soft_error).length
  if n_soft_errors > 0 then
    let pluralpc := if st.configs.length > 1 then "dependency configurations" else if n_soft_errors == 1 then "dependency"
      else "dependencies"
    o.print iostr (lit "\n  " ++ (← color_string (istr (ji n_soft_errors)) (← o.warn_color) st.hascolor) ++
      lit " " ++ lit pluralpc ++ lit " failed but may be precompilable after restarting julia")

/-- The report written by `sprint(context=s.logio) do iostr ... end` after an interrupt or cancel. -/
def interrupted_text (o : Ops m T) (s : T.Sess) (iostr : T.Stream) (ndeps n_failed seconds_elapsed : JInt64) : m Unit := do
  let st ← o.sget s
  if st.fancyprint then
    pps o iostr "Precompiling" (lit (if st.canceled && !st.interrupted then "canceled." else "interrupted."))
  -- On cancel we don't mark in-flight jobs as failed (their subprocesses
  -- were killed by the cancel itself), so report them as the "canceled" count.
  -- Use the sticky `had_pid` flag so we count jobs that actually spawned a
  -- subprocess, not ones that were just past mark_started!. Soft errors are
  -- completed jobs that errored before cancel; report them separately.
  let jobs ← (o.D.keys st.jobs).mapM (getindex o.D st.jobs)
  let n_soft_errors := (jobs.filter is_soft_error).length
  let n_canceled_i := if st.canceled && !st.interrupted then
      ji (jobs.filter fun j => had_pid j && !is_recompiled j && !is_soft_error j).length
    else n_failed
  let verb := if st.canceled && !st.interrupted then "canceled" else "interrupted"
  o.print iostr (lit "  " ++ istr ndeps ++ lit " dependenc" ++ lit (if ndeps.val == 1 then "y" else "ies") ++
    lit " precompiled, " ++ (← color_string (istr n_canceled_i) (← o.error_color) st.hascolor) ++
    lit " " ++ lit verb ++ lit " after " ++ istr seconds_elapsed ++ lit " seconds")
  if n_soft_errors > 0 then
    let pluralpc := if st.configs.length > 1 then "dependency configurations" else if n_soft_errors == 1 then "dependency"
      else "dependencies"
    o.print iostr (lit "\n  " ++ (← color_string (istr (ji n_soft_errors)) (← o.warn_color) st.hascolor) ++
      lit " " ++ lit pluralpc ++ lit " failed but may be precompilable after restarting julia")

/-- The captured-output report written by `sprint(context=s.io) do iostr ... end`. -/
def outputs_text (o : Ops m T) (s : T.Sess) (iostr : T.Stream) : m Unit := do
  let st ← o.sget s
  let mut std_outputs : List (PkgConfig T × Bytes) := []
  for pc in o.D.keys st.jobs do
    let job ← getindex o.D st.jobs pc
    std_outputs := std_outputs ++ [(pc, o.strip (← o.bufTake job.output))]
  std_outputs := std_outputs.filter (!·.2.isEmpty)
  if !std_outputs.isEmpty then
    let plural1 := if std_outputs.length == 1 then "y" else "ies"
    o.print iostr (lit "  " ++ (← color_string (istr (ji std_outputs.length)) (← o.warn_color) st.hascolor) ++
      lit " dependenc" ++ lit plural1 ++ lit " had output during precompilation:")
    for (pkg_config, err) in std_outputs do
      let pkg := pkg_config.1
      let st ← o.sget s
      let err ← if some pkg == st.pkg_liveprinted then pure (lit "[Output was shown above]")
        else do pure (joinB (← color_string (lit "\n│  ") (← o.warn_color) st.hascolor) (splitNL err))
      let name ← full_name o.D st.ext_to_parent pkg
      o.print iostr ((← color_string (lit "\n┌ ") (← o.warn_color) st.hascolor) ++ name ++
        (← color_string (lit "\n│  ") (← o.warn_color) st.hascolor) ++ err ++
        (← color_string (lit "\n└  ") (← o.warn_color) st.hascolor))

/-- `report_precompile_results!(s)`. -/
def report_precompile_results [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T) (s : T.Sess) :
    m (List Bytes) := do
  if !(← o.sget s)._from_loading then
    o.withLock o.require_lock o.clearLoadingCache
  o.notifyEv (← o.sget s).first_started -- in cases of no-op or !fancyprint
  -- a cancel that lands while the last job runs is not seen by the job loop
  discard (should_stop o s)
  let st ← o.sget s
  let quick_exit ← do
    let busy ← st.tasks.anyM fun t => do return !(← o.istaskdone t) || (← o.istaskfailed t)
    pure (busy || st.interrupted || st.canceled)
  let seconds_elapsed ← do
    let t ← if st.time_start.val > 0 then do pure (uitofp .f64 ((← o.time_ns) - st.time_start)) else pure (fl 0)
    o.roundInt (div_float t (fl 0x41CDCD6500000000))
  let jobs ← (o.D.keys st.jobs).mapM (getindex o.D st.jobs)
  let ndeps := ji (jobs.filter is_recompiled).length
  let mut requested_errs := false
  for pc in o.D.keys st.jobs do
    let job ← getindex o.D st.jobs pc
    if (is_failed job || is_dep_failed job) && st.requested_pkgids.contains pc.1 then
      requested_errs := true
      break
  if !st.strict && !requested_errs && !st.interrupted && !st.canceled then
    for pc in o.D.keys (← o.sget s).jobs do
      let job ← getJob o s pc
      if is_failed job || is_dep_failed job then
        let j ← clear_failure o.truncate0 job
        o.smodify s fun st => { st with jobs := o.D.set st.jobs pc j }
  if st.canceled then
    if !(← lock_BG o do return (← o.bgget).info_requested) then
      -- Drop captured stdout/stderr from jobs that didn't fail before cancel,
      -- since their output is just truncated cancel-induced noise. If the user
      -- asked for info (SIGINFO/SIGUSR1) at any point, keep the output so the
      -- profiling info gets surfaced in the cancel report. Soft errors
      -- (e.g. `?` packages) are completed jobs whose captured output is the
      -- actual precompile error message, so preserve it as well.
      for pc in o.D.keys (← o.sget s).jobs do
        let job ← getJob o s pc
        if is_failed job || is_soft_error job then continue
        if (← o.bufSize job.output).val > 0 then discard (o.truncate0 job.output)
  let st ← o.sget s
  let jobs ← (o.D.keys st.jobs).mapM (getindex o.D st.jobs)
  let n_failed := ji (jobs.filter is_failed).length
  -- skipped extensions are implied by their parent or trigger failing, so only count packages
  let mut n_dep_failed := ji 0
  for pc in o.D.keys st.jobs do
    let j ← getindex o.D st.jobs pc
    if is_dep_failed j && !haskey o.D st.ext_to_parent pc.1 then n_dep_failed := n_dep_failed + ji 1
  if ndeps.val > 0 || n_failed.val > 0 then
    if !quick_exit then
      let (logstr, _) ← o.sprintCtx st.logio fun iostr => summary_text o s iostr ndeps n_dep_failed seconds_elapsed
      lock_BG o (o.bgmodify fun bg => { bg with result := some logstr })
      if (← o.bgget).monitoring then
        o.withLock (← o.sget s).print_lock (println o (o.ctx (← o.sget s).logio) logstr)
    else if st.interrupted || st.canceled then
      let (istr_, _) ← o.sprintCtx st.logio fun iostr => interrupted_text o s iostr ndeps n_failed seconds_elapsed
      lock_BG o (o.bgmodify fun bg => { bg with result := some istr_ })
      if (← o.bgget).monitoring then
        o.withLock (← o.sget s).print_lock (println o (o.ctx (← o.sget s).logio) istr_)
  let anyOutput ← ((o.D.keys (← o.sget s).jobs).mapM (getJob o s)) >>= fun js =>
    js.anyM fun j => do return (← o.bufSize j.output).val > 0
  if anyOutput then
    let (str, _) ← o.sprintCtx (← o.sget s).io fun iostr => outputs_text o s iostr
    if !str.isEmpty then
      if (← o.bgget).monitoring then
        o.withLock (← o.sget s).print_lock (println o (o.ctx (← o.sget s).io) str)
  if n_failed.val > 0 then
    let st ← o.sget s
    let mut err_str : Bytes := []
    for pc in o.D.keys st.jobs do
      let job ← getindex o.D st.jobs pc
      if !is_failed job then continue
      err_str := err_str ++ lit "\n"
      err_str := err_str ++ lit "\n" ++ (← full_name o.D st.ext_to_parent pc.1) ++ lit " "
      err_str := err_str ++ joinB (lit " ") (o.cmdArgs pc.2.1)
      err_str := err_str ++ lit "\n" ++ job.error_msg
    if n_dep_failed.val > 0 then
      -- name only the skipped project deps; the rest are implied by them
      let mut skipped : List Bytes := []
      for pc in o.D.keys st.jobs do
        let job ← getindex o.D st.jobs pc
        if is_dep_failed job && st.project_deps.contains pc.1 && !haskey o.D st.ext_to_parent pc.1 then
          skipped := skipped ++ [pc.1.name]
      skipped := sortBytes skipped
      err_str := err_str ++ lit "\n\n" ++ istr n_dep_failed ++
        lit (if n_dep_failed.val == 1 then " package was" else " packages were") ++
        lit " skipped because a dependency failed to precompile"
      if (skipped.length : Int) == n_dep_failed.val then
        err_str := err_str ++ lit ": " ++ joinB (lit ", ") skipped
      else if !skipped.isEmpty then
        err_str := err_str ++ lit ", including " ++ joinB (lit ", ") skipped
      err_str := err_str ++ lit "\nTo attempt them anyway, pass `skip_dependents=false` (`pkg> precompile --noskip`)."
    let pluraled := if n_failed.val == 1 then "" else "s"
    let err_msg := lit "The following " ++ istr n_failed ++ lit " package" ++ lit pluraled ++
      lit " failed to precompile:" ++ err_str ++ lit "\n"
    if st.internal_call then
      o.print (o.ctx st.io) err_msg
    else
      throwP (.pkgPrecompileError err_msg)
  let st ← o.sget s
  if st.interrupted then throwP .interruptException
  if st.canceled && st._from_loading then
    -- otherwise the loader would load the package from source without a cache
    throwP (.pkgPrecompileError (lit "Precompilation was canceled, so the package was not loaded."))
  o.withLock (← o.sget s).cache_lock (do collect_paths o (← o.sget s).cachepath_cache (← o.sget s).requested_pkgids)

/--
Julia source: base/precompilation.jl:3275-3482 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# The actual precompilation implementation (mode-agnostic)
function do_precompile(pkgs::Union{Vector{String}, Vector{PkgId}},
                        internal_call::Bool,
                        strict::Bool,
                        warn_loaded::Bool,
                        timing::Bool,
                        _from_loading::Bool,
                        _reasons::Dict{Symbol,Int},
                        configs::Vector{Config},
                        io::IOContext,
                        fancyprint′::Bool,
                        manifest::Bool,
                        ignore_loaded::Bool,
                        detachable::Bool,
                        skip_dependents::Bool,
                        force::Bool,
                        force_stdlibs::Bool,
                        work_channel::Channel{PrecompileRequest})
    requested_pkgs = copy(pkgs)
    pkg_names = pkgs isa Vector{String} ? copy(pkgs) : String[pkg.name for pkg in pkgs]
    if pkgs isa Vector{PkgId}
        requested_pkgids = copy(pkgs)
    else
        requested_pkgids = PkgId[]
        for name in pkgs
            pkgid = Base.identify_package(name)
            if pkgid === nothing
                _from_loading && return
                throw(PkgPrecompileError("Unknown package: $name"))
            end
            push!(requested_pkgids, pkgid)
        end
    end

    time_start = time_ns()
    env = ExplicitEnv()

    # Windows sometimes hits a ReadOnlyMemoryError, so we halve the default number of tasks. Pkg.jl#2323
    # TODO: Investigate why this happens in windows and restore the full task limit
    default_num_tasks = Sys.iswindows() ? div(Sys.EFFECTIVE_CPU_THREADS::Int, 2) + 1 : Sys.EFFECTIVE_CPU_THREADS::Int + 1
    default_num_tasks = min(default_num_tasks, 16) # limit for better stability on shared resource systems
    num_tasks = max(1, something(tryparse(Int, get(ENV, "JULIA_NUM_PRECOMPILE_TASKS", string(default_num_tasks))), 1))

    # When loading precompiles outside an interactive session, report only that it is
    # precompiling, why, and the result, in plain lines, so that a script does not look stuck
    # and a CI log shows unexpected precompilation without per-package noise. Progress
    # animation in the background can garble other output (#59599). `-q` silences it all.
    logio = io
    logcalls = nothing
    brief = false
    if _from_loading
        if isinteractive()
            logcalls = CoreLogging.Info
        elseif Base.JLOptions().quiet != 0
            logio = IOContext{IO}(devnull)
            fancyprint′ = false
            logcalls = CoreLogging.Debug
        else
            fancyprint′ = false
            brief = true
            logcalls = CoreLogging.Info
        end
    end
    fancyprint = fancyprint′
    hascolor = get(logio, :color, false)::Bool

    # Build dependency graph
    graph = build_dep_graph(env, manifest, _from_loading, requested_pkgids)

    # Return early if no deps
    if isempty(graph.direct_deps)
        isempty(pkgs) && return
        # a request for packages that are all in the sysimage has nothing to do
        all(Base.in_sysimage, requested_pkgids) && return
        error("No direct dependencies outside of the sysimage found matching $(pkgs)")
    end

    # Initialize signalling
    was_processed = Dict{PkgConfig,Base.Event}()
    jobs = Dict{PkgConfig,PrecompileJob}()
    for config in configs
        for pkgid in keys(graph.direct_deps)
            pkg_config = (pkgid, config)
            jobs[pkg_config] = PrecompileJob()
            was_processed[pkg_config] = Base.Event()
        end
    end

    circular_deps = detect_circular_deps!(graph.direct_deps, graph.serial_deps, was_processed, io, graph.ext_to_parent)

    if filter_dep_graph!(graph.direct_deps, pkg_names, graph.ext_to_parent, requested_pkgids)
        @lock BG BG.result = ""
        return
    end

    # When no specific packages were requested, treat project deps as the requested
    # set so direct-dep failures are reported and the returned paths cover the project.
    requested_all = isempty(requested_pkgids)
    requested_all && append!(requested_pkgids, graph.project_deps)

    nconfigs = length(configs)
    target = if nconfigs == 1
        flags = only(configs)[1]
        if !isempty(flags)
            "for configuration $(join(flags, " "))"
        elseif requested_all
            "project..."
        elseif brief
            # without a line per package, name what is being loaded
            "$(join((p.name for p in requested_pkgids), ", ", " and "))..."
        else
            "packages..."
        end
    else
        "for $nconfigs compilation configurations"
    end

    print_lock = io.io isa Base.LibuvStream ? io.io.lock::ReentrantLock : ReentrantLock()

    # Size the shared CPU-thread budget for the parallel workers. Defaults to
    # `EFFECTIVE_CPU_THREADS + 1` (one baseline per worker plus a spare so a lone
    # worker can fill every core during imaging); `JULIA_PRECOMPILE_THREADS`
    # overrides it. Skipped for a single task or when JULIA_IMAGE_THREADS pins a
    # per-worker count (a hard override that bypasses the shared budget), unless
    # `JULIA_PRECOMPILE_THREADS` is also set, in which case it takes precedence.
    # Examples:
    #   neither set                                      -> jobserver budget = EFFECTIVE_CPU_THREADS + 1
    #   JULIA_PRECOMPILE_THREADS=8                       -> jobserver budget = 8
    #   JULIA_IMAGE_THREADS=4                            -> no jobserver; each worker pinned to 4 threads
    #   JULIA_IMAGE_THREADS=4 JULIA_PRECOMPILE_THREADS=8 -> jobserver budget = 8 (JULIA_IMAGE_THREADS ignored here)
    precompile_jobserver = if num_tasks > 1 && (haskey(ENV, "JULIA_PRECOMPILE_THREADS") || !haskey(ENV, "JULIA_IMAGE_THREADS"))
        default_budget = Sys.EFFECTIVE_CPU_THREADS + 1
        budget = max(1, something(tryparse(Int, get(ENV, "JULIA_PRECOMPILE_THREADS", string(default_budget))), default_budget))
        setup_precompile_jobserver!(budget)
    else
        :none
    end

    s = PrecompileSession(;
        configs, io, logio, logcalls, fancyprint, brief, hascolor,
        warn_loaded, ignore_loaded, internal_call, strict, _from_loading,
        skip_dependents, force, force_stdlibs,
        reasons=copy(_reasons),
        time_start, print_lock,
        parallel_limiter=WorkerLimiter(num_tasks, precompile_jobserver !== :none), num_tasks,
        start_loaded_modules=Set{PkgId}(keys(Base.loaded_modules)), requested_pkgids, requested_all,
        direct_deps=graph.direct_deps,
        ext_to_parent=graph.ext_to_parent, parent_to_exts=graph.parent_to_exts,
        triggers=graph.triggers, project_deps=graph.project_deps,
        serial_deps=graph.serial_deps, circular_deps,
        n_total=length(graph.direct_deps) * nconfigs,
        printloop_should_exit=!fancyprint, target,
        jobs, was_processed,
    )

    # Start print loop
    t_print = spawn_print_loop!(s)
    # In non-fancy mode the print loop exits immediately and so `poll_process_stats!`
    # never runs; sample peak RSS on a timer instead for the `~pk-rss` column.
    # Gated per tick since verbose can be enabled mid-run (injected request, `v` key).
    # Locks taken sequentially: the print loop nests BG inside print_lock.
    peak_rss_timer = if !fancyprint
        Timer(0.1; interval=0.5, spawn=true) do _
            verbose_now = @lock BG BG.verbose
            verbose_now && @lock s.print_lock sample_peak_rss!(s.jobs)
        end
    else
        nothing
    end

    try
        if !_from_loading
            @lock Base.require_lock begin
                Base.LOADING_CACHE[] = Base.LoadingCache()
            end
        end
        @debug "precompile: starting precompilation loop" graph.direct_deps graph.project_deps

        # Initial pass
        initial_tasks = spawn_precompile_tasks!(s;
            direct_deps=graph.direct_deps, was_processed, configs, circular_deps,
            requested_pkgids, pkg_names, requested_pkgs, from_loading=_from_loading)
        append!(s.tasks, initial_tasks)

        # Concurrent drainer for injected requests
        drainer = drain_work_channel!(s, work_channel)

        waitall(initial_tasks; failfast=false, throw=false)
        @lock BG close(work_channel)
        wait(drainer)
        append!(s.tasks, s.injected_tasks)
        waitall(s.injected_tasks; failfast=false, throw=false)
        waitall(s.result_waiters; failfast=false, throw=false)

        # Final output
        s.interrupted_or_done = true
        notify(s.first_started) # unblock print loop if nothing ever started (no-op case)
        fancyprint && wait(t_print)
        return report_precompile_results!(s)
    finally
        # Ensure print loop exits even on exception
        s.interrupted_or_done = true
        notify(s.first_started)
        peak_rss_timer === nothing || close(peak_rss_timer)
        precompile_jobserver === :created && teardown_precompile_jobserver!()
    end
end

```
-/
/- `do_precompile(...)`: `nothing` is `none`. `Sys.EFFECTIVE_CPU_THREADS::Int` and the other runtime
values are `Ops` operations. -/
def do_precompile [MonadFinally m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T)
    (pkgs : Pkgs) (internal_call strict warn_loaded _timing _from_loading : Bool) (_reasons : T.Dict Bytes JInt64)
    (configs : List (Config T)) (io : T.IOC) (fancyprint' manifest ignore_loaded _detachable skip_dependents force
      force_stdlibs : Bool) (work_channel : T.ReqChan) : m (Option (List Bytes)) := do
  let requested_pkgs := pkgs
  let pkg_names := match pkgs with
    | .names ns => ns
    | .ids ps => ps.map (·.name)
  let mut requested_pkgids : List PkgId := []
  match pkgs with
  | .ids ps => requested_pkgids := ps
  | .names ns =>
    for name in ns do
      let pkgid ← o.identify_package name
      match pkgid with
      | none =>
        if _from_loading then return none
        throwP (.pkgPrecompileError (lit "Unknown package: " ++ name))
      | some p => requested_pkgids := requested_pkgids ++ [p]
  let time_start ← o.time_ns
  let env ← ExplicitEnv_0 o.D o.any o.env
  -- Windows sometimes hits a ReadOnlyMemoryError, so we halve the default number of tasks. Pkg.jl#2323
  -- TODO: Investigate why this happens in windows and restore the full task limit
  let cpu ← o.EFFECTIVE_CPU_THREADS
  let default_num_tasks := if o.iswindows then ji (cpu.val.tdiv 2) + ji 1 else cpu + ji 1
  let default_num_tasks := ji (min default_num_tasks.val 16) -- limit for better stability on shared resource systems
  let tasksEnv := (← o.getENV (lit "JULIA_NUM_PRECOMPILE_TASKS")).getD (istr default_num_tasks)
  let num_tasks := ji (max 1 ((o.tryparseInt tasksEnv).getD (ji 1)).val)
  -- When loading precompiles outside an interactive session, report only that it is
  -- precompiling, why, and the result, in plain lines, so that a script does not look stuck
  -- and a CI log shows unexpected precompilation without per-package noise. Progress
  -- animation in the background can garble other output (#59599). `-q` silences it all.
  let mut logio := io
  let mut logcalls : Option T.LogLevel := none
  let mut brief := false
  let mut fancyprint' := fancyprint'
  if _from_loading then
    if ← o.isinteractive then
      logcalls := some o.logInfo
    else if (← o.jlQuiet).val != 0 then
      logio := o.wrapIO o.devnull
      fancyprint' := false
      logcalls := some o.logDebug
    else
      fancyprint' := false
      brief := true
      logcalls := some o.logInfo
  let fancyprint := fancyprint'
  let hascolor ← ioHascolor o logio
  -- Build dependency graph
  let graph ← build_dep_graph o.D o.graph env manifest _from_loading requested_pkgids
  -- Return early if no deps
  if (o.D.keys graph.direct_deps).isEmpty then
    if pkgs.isEmpty then return none
    -- a request for packages that are all in the sysimage has nothing to do
    if ← requested_pkgids.allM o.graph.in_sysimage then return none
    throwP (.errorException (lit "No direct dependencies outside of the sysimage found matching " ++ o.showPkgs pkgs))
  -- Initialize signalling
  let mut was_processed : T.Dict (PkgConfig T) T.Ev := o.D.empty
  let mut jobs : T.Dict (PkgConfig T) (PrecompileJob T.Buf) := o.D.empty
  for config in configs do
    for pkgid in o.D.keys graph.direct_deps do
      let pkg_config : PkgConfig T := (pkgid, config)
      jobs := o.D.set jobs pkg_config (PrecompileJob.new (← o.newBuf))
      was_processed := o.D.set was_processed pkg_config (← o.newEvent)
  let circular_deps ← detect_circular_deps_io o graph.direct_deps graph.serial_deps was_processed io graph.ext_to_parent
  let (direct_deps, empty) ← filter_dep_graph o.D graph.direct_deps pkg_names graph.ext_to_parent requested_pkgids
  if empty then
    lock_BG o (o.bgmodify fun bg => { bg with result := some [] })
    return none
  -- When no specific packages were requested, treat project deps as the requested
  -- set so direct-dep failures are reported and the returned paths cover the project.
  let requested_all := requested_pkgids.isEmpty
  if requested_all then requested_pkgids := requested_pkgids ++ graph.project_deps
  let nconfigs := configs.length
  let target ← if nconfigs == 1 then do
      -- `only(configs)[1]`
      let flags ← match configs with
        | [c] => pure c.1
        | _ => throwP .argumentError
      if !(o.cmdArgs flags).isEmpty then pure (lit "for configuration " ++ joinB (lit " ") (o.cmdArgs flags))
      else if requested_all then pure (lit "project...")
      -- without a line per package, name what is being loaded
      else if brief then pure (joinLast (lit ", ") (lit " and ") (requested_pkgids.map (·.name)) ++ lit "...")
      else pure (lit "packages...")
    else pure (lit "for " ++ istr (ji nconfigs) ++ lit " compilation configurations")
  let print_lock ← match ← o.streamLock io with
    | some l => pure l
    | none => o.newLock
  -- Size the shared CPU-thread budget for the parallel workers (see the source comment).
  let use_jobserver ← if num_tasks.val > 1 then do
      if (← o.getENV (lit "JULIA_PRECOMPILE_THREADS")).isSome then pure true
      else do pure (← o.getENV (lit "JULIA_IMAGE_THREADS")).isNone
    else pure false
  let precompile_jobserver ← if use_jobserver then do
      let default_budget := (← o.EFFECTIVE_CPU_THREADS) + ji 1
      let budgetEnv := (← o.getENV (lit "JULIA_PRECOMPILE_THREADS")).getD (istr default_budget)
      let budget := ji (max 1 ((o.tryparseInt budgetEnv).getD default_budget).val)
      setup_precompile_jobserver o.jobserver budget
    else pure JobserverSetup.none
  let limiter := WorkerLimiter.new (← o.newCondition) num_tasks (precompile_jobserver != .none)
  let start_loaded_modules := (← o.loadedModuleKeys).foldl (setPush o.D) o.D.empty
  let first_started ← o.newEvent
  let cache_lock ← o.newLock
  let s ← o.snew {
    configs, io, logio, logcalls, fancyprint, brief, hascolor,
    warn_loaded, ignore_loaded, internal_call, strict, _from_loading,
    skip_dependents, force, force_stdlibs,
    reasons := _reasons,
    header_printed := false, explained_pkgids := o.D.empty, explained_conflicts := [], flags_explained := false,
    time_start, print_lock,
    parallel_limiter := limiter, num_tasks,
    start_loaded_modules, requested_pkgids, requested_all,
    direct_deps,
    ext_to_parent := graph.ext_to_parent, parent_to_exts := graph.parent_to_exts,
    triggers := graph.triggers, project_deps := graph.project_deps,
    serial_deps := graph.serial_deps, circular_deps,
    n_done := ji 0, n_already_precomp := ji 0, n_loaded := ji 0, loaded_pkgs := [],
    n_total := ji ((o.D.keys direct_deps).length * nconfigs), n_batches := ji 1,
    interrupted := false, canceled := false, interrupted_or_done := false,
    printloop_should_exit := !fancyprint, target, pkg_liveprinted := none,
    jobs, was_processed,
    stale_cache := o.D.empty, cachepath_cache := o.D.empty, unverified := o.D.empty, pkg_queue := [],
    prev_cpu_times := o.D.empty, first_started, cache_lock,
    tasks := [], injected_tasks := [], result_waiters := [] }
  -- Start print loop
  let t_print ← spawn_print_loop o s
  -- In non-fancy mode the print loop exits immediately and so `poll_process_stats!`
  -- never runs; sample peak RSS on a timer instead for the `~pk-rss` column.
  -- Gated per tick since verbose can be enabled mid-run (injected request, `v` key).
  -- Locks taken sequentially: the print loop nests BG inside print_lock.
  let peak_rss_timer ← if !fancyprint then do
      some <$> o.newTimerCb (fl 0x3FB999999999999A) (fl 0x3FE0000000000000) (do
        let verbose_now ← lock_BG o do return (← o.bgget).verbose
        if verbose_now then
          o.withLock (← o.sget s).print_lock (do write_peaks o s (← sample_peak_rss o (← o.sget s).jobs)))
    else pure none
  tryFinally
    (do
      if !_from_loading then
        o.withLock o.require_lock o.newLoadingCache
      o.debugStartingLoop direct_deps graph.project_deps
      -- Initial pass
      let initial_tasks ← spawn_precompile_tasks o s direct_deps was_processed configs circular_deps
        requested_pkgids pkg_names requested_pkgs _from_loading
      o.smodify s fun st => { st with tasks := st.tasks ++ initial_tasks }
      -- Concurrent drainer for injected requests
      let drainer ← drain_work_channel o s work_channel
      o.waitall initial_tasks
      lock_BG o (o.reqClose work_channel)
      o.waitTask drainer
      o.smodify s fun st => { st with tasks := st.tasks ++ st.injected_tasks }
      o.waitall (← o.sget s).injected_tasks
      o.waitall (← o.sget s).result_waiters
      -- Final output
      o.smodify s fun st => { st with interrupted_or_done := true }
      o.notifyEv (← o.sget s).first_started -- unblock print loop if nothing ever started (no-op case)
      if fancyprint then o.waitTask t_print
      some <$> report_precompile_results o s)
    (do
      -- Ensure print loop exits even on exception
      o.smodify s fun st => { st with interrupted_or_done := true }
      o.notifyEv (← o.sget s).first_started
      if let some t := peak_rss_timer then o.closeTimer t
      if precompile_jobserver == .created then teardown_precompile_jobserver o.jobserver)

end results

section entry
variable {m : Type → Type} [Monad m] [MonadExceptOf PError m] {T : Rt}
open JuliaLean.base.float (sub_float add_float mul_float div_float lt_float le_float uitofp sitofp)

/-- `exit_requested[] || cancel_requested[] || interrupt_requested[]`. -/
def anyRequested (o : Ops m T) (exit_requested cancel_requested interrupt_requested : T.BRef) : m Bool := do
  if ← o.bget exit_requested then return true
  if ← o.bget cancel_requested then return true
  o.bget interrupt_requested

/--
Julia source: base/precompilation.jl:1555-1848 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _monitor_background_precompile(io::IOContext{IO}, detachable::Bool, wait_for_pkg::Union{Nothing, PkgId};
                                        key_controls::Union{Bool, Nothing})
    # By default only enable key controls when this task is the foreground task (see #61563, #61698).
    # Falls back to roottask when no foreground task is registered (e.g. non-REPL interactive scripts).
    foreground = current_task() === something(Base.foreground_task(), Base.roottask)
    key_controls = @something key_controls foreground
    local completed_at::Union{Nothing, Float64}
    local task

    @lock BG begin
        completed_at = BG.completed_at
        task = BG.task
    end

    if task === nothing || istaskdone(task)
        if completed_at !== nothing
            elapsed = time() - completed_at
            time_str = if elapsed < 60
                "$(round(Int, elapsed)) seconds ago"
            elseif elapsed < 3600
                "$(round(Int, elapsed / 60)) minutes ago"
            elseif elapsed < 86400
                "$(round(Int, elapsed / 3600)) hours ago"
            else
                "$(round(Int, elapsed / 86400)) days ago"
            end
            printpkgstyle(io, :Info, "Background precompilation completed $time_str", color = Base.info_color())
            result = @lock BG BG.result
            if result !== nothing && !isempty(result)
                println(io, "  ", result)
            end
        else
            printpkgstyle(io, :Info, "No background precompilation is running or has been run in this session", color = Base.info_color())
        end
        return
    end

    key_controls &= stdin isa Base.TTY
    # Enable output from do_precompile
    @lock BG begin
        BG.monitoring = true
        BG.key_controls = key_controls
    end
    # cursor and clearing codes only mean something to a terminal showing the progress display
    clear = can_fancyprint(io) ? ansi_cleartoend : ""
    restore = isempty(clear) ? "" : ansi_enablecursor * clear

    exit_requested = Ref(false)
    cancel_requested = Ref(false)
    interrupt_requested = Ref(false)

    # Start a task to listen for keypresses. Skipped if another reader already holds
    # raw mode on stdin (e.g. runtests.jl's stdin_monitor).
    key_task = if key_controls
        Threads.@spawn :samepool try
            trylock(stdin.raw_lock) || return
            @lock BG begin
                BG.detachable = detachable
                BG.confirming = :none
                BG.key_listening = true
            end
            buffered_input = UInt8[]
            try
                term = Base.Terminals.TTYTerminal(get(ENV, "TERM", "dumb"), stdin, stdout, stderr)
                Base.Terminals.raw!(term, true)
                # Drain any pre-existing input (e.g. pasted or pre-typed text)
                # before entering the key listener. This avoids accidentally
                # triggering menu actions from stale input (see #61520).
                # The drained bytes are replayed into stdin on exit.
                # We must start_reading + yield first so libuv delivers any
                # bytes sitting in the kernel tty buffer into stdin.buffer.
                Base.start_reading(stdin)
                yield()
                while bytesavailable(stdin) > 0
                    push!(buffered_input, read(stdin, UInt8))
                end
                try
                    while true
                        completed = @lock BG (BG.completed_at !== nothing)
                        if completed || exit_requested[] || cancel_requested[] || interrupt_requested[]
                            break
                        end
                        Base.wait_readnb(stdin, 1)
                        completed = @lock BG (BG.completed_at !== nothing)
                        if completed || exit_requested[] || cancel_requested[] || interrupt_requested[]
                            break
                        end
                        bytesavailable(stdin) > 0 || continue
                        c = read(stdin, Char)
                        # If waiting for confirmation, Enter confirms, anything else aborts
                        confirmed_action = @lock BG begin
                            prev = BG.confirming
                            BG.confirming = :none
                            (prev !== :none && c in ('\r', '\n')) ? prev : :none
                        end
                        if confirmed_action == :cancel
                            cancel_requested[] = true
                            @lock BG BG.cancel_requested = true
                            broadcast_signal(Base.SIGKILL)
                            break
                        elseif confirmed_action == :info
                            @lock BG BG.info_requested = true
                            broadcast_signal(Sys.isapple() ? Base.SIGINFO : Base.SIGUSR1)
                            continue
                        end
                        if c in ('c', 'C')
                            @lock BG begin
                                BG.confirming = :cancel
                                BG.confirm_deadline = time() + 5.0
                            end
                        elseif detachable && c in ('d', 'D', 'q', 'Q', ']')
                            exit_requested[] = true
                            break
                        elseif c == '\x03'  # Ctrl-C
                            interrupt_requested[] = true
                            println(io)  # newline after keypress
                            @lock BG BG.interrupt_requested = true
                            broadcast_signal(Base.SIGINT)
                            break
                        elseif c in ('i', 'I')
                            @lock BG begin
                                BG.confirming = :info
                                BG.confirm_deadline = time() + 5.0
                            end
                        elseif c in ('v', 'V')
                            @lock BG BG.verbose = !BG.verbose
                        elseif c in ('?', 'h', 'H')
                            @lock io begin
                                println(io, "  Keyboard shortcuts:", ansi_cleartoendofline)
                                println(io, "    c       Cancel precompilation via killing subprocesses (press Enter to confirm)", ansi_cleartoendofline)
                                if detachable
                                    println(io, "    d/q/]   Detach (precompilation continues in background)", ansi_cleartoendofline)
                                end
                                println(io, "    i       Send profiling signal to subprocesses (press Enter to confirm)", ansi_cleartoendofline)
                                fields = Sys.iswindows() ? "elapsed time and PID" : "elapsed time, PID, CPU% and memory"
                                println(io, "    v       Toggle verbose mode (show $(fields) for each worker)", ansi_cleartoendofline)
                                println(io, "    Ctrl-C  Interrupt (sends SIGINT, shows output)", ansi_cleartoendofline)
                                println(io, "    ?/h     Show this help", ansi_cleartoendofline)
                            end
                        end
                    end
                finally
                    Base.Terminals.raw!(term, false)
                end
            catch err
                err isa EOFError && return
                exit_requested[] = true
                rethrow()
            finally
                # Replay any buffered input back into stdin so the REPL
                # (or whatever reads stdin next) sees it as typed text.
                if !isempty(buffered_input)
                    lock(stdin.cond)
                    try
                        write(stdin.buffer, buffered_input)
                        notify(stdin.cond)
                    finally
                        unlock(stdin.cond)
                    end
                end
                Base.reseteof(stdin)
                @lock BG begin
                    BG.confirming = :none
                    BG.key_listening = false
                end
                unlock(stdin.raw_lock)
            end
        finally
            @lock BG.task_done notify(BG.task_done)
        end
    else
        nothing
    end

    # Wake up key_task by signaling EOF on stdin so wait_readnb returns
    wake_key_task = () -> begin
        if key_task !== nothing && !istaskdone(key_task)
            lock(stdin.cond)
            try
                stdin.status = Base.StatusEOF
                notify(stdin.cond)
            finally
                unlock(stdin.cond)
            end
        end
    end

    # If waiting for a specific package, spawn a watcher that exits when it's done
    if wait_for_pkg !== nothing
        Threads.@spawn :samepool begin
            @lock BG.pkg_done begin
                # Wait for the package to appear in pending_pkgids (it may not be
                # registered yet if the request was just injected via work_channel
                # and drain_work_channel! hasn't processed it).
                # Also check completed_pkgids in case the package was added and
                # removed before we started watching.
                while get(BG.pending_pkgids, wait_for_pkg, 0) == 0 && wait_for_pkg ∉ BG.completed_pkgids && BG.completed_at === nothing
                    wait(BG.pkg_done)
                end
                # Now wait for it to finish
                while get(BG.pending_pkgids, wait_for_pkg, 0) > 0
                    wait(BG.pkg_done)
                end
            end
            exit_requested[] = true
            @lock BG.task_done notify(BG.task_done)
        end
    else
        nothing
    end

    counted = false
    return try
        if foreground
            @lock BG BG.foreground_monitors += 1
            counted = true
        end
        # Wait for task completion or user action
        @lock BG.task_done begin
            while !exit_requested[] && !cancel_requested[] && !interrupt_requested[]
                BG.completed_at !== nothing && break
                wait(BG.task_done)
            end
        end

        # If user requested cancel, stop the background task
        if cancel_requested[]
            key_task !== nothing && wait(key_task)
            print(io, restore)
            printpkgstyle(io, :Info, "Canceling precompilation...$(clear)", color = Base.info_color())
            # Wait for the task to emit its final report before clearing
            # `BG.monitoring`, which gates that report's output.
            wait(task; throw=false)
            @lock BG BG.monitoring = false
            return
        end

        # If user requested interrupt, wait for background task to finish cleanly
        if interrupt_requested[]
            key_task !== nothing && wait(key_task)
            # Escalate to SIGKILL if background task doesn't finish promptly
            escalation = Timer(5) do _
                broadcast_signal(Base.SIGKILL)
            end
            wait(task; throw=false)
            close(escalation)
            return
        end

        # If we were waiting for a specific package and it finished, clean up silently
        if exit_requested[] && wait_for_pkg !== nothing
            # keep showing the run to a foreground task still waiting on it, but not over the
            # prompt this request returns to
            others = stop_monitoring_unless_waited_on(counted)
            if key_task !== nothing
                wake_key_task()
                wait(key_task)
            end
            others || print(io, restore)
            return
        end

        # If user requested exit, clean up and return
        if exit_requested[]
            @lock BG BG.monitoring = false
            key_task !== nothing && wait(key_task)
            print(io, restore)
            n_pending = @lock BG length(BG.pending_pkgids)
            progress = n_pending > 0 ? " ($n_pending packages remaining)." : "."
            printpkgstyle(io, :Precompiling, "detached$(progress) Precompilation will continue in the background. Monitor with `precompile --monitor`.$(clear)", color = Base.info_color())
            return
        end

        # Normal completion - signal key_task to exit and wait
        if key_task !== nothing
            wake_key_task()
            wait(key_task)
        end

        wait(task; throw=false)
    catch
        # Clean up on error
        stop_monitoring_unless_waited_on(counted)
        if key_task !== nothing
            exit_requested[] = true
            wake_key_task()
            try; wait(key_task); catch; end
        end
        rethrow()
    finally
        counted && @lock BG BG.foreground_monitors -= 1
    end
end

```
-/
/- One iteration of the key listener's `while true` loop: `false` for `break`. `c` is read as the
bytes of one `Char`. -/
def key_iter (o : Ops m T) (io : T.IOC) (detachable : Bool) (exit_requested cancel_requested interrupt_requested : T.BRef) :
    m Bool := do
  let completed ← lock_BG o do return (← o.bgget).completed_at.isSome
  if completed then return false
  if ← anyRequested o exit_requested cancel_requested interrupt_requested then return false
  o.stdinWaitReadnb (ji 1)
  let completed ← lock_BG o do return (← o.bgget).completed_at.isSome
  if completed then return false
  if ← anyRequested o exit_requested cancel_requested interrupt_requested then return false
  if !((← o.stdinBytesavailable).val > 0) then return true
  let c ← o.stdinReadChar
  -- If waiting for confirmation, Enter confirms, anything else aborts
  let confirmed_action ← lock_BG o do
    let prev := (← o.bgget).confirming
    o.bgmodify fun bg => { bg with confirming := lit "none" }
    return if prev != lit "none" && (c == lit "\r" || c == lit "\n") then prev else lit "none"
  if confirmed_action == lit "cancel" then
    o.bset cancel_requested true
    lock_BG o (o.bgmodify fun bg => { bg with cancel_requested := true })
    broadcast_signal_Integer o 9 -- `Base.SIGKILL`
    return false
  else if confirmed_action == lit "info" then
    lock_BG o (o.bgmodify fun bg => { bg with info_requested := true })
    -- `Base.SIGINFO` is 29; `Base.SIGUSR1` is 10 off Apple platforms
    broadcast_signal_Integer o (if o.isapple then 29 else 10)
    return true
  if c == lit "c" || c == lit "C" then
    lock_BG o do
      o.bgmodify fun bg => { bg with confirming := lit "cancel" }
      let t ← o.time
      o.bgmodify fun bg => { bg with confirm_deadline := add_float t (fl 0x4014000000000000) }
  else if detachable && (c == lit "d" || c == lit "D" || c == lit "q" || c == lit "Q" || c == lit "]") then
    o.bset exit_requested true
    return false
  else if c == lit "\x03" then -- Ctrl-C
    o.bset interrupt_requested true
    println o (o.ctx io) [] -- newline after keypress
    lock_BG o (o.bgmodify fun bg => { bg with interrupt_requested := true })
    broadcast_signal_Integer o 2 -- `Base.SIGINT`
    return false
  else if c == lit "i" || c == lit "I" then
    lock_BG o do
      o.bgmodify fun bg => { bg with confirming := lit "info" }
      let t ← o.time
      o.bgmodify fun bg => { bg with confirm_deadline := add_float t (fl 0x4014000000000000) }
  else if c == lit "v" || c == lit "V" then
    lock_BG o (o.bgmodify fun bg => { bg with verbose := !bg.verbose })
  else if c == lit "?" || c == lit "h" || c == lit "H" then
    let io' := o.ctx io
    o.lockIO io' do
      println o io' (lit "  Keyboard shortcuts:" ++ ansi_cleartoendofline)
      println o io' (lit "    c       Cancel precompilation via killing subprocesses (press Enter to confirm)" ++ ansi_cleartoendofline)
      if detachable then
        println o io' (lit "    d/q/]   Detach (precompilation continues in background)" ++ ansi_cleartoendofline)
      println o io' (lit "    i       Send profiling signal to subprocesses (press Enter to confirm)" ++ ansi_cleartoendofline)
      let fields := if o.iswindows then "elapsed time and PID" else "elapsed time, PID, CPU% and memory"
      println o io' (lit "    v       Toggle verbose mode (show " ++ lit fields ++ lit " for each worker)" ++ ansi_cleartoendofline)
      println o io' (lit "    Ctrl-C  Interrupt (sends SIGINT, shows output)" ++ ansi_cleartoendofline)
      println o io' (lit "    ?/h     Show this help" ++ ansi_cleartoendofline)
  return true

/-- The key listener's `while true` loop. -/
def key_loop [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T) (io : T.IOC) (detachable : Bool)
    (exit_requested cancel_requested interrupt_requested : T.BRef) : m Unit := do
  let again ← key_iter o io detachable exit_requested cancel_requested interrupt_requested
  if again then key_loop o io detachable exit_requested cancel_requested interrupt_requested else pure ()
partial_fixpoint

/-- `while bytesavailable(stdin) > 0; push!(buffered_input, read(stdin, UInt8)); end`. -/
def drain_stdin [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T) (buffered_input : T.U8Vec) :
    m Unit := do
  let n ← o.stdinBytesavailable
  if n.val > 0 then
    o.u8Push buffered_input (← o.stdinReadByte)
    drain_stdin o buffered_input
  else pure ()
partial_fixpoint

/-- The key-listener task of `_monitor_background_precompile`. -/
def key_listener [MonadFinally m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T) (io : T.IOC)
    (detachable : Bool) (exit_requested cancel_requested interrupt_requested : T.BRef) : m Unit :=
  tryFinally (do
      if !(← o.stdinTrylockRaw) then return
      lock_BG o do
        o.bgmodify fun bg => { bg with detachable := detachable }
        o.bgmodify fun bg => { bg with confirming := lit "none" }
        o.bgmodify fun bg => { bg with key_listening := true }
      let buffered_input ← o.newU8Vec
      let inner ← catchE (do
        let term ← o.ttyTerminal ((← o.getENV (lit "TERM")).getD (lit "dumb"))
        o.rawMode term true
        -- Drain any pre-existing input (e.g. pasted or pre-typed text)
        -- before entering the key listener. This avoids accidentally
        -- triggering menu actions from stale input (see #61520).
        -- The drained bytes are replayed into stdin on exit.
        -- We must start_reading + yield first so libuv delivers any
        -- bytes sitting in the kernel tty buffer into stdin.buffer.
        o.stdinStartReading
        o.yieldTask
        drain_stdin o buffered_input
        tryFinally (key_loop o io detachable exit_requested cancel_requested interrupt_requested)
          (o.rawMode term false))
      -- `catch err`
      let after ← match inner with
        | .ok () => pure (Except.ok false)
        | .error .eofError => pure (.ok true) -- `return`
        | .error err => do
          o.bset exit_requested true
          pure (.error err)
      -- `finally`: replay any buffered input back into stdin so the REPL
      -- (or whatever reads stdin next) sees it as typed text.
      let buffered ← o.u8Get buffered_input
      if !buffered.isEmpty then
        o.stdinLockCond
        tryFinally (do
            o.stdinBufferWrite buffered
            o.stdinNotifyCond)
          o.stdinUnlockCond
      o.stdinReseteof
      lock_BG o do
        o.bgmodify fun bg => { bg with confirming := lit "none" }
        o.bgmodify fun bg => { bg with key_listening := false }
      o.stdinUnlockRaw
      match after with
      | .error e => throwThe PError e
      | .ok _ => return)
    (do o.condLock (← o.bgget).task_done (do o.condNotify (← o.bgget).task_done))

/-- The `wake_key_task` closure: signals EOF on stdin so `wait_readnb` returns. -/
def wake_key_task [MonadFinally m] (o : Ops m T) (key_task : Option T.Tsk) : m Unit := do
  if let some kt := key_task then
    if !(← o.istaskdone kt) then
      o.stdinLockCond
      tryFinally (do
          o.stdinSetStatusEOF
          o.stdinNotifyCond)
        o.stdinUnlockCond

/-- The first `while` of the package watcher. -/
def watch_appear [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T) (pkg : PkgId) : m Unit := do
  let bg ← o.bgget
  if (getD o.D bg.pending_pkgids pkg (ji 0)).val == 0 && !setIn o.D bg.completed_pkgids pkg && bg.completed_at.isNone then
    o.condWait bg.pkg_done
    watch_appear o pkg
  else pure ()
partial_fixpoint

/-- The second `while` of the package watcher. -/
def watch_finish [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T) (pkg : PkgId) : m Unit := do
  let bg ← o.bgget
  if (getD o.D bg.pending_pkgids pkg (ji 0)).val > 0 then
    o.condWait bg.pkg_done
    watch_finish o pkg
  else pure ()
partial_fixpoint

/-- The `while` waiting on `BG.task_done` for completion or a user action. -/
def wait_task_done [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T)
    (exit_requested cancel_requested interrupt_requested : T.BRef) : m Unit := do
  if ← anyRequested o exit_requested cancel_requested interrupt_requested then return ()
  let bg ← o.bgget
  if bg.completed_at.isSome then return ()
  o.condWait bg.task_done
  wait_task_done o exit_requested cancel_requested interrupt_requested
partial_fixpoint

/-- The body of the monitor's `try` block after `counted` is set. -/
def monitor_main [MonadFinally m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T) (io : T.IOC)
    (wait_for_pkg : Option PkgId) (task : T.Tsk) (key_task : Option T.Tsk) (clear restore : Bytes) (counted : Bool)
    (exit_requested cancel_requested interrupt_requested : T.BRef) : m Unit := do
  -- Wait for task completion or user action
  o.condLock (← o.bgget).task_done (wait_task_done o exit_requested cancel_requested interrupt_requested)
  -- If user requested cancel, stop the background task
  if ← o.bget cancel_requested then
    if let some kt := key_task then o.waitTask kt
    o.print (o.ctx io) restore
    pps o (o.ctx io) "Info" (lit "Canceling precompilation..." ++ clear) (← o.info_color)
    -- Wait for the task to emit its final report before clearing
    -- `BG.monitoring`, which gates that report's output.
    o.waitTaskNoThrow task
    lock_BG o (o.bgmodify fun bg => { bg with monitoring := false })
    return
  -- If user requested interrupt, wait for background task to finish cleanly
  if ← o.bget interrupt_requested then
    if let some kt := key_task then o.waitTask kt
    -- Escalate to SIGKILL if background task doesn't finish promptly
    let escalation ← o.newTimerOnce (fl 0x4014000000000000) (broadcast_signal_Integer o 9)
    o.waitTaskNoThrow task
    o.closeTimer escalation
    return
  -- If we were waiting for a specific package and it finished, clean up silently
  if (← o.bget exit_requested) && wait_for_pkg.isSome then
    -- keep showing the run to a foreground task still waiting on it, but not over the
    -- prompt this request returns to
    let others ← stop_monitoring_unless_waited_on o counted
    if let some kt := key_task then
      wake_key_task o key_task
      o.waitTask kt
    if !others then o.print (o.ctx io) restore
    return
  -- If user requested exit, clean up and return
  if ← o.bget exit_requested then
    lock_BG o (o.bgmodify fun bg => { bg with monitoring := false })
    if let some kt := key_task then o.waitTask kt
    o.print (o.ctx io) restore
    let n_pending ← lock_BG o do return (o.D.keys (← o.bgget).pending_pkgids).length
    let progress := if n_pending > 0 then lit " (" ++ istr (ji n_pending) ++ lit " packages remaining)." else lit "."
    pps o (o.ctx io) "Precompiling" (lit "detached" ++ progress ++
      lit " Precompilation will continue in the background. Monitor with `precompile --monitor`." ++ clear) (← o.info_color)
    return
  -- Normal completion - signal key_task to exit and wait
  if let some kt := key_task then
    wake_key_task o key_task
    o.waitTask kt
  o.waitTaskNoThrow task

/-- `_monitor_background_precompile(io, detachable, wait_for_pkg; key_controls)`. -/
def _monitor_background_precompile [MonadFinally m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (o : Ops m T) (io : T.IOC) (detachable : Bool) (wait_for_pkg : Option PkgId) (key_controls : Option Bool) :
    m Unit := do
  -- By default only enable key controls when this task is the foreground task (see #61563, #61698).
  -- Falls back to roottask when no foreground task is registered (e.g. non-REPL interactive scripts).
  let foreground ← o.isForegroundTask
  let key_controls := key_controls.getD foreground
  let (completed_at, task) ← lock_BG o do
    let bg ← o.bgget
    return (bg.completed_at, bg.task)
  let finished ← match task with
    | none => pure true
    | some t => o.istaskdone t
  if finished then
    match completed_at with
    | some completed_at =>
      let elapsed := sub_float (← o.time) completed_at
      let time_str ← if lt_float elapsed (fl 0x404E000000000000) then do
          pure (istr (← o.roundInt elapsed) ++ lit " seconds ago")
        else if lt_float elapsed (fl 0x40AC200000000000) then do
          pure (istr (← o.roundInt (div_float elapsed (fl 0x404E000000000000))) ++ lit " minutes ago")
        else if lt_float elapsed (fl 0x40F5180000000000) then do
          pure (istr (← o.roundInt (div_float elapsed (fl 0x40AC200000000000))) ++ lit " hours ago")
        else do
          pure (istr (← o.roundInt (div_float elapsed (fl 0x40F5180000000000))) ++ lit " days ago")
      pps o (o.ctx io) "Info" (lit "Background precompilation completed " ++ time_str) (← o.info_color)
      let result ← lock_BG o do return (← o.bgget).result
      if let some result := result then
        if !result.isEmpty then println o (o.ctx io) (lit "  " ++ result)
    | none =>
      pps o (o.ctx io) "Info" (lit "No background precompilation is running or has been run in this session")
        (← o.info_color)
    return
  let some task := task | return
  let key_controls := key_controls && (← o.stdinIsTTY)
  -- Enable output from do_precompile
  lock_BG o do
    o.bgmodify fun bg => { bg with monitoring := true }
    o.bgmodify fun bg => { bg with key_controls := key_controls }
  -- cursor and clearing codes only mean something to a terminal showing the progress display
  let clear := if ← can_fancyprint_bool o (o.ctx io) then ansi_cleartoend else []
  let restore := if clear.isEmpty then [] else ansi_enablecursor ++ clear
  let exit_requested ← o.newBRef false
  let cancel_requested ← o.newBRef false
  let interrupt_requested ← o.newBRef false
  -- Start a task to listen for keypresses. Skipped if another reader already holds
  -- raw mode on stdin (e.g. runtests.jl's stdin_monitor).
  let key_task ← if key_controls then
      some <$> o.spawn (key_listener o io detachable exit_requested cancel_requested interrupt_requested)
    else pure none
  -- If waiting for a specific package, spawn a watcher that exits when it's done
  if let some pkg := wait_for_pkg then
    discard <| o.spawn do
      o.condLock (← o.bgget).pkg_done do
        -- Wait for the package to appear in pending_pkgids (it may not be
        -- registered yet if the request was just injected via work_channel
        -- and drain_work_channel! hasn't processed it).
        -- Also check completed_pkgids in case the package was added and
        -- removed before we started watching.
        watch_appear o pkg
        -- Now wait for it to finish
        watch_finish o pkg
      o.bset exit_requested true
      o.condLock (← o.bgget).task_done (do o.condNotify (← o.bgget).task_done)
  -- `counted` is set by the first statement of the `try` block
  let r0 ← catchE (do
    if foreground then
      lock_BG o (o.bgmodify fun bg => { bg with foreground_monitors := bg.foreground_monitors + ji 1 })
      pure true
    else pure false)
  let (counted, res) ← match r0 with
    | .error e => pure (false, (Except.error e : Except PError Unit))
    | .ok counted => do
      let r ← catchE (monitor_main o io wait_for_pkg task key_task clear restore counted exit_requested
        cancel_requested interrupt_requested)
      pure (counted, r)
  -- `catch`: clean up on error, then `rethrow()`
  let after ← match res with
    | .ok () => pure (Except.ok ())
    | .error e => catchE (do
      discard (stop_monitoring_unless_waited_on o counted)
      if let some kt := key_task then
        o.bset exit_requested true
        wake_key_task o key_task
        tryCatchThe PError (o.waitTask kt) fun _ => pure ()
      throwThe PError e)
  -- `finally`
  if counted then
    lock_BG o (o.bgmodify fun bg => { bg with foreground_monitors := bg.foreground_monitors - ji 1 })
  match after with
  | .error e => throwThe PError e
  | .ok () => pure ()

/--
Julia source: base/precompilation.jl:1550-1554 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function monitor_background_precompile(io::IO = stderr, detachable::Bool = true, wait_for_pkg::Union{Nothing, PkgId} = nothing;
                                       key_controls::Union{Bool, Nothing} = nothing)
    _monitor_background_precompile(unstable_iocontext(io), detachable, wait_for_pkg; key_controls)
end

```
-/
/- `monitor_background_precompile(io, detachable, wait_for_pkg; key_controls)`; `io` defaults to
`stderr`. -/
def monitor_background_precompile [MonadFinally m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (o : Ops m T) (io : Option T.Stream := none) (detachable : Bool := true) (wait_for_pkg : Option PkgId := none)
    (key_controls : Option Bool := none) : m Unit :=
  _monitor_background_precompile o (unstable_iocontext o.asContext o.wrapIO (io.getD o.stderr)) detachable wait_for_pkg
    key_controls

/--
Julia source: base/precompilation.jl:1474-1482 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Monitor the precompile progress for `pkg` until that package finishes.
# This should be called after unlocking require_lock.
function wait_for_pending_package(pkg::PkgId)
    is_package_pending(pkg) || return false
    printpkgstyle(stderr, :Info, "$(pkg.name) is currently being precompiled in the background. Waiting for it to finish...", color = Base.info_color())
    monitor_background_precompile(stderr, false, pkg)
    return true
end

```
-/
def wait_for_pending_package [MonadFinally m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T)
    (pkg : PkgId) : m Bool := do
  if !(← is_package_pending o pkg) then return false
  pps o o.stderr "Info" (pkg.name ++ lit " is currently being precompiled in the background. Waiting for it to finish...")
    (← o.info_color)
  monitor_background_precompile o (some o.stderr) false (some pkg)
  return true

/--
Julia source: base/precompilation.jl:1860-1963 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function launch_background_precompile(pkgs::Union{Vector{String}, Vector{PkgId}},
                                       internal_call::Bool,
                                       strict::Bool,
                                       warn_loaded::Bool,
                                       timing::Bool,
                                       verbose::Bool,
                                       _from_loading::Bool,
                                       _reasons::Dict{Symbol,Int},
                                       configs::Vector{Config},
                                       io::IOContext,
                                       fancyprint::Bool,
                                       manifest::Bool,
                                       ignore_loaded::Bool,
                                       detachable::Bool,
                                       skip_dependents::Bool,
                                       force::Bool,
                                       force_stdlibs::Bool)
    # Stop any existing background precompilation
    @lock BG begin
        if BG.task !== nothing && !istaskdone(BG.task)
            BG.interrupt_requested = true
            @lock BG.task_done notify(BG.task_done)
        end
    end

    # Wait for previous task to complete
    old_task = @lock BG BG.task
    if old_task !== nothing
        wait(old_task)
    end

    @lock BG begin
        BG.interrupt_requested = false
        BG.cancel_requested = false
        BG.info_requested = false
        BG.verbose = verbose
        empty!(BG.signal_channels)
        BG.monitoring = true
        BG.key_controls = false
        BG.completed_at = nothing
        BG.result = nothing
        BG.return_value = nothing
        BG.exception = nothing
        empty!(BG.pending_pkgids)
        empty!(BG.completed_pkgids)
        BG.work_channel = Channel{PrecompileRequest}(Inf)
    end

    # Register an atexit hook (once) to cleanly shut down background precompilation
    # before the event loop is torn down.
    register_atexit_hook()

    # Launch new background precompilation
    @lock BG begin
        wc = BG.work_channel
        BG.task = Threads.@spawn :samepool begin
            try
                # pass the ids through: an extension has no name resolvable from `Main`
                ret = do_precompile(pkgs, internal_call, strict, warn_loaded, timing, _from_loading, _reasons,
                                    configs, io, fancyprint, manifest, ignore_loaded, detachable,
                                    skip_dependents, force, force_stdlibs, wc)

                @lock BG begin
                    BG.return_value = ret
                end
            catch e
                @lock BG begin
                    if BG.interrupt_requested || BG.cancel_requested
                        BG.result = "Background precompilation was interrupted"
                        # loading must stop rather than compile the package again serially
                        _from_loading && (BG.exception = e)
                    else
                        BG.exception = e
                        BG.result = "Background precompilation failed: $(sprint(showerror, e))"
                    end
                end
            finally
                close(wc)
                # Drain pending requests with error
                while isready(wc)
                    req = try; take!(wc); catch; break; end
                    try; put!(req.result, InterruptException()); catch; end
                end
                @lock BG begin
                    BG.task = nothing
                    BG.interrupt_requested = false
                    BG.cancel_requested = false
                    BG.info_requested = false
                    foreach(close, BG.signal_channels)
                    empty!(BG.signal_channels)
                    @lock BG.pkg_done begin
                        empty!(BG.pending_pkgids)
                        notify(BG.pkg_done)
                    end
                    BG.monitoring = false
                    BG.completed_at = time()
                    @lock BG.task_done notify(BG.task_done)
                end
            end
        end
    end

    return nothing
end
```
-/
/- The `while isready(wc)` loop of the background task's `finally`. -/
def fail_queued_requests [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T) (wc : T.ReqChan) : m Unit := do
  let ready ← o.reqIsready wc
  if ready then
    let req ← catchE (o.reqTake wc)
    match req with
    | .error _ => pure ()
    | .ok req =>
      tryCatchThe PError (o.resPut req.result (.exc .interruptException)) fun _ => pure ()
      fail_queued_requests o wc
  else pure ()
partial_fixpoint

/-- `launch_background_precompile(...)`. -/
def launch_background_precompile [MonadFinally m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T)
    (pkgs : Pkgs) (internal_call strict warn_loaded timing verbose _from_loading : Bool) (_reasons : T.Dict Bytes JInt64)
    (configs : List (Config T)) (io : T.IOC) (fancyprint manifest ignore_loaded detachable skip_dependents force
      force_stdlibs : Bool) : m Unit := do
  -- Stop any existing background precompilation
  lock_BG o do
    if let some t := (← o.bgget).task then
      if !(← o.istaskdone t) then
        o.bgmodify fun bg => { bg with interrupt_requested := true }
        o.condLock (← o.bgget).task_done (do o.condNotify (← o.bgget).task_done)
  -- Wait for previous task to complete
  let old_task ← lock_BG o do return (← o.bgget).task
  if let some t := old_task then o.waitTask t
  lock_BG o do
    o.bgmodify fun bg =>
      { bg with interrupt_requested := false, cancel_requested := false, info_requested := false, verbose := verbose,
                signal_channels := [], monitoring := true, key_controls := false, completed_at := none, result := none,
                return_value := none, exception := none }
    o.bgmodify fun bg => { bg with pending_pkgids := o.D.empty, completed_pkgids := o.D.empty }
    let wc ← o.newReqChannel
    o.bgmodify fun bg => { bg with work_channel := wc }
  -- Register an atexit hook (once) to cleanly shut down background precompilation
  -- before the event loop is torn down.
  register_atexit_hook o
  -- Launch new background precompilation
  lock_BG o do
    let wc := (← o.bgget).work_channel
    let body : m Unit := do
      let r ← catchE (do
        -- pass the ids through: an extension has no name resolvable from `Main`
        let ret ← do_precompile o pkgs internal_call strict warn_loaded timing _from_loading _reasons configs io
          fancyprint manifest ignore_loaded detachable skip_dependents force force_stdlibs wc
        lock_BG o (o.bgmodify fun bg => { bg with return_value := ret }))
      let after ← match r with
        | .ok () => pure (Except.ok ())
        | .error e => catchE (lock_BG o do
          let bg ← o.bgget
          if bg.interrupt_requested || bg.cancel_requested then
            o.bgmodify fun bg => { bg with result := some (lit "Background precompilation was interrupted") }
            -- loading must stop rather than compile the package again serially
            if _from_loading then o.bgmodify fun bg => { bg with exception := some e }
          else
            o.bgmodify fun bg => { bg with exception := some e }
            let msg ← o.showerror e
            o.bgmodify fun bg => { bg with result := some (lit "Background precompilation failed: " ++ msg) })
      -- `finally`
      o.reqClose wc
      -- Drain pending requests with error
      fail_queued_requests o wc
      lock_BG o do
        o.bgmodify fun bg =>
          { bg with task := none, interrupt_requested := false, cancel_requested := false, info_requested := false }
        for ch in (← o.bgget).signal_channels do o.sigClose ch
        o.bgmodify fun bg => { bg with signal_channels := [] }
        o.condLock (← o.bgget).pkg_done do
          o.bgmodify fun bg => { bg with pending_pkgids := o.D.empty }
          o.condNotify (← o.bgget).pkg_done
        o.bgmodify fun bg => { bg with monitoring := false }
        let t ← o.time
        o.bgmodify fun bg => { bg with completed_at := some t }
        o.condLock (← o.bgget).task_done (do o.condNotify (← o.bgget).task_done)
      match after with
      | .error e => throwThe PError e
      | .ok () => pure ()
    let t ← o.spawn body
    o.bgmodify fun bg => { bg with task := some t }
  return ()

/--
Julia source: base/precompilation.jl:1973-2064 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _precompilepkgs(pkgs::Union{Vector{String}, Vector{PkgId}},
                         internal_call::Bool,
                         strict::Bool,
                         warn_loaded::Bool,
                         timing::Bool,
                         verbose::Bool,
                         _from_loading::Bool,
                         _reasons::Dict{Symbol,Int},
                         configs::Vector{Config},
                         io::IOContext,
                         fancyprint′::Bool,
                         manifest::Bool,
                         ignore_loaded::Bool,
                         detachable::Bool,
                         skip_dependents::Bool,
                         force::Bool,
                         force_stdlibs::Bool)
    # Try to inject into a running background task, else launch a new one, under
    # launch_lock so concurrent callers cannot spawn competing background tasks.
    local req = nothing
    live_display = false
    injected = @lock launch_lock begin
        did_inject = @lock BG begin
            if BG.task !== nothing && !istaskdone(BG.task) &&
                    isopen(BG.work_channel)
                req = PrecompileRequest(copy(pkgs), internal_call, strict, warn_loaded, timing, _from_loading, _reasons,
                                        configs, io, fancyprint′, manifest, ignore_loaded, detachable,
                                        skip_dependents, force, force_stdlibs, Channel{Any}(1))
                try
                    # Enable verbose before enqueueing, and only ever turn it on so a
                    # non-verbose merge doesn't disable an already-verbose run.
                    verbose && (BG.verbose = true)
                    put!(BG.work_channel, req)
                    # verbose output prints lines rather than a live display
                    live_display = BG.monitoring && !BG.verbose
                    true
                catch
                    req = nothing
                    false
                end
            else
                false
            end
        end
        if !did_inject
            launch_background_precompile(pkgs, internal_call, strict, warn_loaded, timing, verbose, _from_loading, _reasons,
                                         configs, io, fancyprint′, manifest, ignore_loaded, detachable,
                                         skip_dependents, force, force_stdlibs)
        end
        did_inject
    end
    # a live progress display already shows the merged packages, and a line printed into it
    # from here would be overwritten
    if injected && !(can_fancyprint(io) && live_display)
        printpkgstyle(io, :Precompiling, "Merging precompilation request into existing run...", color = Base.info_color())
    end

    if req !== nothing
        # Injected into existing task — monitor until our package finishes, then read result
        wait_for_pkg = if _from_loading && length(pkgs) == 1
            pkgs[1] isa PkgId ? pkgs[1] : Base.identify_package(pkgs[1])
        else
            nothing
        end
        monitor_background_precompile(io, detachable, wait_for_pkg)
        if _from_loading
            # _from_loading: package just left pending_pkgids, waiter will put result shortly
            result = take!(req.result)
            result isa Exception && throw(result)
            return result
        end
        # Interactive: if result is ready (task completed), use it; if detached, return nothing
        if isready(req.result)
            result = take!(req.result)
            result isa Exception && throw(result)
            return result
        end
        return nothing
    end

    # Launched new task — wait for full completion
    monitor_background_precompile(io, detachable)

    local ret_val, ret_ex
    @lock BG begin
        ret_val = BG.return_value
        ret_ex = BG.exception
    end
    ret_ex !== nothing && throw(ret_ex)
    return ret_val
end

```
-/
/- `_precompilepkgs(...)`: the result paths, or `nothing` (`none`). -/
def _precompilepkgs [MonadFinally m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T)
    (pkgs : Pkgs) (internal_call strict warn_loaded timing verbose _from_loading : Bool) (_reasons : T.Dict Bytes JInt64)
    (configs : List (Config T)) (io : T.IOC) (fancyprint' manifest ignore_loaded detachable skip_dependents force
      force_stdlibs : Bool) : m (Option (List Bytes)) := do
  -- Try to inject into a running background task, else launch a new one, under
  -- launch_lock so concurrent callers cannot spawn competing background tasks.
  let (injected, req, live_display) ← o.withLock o.launch_lock do
    let (did_inject, req, live_display) ← lock_BG o do
      let bg ← o.bgget
      let running ← match bg.task with
        | none => pure false
        | some t => do
          if ← o.istaskdone t then pure false else o.reqIsopen bg.work_channel
      if running then
        let req : PrecompileRequest T := ⟨pkgs, internal_call, strict, warn_loaded, timing, _from_loading, _reasons,
          configs, io, fancyprint', manifest, ignore_loaded, detachable, skip_dependents, force, force_stdlibs,
          ← o.newResChannel⟩
        let r ← catchE (do
          -- Enable verbose before enqueueing, and only ever turn it on so a
          -- non-verbose merge doesn't disable an already-verbose run.
          if verbose then o.bgmodify fun bg => { bg with verbose := true }
          o.reqPut (← o.bgget).work_channel req
          -- verbose output prints lines rather than a live display
          let bg ← o.bgget
          return bg.monitoring && !bg.verbose)
        match r with
        | .ok live_display => pure (true, some req, live_display)
        | .error _ => pure (false, none, false)
      else pure (false, none, false)
    if !did_inject then
      launch_background_precompile o pkgs internal_call strict warn_loaded timing verbose _from_loading _reasons
        configs io fancyprint' manifest ignore_loaded detachable skip_dependents force force_stdlibs
    return (did_inject, req, live_display)
  -- a live progress display already shows the merged packages, and a line printed into it
  -- from here would be overwritten
  if injected then
    let shown ← do
      if ← can_fancyprint_bool o (o.ctx io) then pure live_display else pure false
    if !shown then
      pps o (o.ctx io) "Precompiling" (lit "Merging precompilation request into existing run...") (← o.info_color)
  match req with
  | some req =>
    -- Injected into existing task — monitor until our package finishes, then read result
    let wait_for_pkg ← if _from_loading && pkgs.length == 1 then
        match pkgs with
        | .ids (p :: _) => pure (some p)
        | .names (n :: _) => o.identify_package n
        | _ => pure none
      else pure none
    monitor_background_precompile o (some (o.ctx io)) detachable wait_for_pkg
    if _from_loading then
      -- _from_loading: package just left pending_pkgids, waiter will put result shortly
      match ← o.resTake req.result with
      | .exc e => throwThe PError e
      | .paths ps => return some ps
    -- Interactive: if result is ready (task completed), use it; if detached, return nothing
    if ← o.resIsready req.result then
      match ← o.resTake req.result with
      | .exc e => throwThe PError e
      | .paths ps => return some ps
    return none
  | none =>
    -- Launched new task — wait for full completion
    monitor_background_precompile o (some (o.ctx io)) detachable
    let (ret_val, ret_ex) ← lock_BG o do
      let bg ← o.bgget
      return (bg.return_value, bg.exception)
    if let some e := ret_ex then throwThe PError e
    return ret_val

/--
Julia source: base/precompilation.jl:1206-1369 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
## Public API

"""
    precompilepkgs(pkgs; kwargs...)

Precompile packages and their dependencies, with support for parallel compilation,
progress tracking, and various compilation configurations.

`pkgs::Union{Vector{String}, Vector{PkgId}}`: Packages to precompile. When
empty (default), precompiles all project dependencies. When specified,
precompiles only the given packages and their dependencies (unless
`manifest=true`).

!!! note
    Errors will only throw when precompiling the top-level dependencies, given that
    not all manifest dependencies may be loaded by the top-level dependencies on the given system.
    This can be overridden to make errors in all dependencies throw by setting the kwarg `strict` to `true`

# Keyword Arguments
- `internal_call::Bool`: Indicates this is an automatic precompilation call
  from somewhere external (e.g. Pkg). Do not use this parameter.

- `strict::Bool`: Controls error reporting scope. When `false` (default), only reports
  errors for direct project dependencies. Only relevant when `manifest=true`.

- `warn_loaded::Bool`: When `true` (default), checks for and warns about packages that are
  precompiled but already loaded with a different version. Displays a warning that Julia
  needs to be restarted to use the newly precompiled versions.

- `timing::Bool`: When `true` (not default), displays timing information for
  each package compilation, but only if compilation might have succeeded.
  Disables fancy progress bar output (timing is shown in simple text mode).

- `verbose::Bool`: When `true` (not default), enables verbose timing mode: implies
  `timing=true` and appends a per-package breakdown to each completion line with
  these columns:
    * `total`   — total wall-clock time for the worker subprocess.
    * `include` — time spent in `Base.include` of the package source.
    * `(deps)`  — subset of `include`: time spent loading already-precompiled
                  dependencies from disk (via `require`).
    * `(comp)`  — subset of `include`: cumulative compile time (type inference
                  and code generation) reported by `cumulative_compile_time_ns`.
    * `methods` — number of newly-inferred methods cached for this package.
    * `img-gen` — `total - include`: post-include work (native-code generation,
                  serialization, writing the `.ji` and pkgimage to disk).
    * `cache`   — combined on-disk size of the `.ji` cache and any pkgimage.
    * `~pk-rss` — approximate peak resident set size of the worker subprocess.
                  The leading `~` indicates the value is sampled (every ~0.5 s)
                  rather than observed continuously, so transient peaks between
                  samples may be missed. Linux/macOS only, `-` elsewhere.
  Values under 5 ms and zero counts are dimmed for readability.

- `_from_loading::Bool`: Internal flag indicating the call originated from the
  package loading system. When `true` (not default): returns early instead of
  throwing when packages are not found; suppresses progress messages when not
  in an interactive session; allows packages outside the current environment to
  be added as serial precompilation jobs; skips LOADING_CACHE initialization;
  and changes cachefile locking behavior.

- `_reasons::Dict{Symbol,Int}`: Internal, with `_from_loading`: why the loader rejected
  the requested packages' caches (see `Base.list_reasons`). The reasons a user can act
  on are explained at the start of the session.

- `configs::Union{Config,Vector{Config}}`: Compilation configurations to use. Each Config
  is a `Pair{Cmd, Base.CacheFlags}` specifying command flags and cache flags. When
  multiple configs are provided, each package is precompiled for each configuration.

- `io::IO`: Output stream for progress messages, warnings, and errors. Can be
  redirected (e.g., to `devnull` when called from loading in non-interactive mode).

- `fancyprint::Bool`: Controls output format. When `true`, displays an animated progress
  bar with spinners. When `false`, instead enables `timing` mode. Automatically
  disabled when `timing=true` or when called from loading in non-interactive mode.

- `manifest::Bool`: Controls the scope of packages to precompile. When `false` (default),
  precompiles only packages specified in `pkgs` and their dependencies. When `true`,
  precompiles all packages in the manifest (workspace mode), typically used by Pkg for
  workspace precompile requests.

- `ignore_loaded::Bool`: Controls whether already-loaded packages affect cache
  freshness checks. When `false` (not default), loaded package versions are considered when
  determining if cache files are fresh.

- `detachable::Bool`: When `true` (not default), allows detaching from the
  precompilation monitor with the `d` key, letting precompilation continue in
  the background. The monitor can be reattached later via
  [`Base.Precompilation.monitor_background_precompile`](@ref). Pkg.jl passes
  `detachable=true` in interactive sessions.

- `skip_dependents::Bool`: When `true` (default), packages that depend on a package
  which failed to precompile are not attempted, since loading the failed dependency
  would fail again. Set to `false` to attempt them anyway, for example when a package
  only loads that dependency on some platforms. Extensions always load their parent
  and triggers, so they are never attempted when one of those failed, regardless of
  this setting.

- `force::Bool`: When `true` (not default), recompiles packages whose cache files are
  already fresh. Standard libraries are left alone.

# Keyboard Controls

When running interactively in a TTY, the following keys are available during
precompilation:

  - **`c`** — Cancel precompilation. Prompts for Enter to confirm; ignored after
    5 seconds or if any other key is pressed.
  - **`d`/`q`/`]`** — Detach (only when `detachable=true`). Returns to the REPL while
    precompilation continues in the background.
  - **`i`** — Info. Sends a profiling signal (SIGINFO on macOS/BSD, SIGUSR1 on
    Linux) to subprocesses, triggering a profile peek without interrupting
    compilation. Prompts for Enter to confirm; ignored after 5 seconds or if any
    other key is pressed.
  - **`v`** — Toggle verbose mode. Shows elapsed time and worker PID for each actively
    compiling package, plus CPU% and memory (RSS) on Linux and macOS.
  - **`?`/`h`** — Show keyboard shortcut help.
  - **Ctrl-C** — Interrupt. Sends SIGINT to subprocesses and displays their output.

# Return
- `Vector{String}`: Paths to cache files for the requested packages.
- `Nothing`: precompilation should be skipped

# Notes
- Packages in circular dependency cycles are skipped with a warning.
- Packages with `__precompile__(false)` are skipped if they are from loading to
  avoid repeated work on every session.
- Parallel compilation is controlled by `JULIA_NUM_PRECOMPILE_TASKS` environment variable
  (defaults to EFFECTIVE_CPU_THREADS + 1, capped at 16, halved on Windows). The total CPU-thread
  budget shared across those workers (worker baselines plus native-image codegen threads)
  is controlled by `JULIA_PRECOMPILE_THREADS` (defaults to EFFECTIVE_CPU_THREADS + 1).
- Extensions are precompiled when all their triggers are available in the environment.
"""
function precompilepkgs(pkgs::Union{Vector{String}, Vector{PkgId}}=String[];
                        internal_call::Bool=false,
                        strict::Bool = false,
                        warn_loaded::Bool = true,
                        timing::Bool = false,
                        verbose::Bool = false,
                        _from_loading::Bool=false,
                        _reasons::Dict{Symbol,Int}=Dict{Symbol,Int}(),
                        configs::Union{Config,Vector{Config}}=(``=>Base.CacheFlags()),
                        io::IO=stderr,
                        # asking for timing disables fancy mode, as timing is shown in non-fancy mode;
                        # verbose implies timing (see below), so also disables fancy mode
                        fancyprint::Bool = can_fancyprint(io) && !timing && !verbose,
                        manifest::Bool=false,
                        ignore_loaded::Bool=true,
                        detachable::Bool=false,
                        skip_dependents::Bool=true,
                        force::Bool=false,
                        # undocumented: `force` for stdlibs too. Warning: their new cache files land in
                        # the user depot rather than the one julia ships them in, and shadow those from then on
                        force_stdlibs::Bool=false)
    # verbose timing mode requires timing to be enabled (per-package breakdown
    # is only shown alongside timing lines in non-fancy mode)
    verbose && (timing = true)
    force_stdlibs && (force = true)
    @debug "precompilepkgs called with" pkgs internal_call strict warn_loaded timing verbose _from_loading configs fancyprint manifest ignore_loaded detachable skip_dependents force force_stdlibs
    # monomorphize this to avoid latency problems
    _precompilepkgs(pkgs, internal_call, strict, warn_loaded, timing, verbose, _from_loading, _reasons,
                   configs isa Vector{Config} ? configs : [configs],
                   unstable_iocontext(io), fancyprint, manifest, ignore_loaded, detachable,
                   skip_dependents, force, force_stdlibs)
end

```
-/
/- `precompilepkgs(pkgs; kwargs...)`. A keyword left `none` takes its default: `_reasons` an empty
dictionary, `configs` the single config `` `` => Base.CacheFlags()``, `io` `stderr`, and `fancyprint`
`can_fancyprint(io) && !timing && !verbose` (evaluated before the body, with the given `timing` and
`verbose`). -/
def precompilepkgs [MonadFinally m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T)
    (pkgs : Pkgs := .names []) (internal_call : Bool := false) (strict : Bool := false) (warn_loaded : Bool := true)
    (timing : Bool := false) (verbose : Bool := false) (_from_loading : Bool := false)
    (_reasons : Option (T.Dict Bytes JInt64) := none) (configs : Option (Config T ⊕ List (Config T)) := none)
    (io : Option T.Stream := none) (fancyprint : Option Bool := none) (manifest : Bool := false)
    (ignore_loaded : Bool := true) (detachable : Bool := false) (skip_dependents : Bool := true) (force : Bool := false)
    (force_stdlibs : Bool := false) : m (Option (List Bytes)) := do
  let _reasons := _reasons.getD o.D.empty
  let configs ← match configs with
    | some c => pure c
    | none => do pure (.inl (o.emptyCmd, ← o.newCacheFlags))
  let io := io.getD o.stderr
  -- asking for timing disables fancy mode, as timing is shown in non-fancy mode;
  -- verbose implies timing (see below), so also disables fancy mode
  let fancyprint ← match fancyprint with
    | some b => pure b
    | none => do pure ((← can_fancyprint_bool o io) && !timing && !verbose)
  -- verbose timing mode requires timing to be enabled (per-package breakdown
  -- is only shown alongside timing lines in non-fancy mode)
  let timing := timing || verbose
  let force := force || force_stdlibs
  o.debugCalled pkgs [(lit "internal_call", internal_call), (lit "strict", strict), (lit "warn_loaded", warn_loaded),
    (lit "timing", timing), (lit "verbose", verbose), (lit "_from_loading", _from_loading)] configs
    [(lit "fancyprint", fancyprint), (lit "manifest", manifest), (lit "ignore_loaded", ignore_loaded),
    (lit "detachable", detachable), (lit "skip_dependents", skip_dependents), (lit "force", force),
    (lit "force_stdlibs", force_stdlibs)]
  -- monomorphize this to avoid latency problems
  _precompilepkgs o pkgs internal_call strict warn_loaded timing verbose _from_loading _reasons
    (match configs with
      | .inl c => [c]
      | .inr cs => cs)
    (unstable_iocontext o.asContext o.wrapIO io) fancyprint manifest ignore_loaded detachable skip_dependents force
    force_stdlibs

/--
Julia source: base/precompilation.jl:1397-1456 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _precompile_for_loading(into::Module, names::Vector{Symbol})
    pkgs = PkgId[]
    for name in names
        pkg = Base.identify_package(into, String(name))
        pkg === nothing && continue
        Base.root_module_exists(pkg) && continue
        pkg in pkgs || push!(pkgs, pkg)
    end
    isempty(pkgs) && return

    # Extensions the statement makes loadable: the parent is reachable from what is
    # being loaded or already loaded, at least one trigger is being loaded, and every
    # trigger is reachable, already loaded, or in the sysimage.
    env = ExplicitEnv()
    reachable = Set{UUID}()
    for pkg in pkgs
        pkg.uuid === nothing && continue
        _collect_reachable!(reachable, env.deps, pkg.uuid)
    end
    loaded = @lock Base.require_lock Set{UUID}(pkg.uuid::UUID for pkg in keys(Base.loaded_modules) if pkg.uuid !== nothing)
    available(uuid::UUID) = uuid in reachable || uuid in loaded ||
        (haskey(env.names, uuid) && Base.in_sysimage(PkgId(uuid, env.names[uuid])))
    ext_parents = Dict{PkgId, PkgId}()
    for uuid in Iterators.flatten((reachable, loaded))
        for (ext_name, trigger_uuids) in get(Dict{String, Vector{UUID}}, env.extensions, uuid)
            all(available, trigger_uuids) || continue
            (uuid in reachable || any(in(reachable), trigger_uuids)) || continue
            ext = PkgId(Base.uuid5(uuid, ext_name), ext_name)
            (Base.root_module_exists(ext) || haskey(ext_parents, ext)) && continue
            push!(pkgs, ext)
            ext_parents[ext] = PkgId(uuid, env.names[uuid])
        end
    end
    # a single package gets no benefit over the session `require` starts itself
    length(pkgs) > 1 || return

    stale = PkgId[]
    reasons = Dict{Symbol,Int}()
    stale_cache = Dict{Base.StaleCacheKey,Bool}()
    cachepath_cache = Dict{PkgId, Vector{String}}()
    for pkg in pkgs
        fresh = try
            Base.compilecache_freshest_path(pkg; ignore_loaded=false, stale_cache, cachepath_cache,
                                            verify_checksums=false, reasons) !== nothing
        catch
            true # e.g. no source located: leave it to `require` to report
        end
        fresh || push!(stale, pkg)
    end
    isempty(stale) && return

    # the driver explains the actionable reasons to the user; this is the full record
    label(pkg) = haskey(ext_parents, pkg) ? Base.pkg_log_name(pkg, ext_parents[pkg]) : Base.pkg_log_name(pkg)
    @debug "Precompiling $(join((label(pkg) for pkg in stale), ", "))$(Base.list_reasons(reasons; full=true))"
    # `@invokelatest` for the same reason as in `Base.__require_prelocked`, see #60223
    @invokelatest precompilepkgs(pkgs; _from_loading=true, ignore_loaded=false,
                                 _reasons=reasons)
    return
end

```
-/
/- `_precompile_for_loading(into, names)`; `names` are the symbols' names. -/
def _precompile_for_loading [MonadFinally m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T)
    (into : T.Mod) (names : List Bytes) : m Unit := do
  let mut pkgs : List PkgId := []
  for name in names do
    let pkg ← o.identify_package_in into name
    let some pkg := pkg | continue
    if ← o.root_module_exists pkg then continue
    if !pkgs.contains pkg then pkgs := pkgs ++ [pkg]
  if pkgs.isEmpty then return
  -- Extensions the statement makes loadable: the parent is reachable from what is
  -- being loaded or already loaded, at least one trigger is being loaded, and every
  -- trigger is reachable, already loaded, or in the sysimage.
  let env ← ExplicitEnv_0 o.D o.any o.env
  let mut reachable : T.Dict UUID Unit := o.D.empty
  for pkg in pkgs do
    let some u := pkg.uuid | continue
    reachable ← _collect_reachable o.D reachable env.deps u
  let loaded ← o.withLock o.require_lock do
    let ks ← o.loadedModuleKeys
    let mut l : T.Dict UUID Unit := o.D.empty
    for pkg in ks do
      if let some u := pkg.uuid then l := setPush o.D l u
    return l
  let reach := reachable
  let available (uuid : UUID) : m Bool := do
    if setIn o.D reach uuid || setIn o.D loaded uuid then return true
    match o.D.get env.names uuid with
    | some name => o.graph.in_sysimage (pkgOf uuid name)
    | none => return false
  let mut ext_parents : T.Dict PkgId PkgId := o.D.empty
  for uuid in o.D.keys reachable ++ o.D.keys loaded do
    let exts := getD o.D env.extensions uuid o.D.empty
    for ext_name in o.D.keys exts do
      let trigger_uuids ← getindex o.D exts ext_name
      if !(← trigger_uuids.allM available) then continue
      if !(setIn o.D reachable uuid || trigger_uuids.any (setIn o.D reachable ·)) then continue
      let ext : PkgId := ⟨some (o.graph.uuid5 uuid ext_name), ext_name⟩
      if (← o.root_module_exists ext) || haskey o.D ext_parents ext then continue
      pkgs := pkgs ++ [ext]
      ext_parents := o.D.set ext_parents ext (pkgOf uuid (← getindex o.D env.names uuid))
  -- a single package gets no benefit over the session `require` starts itself
  if !(pkgs.length > 1) then return
  let mut stale : List PkgId := []
  let mut reasons : T.Dict Bytes JInt64 := o.D.empty
  let mut stale_cache : T.Dict T.SCK Bool := o.D.empty
  let cachepath_cache : T.Dict PkgId (List Bytes) := o.D.empty
  for pkg in pkgs do
    let args : FreshestArgs T :=
      { ignore_loaded := false, stale_cache := stale_cache, cachepath_cache := cachepath_cache,
        verify_checksums := false, reasons := some reasons }
    let r ← catchE (o.compilecache_freshest_path pkg args)
    let fresh ← match r with
      | .error _ => pure true -- e.g. no source located: leave it to `require` to report
      | .ok r => do
        stale_cache := r.stale_cache
        reasons := r.reasons.getD reasons
        match r.result with
        | .ok p => pure p.isSome
        | .error _ => pure true
    if !fresh then stale := stale ++ [pkg]
  if stale.isEmpty then return
  -- the driver explains the actionable reasons to the user; this is the full record
  let ep := ext_parents
  let rs := reasons
  let label (pkg : PkgId) : m Bytes := do
    match o.D.get ep pkg with
    | some parent => o.pkg_log_name2 pkg parent
    | none => o.pkg_log_name pkg
  o.debugLazy (do
    let labels ← stale.mapM label
    return lit "Precompiling " ++ joinB (lit ", ") labels ++ (← o.list_reasons_full rs))
  -- `@invokelatest` for the same reason as in `Base.__require_prelocked`, see #60223
  discard (precompilepkgs o (.ids pkgs) (_from_loading := true) (ignore_loaded := false) (_reasons := some reasons))
  return

/--
Julia source: base/precompilation.jl:1370-1396 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    precompile_for_loading(into::Module, names::Vector{Symbol})

Look-ahead for a `using`/`import` statement that is about to load the packages
`names` into `into`. Precompiles in one parallel session every package of the
statement that is not loaded yet and has no usable cache, together with the
extensions that become loadable once they all are (including extensions whose
other triggers are already loaded). Each subsequent `require` then finds a fresh
cache instead of starting its own session per package, and extensions do not
trail as extra sessions after their triggers load.

Any failure is left for `require` to report: this only does work `require`
would otherwise do itself, one package at a time.
"""
function precompile_for_loading(into::Module, names::Vector{Symbol})
    Base.JLOptions().use_compiled_modules == 1 || return
    Base.generating_output() && return
    Base.disable_parallel_precompile && return
    try
        _precompile_for_loading(into, names)
    catch err
        err isa Union{InterruptException, Base.CancellationRequest} && rethrow()
        @debug "Look-ahead precompilation failed, leaving it to `require`" exception=(err, catch_backtrace())
    end
    return
end

```
-/
/- `precompile_for_loading(into, names)`. -/
def precompile_for_loading [MonadFinally m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : Ops m T)
    (into : T.Mod) (names : List Bytes) : m Unit := do
  if (← o.use_compiled_modules).val != 1 then return
  if ← o.generating_output then return
  if ← o.disable_parallel_precompile then return
  let r ← catchE (_precompile_for_loading o into names)
  match r with
  | .ok () => pure ()
  | .error err =>
    match err with
    | .interruptException | .cancellationRequest => throwThe PError err
    | _ => o.debugLookAhead err
  return

end entry

-- UNTRANSLATED
-- the `end` of `module Precompilation`: no method
-- Source: base/precompilation.jl:3483-3483 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- end
-- /Source

end JuliaLean.base.precompilation

namespace JuliaLean.RuntimeCov.Precompilation

open JuliaLean.RuntimeCov

/-! ## Jobserver and worker limiter, lines 20-158 -/

inductive JobserverSetup where
  | created
  | joined
  | none
  deriving DecidableEq, Repr

/-- `setup_precompile_jobserver!`, base/precompilation.jl:20-28. The Boolean
component records whether the environment entry is present afterwards. -/
def setupPrecompileJobserver (created active : Bool) : JobserverSetup × Bool :=
  if created then (.created, true) else (if active then .joined else .none, false)

/-- `teardown_precompile_jobserver!`, base/precompilation.jl:30-34. -/
def teardownPrecompileJobserver : Bool := false

structure WorkerLimiter where
  max : Int
  jobserver : Bool
  active : Int
  seq : Int
  waiting : List (Float × Int)
  ntokens : Nat
  deriving Repr

/-- `WorkerLimiter(max, jobserver)`, base/precompilation.jl:62-63. -/
def newWorkerLimiter (max : Int) (jobserver : Bool) : WorkerLimiter :=
  ⟨max, jobserver, 0, 0, [], 0⟩

structure BaselineAttempt where
  result : Int
  cancelled : Bool
  timedOut : Bool
  deriving DecidableEq, Repr

/-- `_jobserver_acquire_baseline`, base/precompilation.jl:75-96. Each element
is one loop iteration after the runtime acquire, cancel callback and monotonic
timeout checks. -/
def jobserverAcquireBaseline : List BaselineAttempt → Nat → Bool × Nat
  | [], n => (false, n)
  | a :: rest, n =>
      if a.result = 1 then (true, n + 1)
      else if a.result = -1 || a.cancelled || a.timedOut then (false, n)
      else jobserverAcquireBaseline rest n

/-- `_jobserver_release_baseline`, base/precompilation.jl:98-108. The list
contains successive `@atomicreplace` success results. -/
def jobserverReleaseBaseline : List Bool → Nat → Bool × Nat
  | _, 0 => (false, 0)
  | [], n => (false, n)
  | success :: rest, n =>
      if success then (true, n - 1) else jobserverReleaseBaseline rest n

/-- `_acquire_slot`, base/precompilation.jl:110-122, after its priority wait
has admitted this request. -/
def acquireSlot (w : WorkerLimiter) (priority : Float) : WorkerLimiter :=
  let seq := w.seq + 1
  let key := (priority, -seq)
  { w with active := w.active + 1, seq, waiting := (w.waiting ++ [key]).erase key }

/-- `_release_slot`, base/precompilation.jl:124-130. -/
def releaseSlot (w : WorkerLimiter) : WorkerLimiter := { w with active := w.active - 1 }

/-- `Base.acquire(w::WorkerLimiter)`, base/precompilation.jl:132-143. A
baseline exception releases the process slot before it is rethrown. -/
def acquireWorker (w : WorkerLimiter) (priority : Float)
    (attempts : Rt (List BaselineAttempt)) : Rt Unit × WorkerLimiter :=
  let w := acquireSlot w priority
  if !w.jobserver then (.ok (), w) else
    match attempts with
    | .error e => (.error e, releaseSlot w)
    | .ok xs =>
        let (_, n) := jobserverAcquireBaseline xs w.ntokens
        (.ok (), { w with ntokens := n })

/-- `Base.release(w::WorkerLimiter)`, base/precompilation.jl:145-149. -/
def releaseWorker (w : WorkerLimiter) (cas : List Bool) : WorkerLimiter :=
  let w := if w.jobserver then { w with ntokens := (jobserverReleaseBaseline cas w.ntokens).2 } else w
  releaseSlot w

/-- `Base.acquire(f, w::WorkerLimiter)`, base/precompilation.jl:151-158. The
worker is released after either the callback result or exception. -/
def withWorker {α : Type} (w : WorkerLimiter) (priority : Float)
    (attempts : Rt (List BaselineAttempt)) (cas : List Bool) (f : Rt α) : Rt α × WorkerLimiter :=
  let (acquired, w) := acquireWorker w priority attempts
  match acquired with
  | .error e => (.error e, w)
  | .ok _ => (f, releaseWorker w cas)

/-! ## Per-package job state, lines 183-210 -/

inductive JobStatus where
  | pending | started | recompiled | softError | failed | depFailed
  deriving DecidableEq, Repr

structure PrecompileJob where
  status : JobStatus
  startedAt : Float
  errorMsg : String
  outputBytes : Nat
  pid : Int
  hadPid : Bool
  lockHolder : String
  waitingForBg : Bool
  verboseTiming : String
  peakRssBytes : Nat
  deriving Repr

/-- `PrecompileJob()`, base/precompilation.jl:183. -/
def newPrecompileJob : PrecompileJob :=
  ⟨.pending, 0.0, "", 0, 0, false, "", false, "", 0⟩

/-- Status and state queries, base/precompilation.jl:186-195. -/
def isPending (j : PrecompileJob) : Bool := j.status = .pending
def isStarted (j : PrecompileJob) : Bool := j.status = .started
def isRecompiled (j : PrecompileJob) : Bool := j.status = .recompiled
def isSoftError (j : PrecompileJob) : Bool := j.status = .softError
def isFailed (j : PrecompileJob) : Bool := j.status = .failed
def isDepFailed (j : PrecompileJob) : Bool := j.status = .depFailed
def hasPid (j : PrecompileJob) : Bool := j.pid > 0
def hadPid (j : PrecompileJob) : Bool := j.hadPid
def isLocked (j : PrecompileJob) : Bool := !j.lockHolder.isEmpty
def isWaiting (j : PrecompileJob) : Bool := j.waitingForBg

/-- Mutators at base/precompilation.jl:197-210. -/
def markStarted (j : PrecompileJob) (t : Float) : PrecompileJob :=
  { j with status := .started, startedAt := t }
def markRecompiled (j : PrecompileJob) : PrecompileJob := { j with status := .recompiled }
def markSoftError (j : PrecompileJob) : PrecompileJob := { j with status := .softError }
def markFailed (j : PrecompileJob) (msg : String) : PrecompileJob :=
  { j with status := .failed, errorMsg := msg }
def markDepFailed (j : PrecompileJob) (root : String) : PrecompileJob :=
  { j with status := .depFailed, errorMsg := root }
def setPid (j : PrecompileJob) (pid : Int) : PrecompileJob := { j with pid, hadPid := true }
def clearPid (j : PrecompileJob) : PrecompileJob := { j with pid := 0 }
def clearFailure (j : PrecompileJob) : PrecompileJob :=
  { j with status := .pending, errorMsg := "", outputBytes := 0 }

/-! ## Lock delegates and short formatting helpers, lines 336-486 -/

def lockWith {α : Type} (lock : (Unit → α) → α) (f : Unit → α) : α := lock f
def lockState {α : Type} (lock : Unit → α) : α := lock ()
def unlockState {α : Type} (unlock : Unit → α) : α := unlock ()

/-- `ansi_moveup`, base/precompilation.jl:354. -/
def ansiMoveup (n : Int) : String := "\u001b[" ++ toString n ++ "A"

/-- The three printing methods for `PkgPrecompileError`, lines 359-363. -/
def showerror (msg : String) : String := msg
def showerrorWithBacktrace (msg : String) : String := showerror msg
def showPrecompileError (msg : String) : String := "PkgPrecompileError: " ++ msg

/-- `can_fancyprint`, base/precompilation.jl:365. -/
def canFancyprint (forced : Option Bool) (isTty ciTrue : Bool) : Bool :=
  forced.getD (isTty && !ciTrue)

/-- The three `unstable_iocontext` methods, lines 371-373. -/
inductive IOForm where | concrete | contextConcrete | contextOther deriving DecidableEq, Repr
def unstableIoContext : IOForm → IOForm
  | .contextConcrete => .contextConcrete
  | .contextOther => .contextConcrete
  | .concrete => .contextConcrete

/-- `printpkgstyle`, base/precompilation.jl:375-380, as its emitted text. -/
def printpkgstyle (header msg : String) : String := header ++ " " ++ msg ++ "\n"

/-- `timing_string`, base/precompilation.jl:382. `rounded` is the decimal text
from `round(t, digits=1)`. -/
def timingString (rounded : String) : String := lpad rounded 6 ++ " s"

/-- `format_verbose_timing_header`, base/precompilation.jl:442. -/
def formatVerboseTimingHeader : String :=
  "   total │ include   (deps)   (comp) │ methods  img-gen     cache  ~pk-rss"

/-- `_precompile_cache_bytes`, base/precompilation.jl:446-454. Missing files
and any caught file-system error contribute zero. -/
def precompileCacheBytes (jl : Rt (Option Nat)) (so : Option (Rt (Option Nat))) : Nat :=
  match jl with
  | .error _ => 0
  | .ok j =>
      match so with
      | some (.error _) => j.getD 0
      | some (.ok s) => j.getD 0 + s.getD 0
      | none => j.getD 0

/-- `color_string`, base/precompilation.jl:458-466. -/
def colorString (s enable disable : String) (hascolor : Bool) : String :=
  if hascolor then enable ++ s ++ disable else s

/-- `start_progress`, line 486, and the one-line end/bottom helpers. -/
def startProgress (_io _progress : Nat) : String := "\u001b[?25l"
def endProgress (_io _progress : Nat) : String := "\u001b[?25h\u001b[2K"
def printProgressBottom (_io : Nat) : String := "\u001b[S\u001b[1A\u001b[2K\u001b[1G"

/-! ## Dependency-cycle scan, lines 960-992 -/

abbrev Node := Nat
abbrev Graph := List (Node × List Node)

def depsOf (g : Graph) (n : Node) : List Node :=
  match g.find? (fun p => p.1 = n) with | some p => p.2 | none => []

def lookupMark (marks : List (Node × Bool)) (n : Node) : Option Bool :=
  (marks.find? (fun p => p.1 = n)).map Prod.snd

def setMark (marks : List (Node × Bool)) (n : Node) (b : Bool) : List (Node × Bool) :=
  (n, b) :: marks.filter (fun p => p.1 != n)

def suffixFrom (n : Node) : List Node → List Node
  | [] => []
  | x :: xs => if x = n then x :: xs else suffixFrom n xs

structure ScanState where
  stack : List Node
  marks : List (Node × Bool)
  cycles : List (List Node)
  deriving DecidableEq, Repr

structure ScanFold where
  cycle : Option (List Node)
  early : Bool
  state : ScanState
  deriving DecidableEq, Repr

/-- `scan_deps!`, base/precompilation.jl:967-992. `fuel` bounds recursive graph
walks without changing any terminating finite traversal with enough fuel. -/
def scanDeps : Nat → Graph → Node → ScanState → Bool × ScanState
  | 0, _, pkg, s => (false, { s with marks := setMark s.marks pkg false })
  | fuel + 1, g, pkg, s =>
      let pushed := { s with stack := s.stack ++ [pkg] }
      let folded := (depsOf g pkg).foldl (fun (a : ScanFold) dep =>
        if a.early then a
        else if dep ∈ a.state.stack then
          let found := suffixFrom dep a.state.stack
          let best := match a.cycle with
            | none => some found
            | some old => if found.length < old.length then some found else some old
          { a with cycle := best }
        else
          let (reaches, next) :=
            match lookupMark a.state.marks dep with
            | some b => (b, a.state)
            | none => scanDeps fuel g dep a.state
          if reaches then ⟨a.cycle, true, next⟩ else ⟨a.cycle, false, next⟩)
        (⟨none, false, pushed⟩ : ScanFold)
      let popped := { folded.state with stack := folded.state.stack.dropLast }
      if folded.early then (true, { popped with marks := setMark popped.marks pkg true })
      else match folded.cycle with
        | some c =>
            let marked := { popped with marks := setMark popped.marks pkg true }
            (true, { marked with cycles := popped.cycles ++ [c] })
        | none => (false, { popped with marks := setMark popped.marks pkg false })

/-- `scan_pkg!`, base/precompilation.jl:960-966. -/
def scanPkg (fuel : Nat) (g : Graph) (pkg : Node) (s : ScanState) : Bool × ScanState :=
  match lookupMark s.marks pkg with
  | some b => (b, s)
  | none => scanDeps fuel g pkg s

end JuliaLean.RuntimeCov.Precompilation

namespace JuliaLean.RuntimeCov.PrecompilationMore

open JuliaLean.RuntimeCov
open JuliaLean.RuntimeCov.Precompilation

/-! ## Verbose timing and progress rendering -/

inductive TimingToken where
  | includeNs (n : Nat)
  | compilationNs (n : Nat)
  | depsNs (n : Nat)
  | methods (n : Nat)
  | other
  deriving DecidableEq, Repr

structure TimingData where
  includeNs : Nat := 0
  compilationNs : Nat := 0
  depsNs : Nat := 0
  methods : Nat := 0
  seenInclude : Bool := false
  deriving DecidableEq, Repr

/-- Token loop inside `format_verbose_timing`, base/precompilation.jl:390-416. -/
def scanTiming : List TimingToken → TimingData
  | [] => {}
  | t :: ts =>
      let d := scanTiming ts
      match t with
      | .includeNs n => { d with includeNs := n, seenInclude := true }
      | .compilationNs n => { d with compilationNs := n }
      | .depsNs n => { d with depsNs := n }
      | .methods n => { d with methods := n }
      | .other => d

/-- Nested `dim`, line 417. -/
def dim (s : String) (isDim : Bool) (paint : String → String) : String :=
  if isDim then paint s else s

/-- Nested `col`, lines 418-427. `rounded` is the decimal string produced by
Julia's two-digit `round`; `small` is `x < 0.005`. -/
def col (rounded : String) (small : Bool) (paint : String → String) : String :=
  let s := if rounded.contains '.' then rounded else rounded ++ ".00"
  dim (lpad s 6 ++ "s") small paint

/-- `format_verbose_timing`, lines 390-438. Numeric presentation is the
`render` callback; parsing, the required include marker and derived image time
are modelled here. -/
def formatVerboseTiming (payload : List TimingToken) (totalNs cacheBytes peakRssBytes : Nat)
    (render : TimingData → Nat → Nat → Nat → String) : String :=
  let d := scanTiming payload
  if d.seenInclude then render d (totalNs - d.includeNs) cacheBytes peakRssBytes else ""

structure ProgressState where
  max : Int
  current : Int
  prev : Int
  hasShown : Bool
  timeShown : Int
  alwaysReprint : Bool
  deriving DecidableEq, Repr

/-- `show_progress`, base/precompilation.jl:488-536. The two Boolean inputs are
the percentage and time throttling comparisons after Julia computes them. -/
def showProgress (p : ProgressState) (percentageAdvanced timeAdvanced : Bool)
    (now : Int) (render : ProgressState → String) : ProgressState × Option String :=
  if !p.alwaysReprint && p.hasShown && !percentageAdvanced then (p, none)
  else if !p.alwaysReprint && p.hasShown && !timeAdvanced then (p, none)
  else
    let p' := { p with timeShown := now, prev := p.current, hasShown := true }
    (p', some (render p'))

/-! ## Explicit environments and workspace traversal, lines 567-911 -/

abbrev Uuid := Nat
abbrev NameMap := List (String × Uuid)
abbrev DepMap := List (Uuid × List Uuid)

structure ExplicitEnv where
  path : String
  projectDeps : NameMap
  projectWeakdeps : NameMap
  projectExtras : NameMap
  projectExtensions : List (String × List Uuid)
  workspaceDeps : List (Uuid × String)
  deps : DepMap
  weakdeps : DepMap
  extensions : List (Uuid × List (String × List Uuid))
  names : List (Uuid × String)
  lookupPresent : List Uuid
  deriving DecidableEq, Repr

/-- `ExplicitEnv(::Nothing, envpath)`, base/precompilation.jl:568-580. -/
def emptyExplicitEnv (envpath : String := "") : ExplicitEnv :=
  ⟨envpath, [], [], [], [], [], [], [], [], [], []⟩

/-- `ExplicitEnv()`, line 567. -/
def defaultExplicitEnv (activeProject : Option String) (load : String → ExplicitEnv) : ExplicitEnv :=
  match activeProject with | none => emptyExplicitEnv | some p => load p

structure ParsedEnv where
  projectDeps : NameMap
  projectWeakdeps : NameMap
  projectExtras : NameMap
  projectExtensions : List (String × List Uuid)
  workspaceDeps : List (Uuid × String)
  deps : DepMap
  weakdeps : DepMap
  extensions : List (Uuid × List (String × List Uuid))
  names : List (Uuid × String)
  lookupPresent : List Uuid
  deriving DecidableEq, Repr

/-- `ExplicitEnv(envpath::String)`, base/precompilation.jl:581-810. The parsed
and expanded TOML tables are explicit because TOML parsing is modelled by its
own area. -/
def explicitEnv (isfile hasManifest : Bool) (absPath : String) (p : ParsedEnv) : ExplicitEnv :=
  if !isfile || !hasManifest then emptyExplicitEnv absPath
  else ⟨absPath, p.projectDeps, p.projectWeakdeps, p.projectExtras,
    p.projectExtensions, p.workspaceDeps, p.deps, p.weakdeps, p.extensions,
    p.names, p.lookupPresent⟩

structure WorkspaceProject where
  file : String
  deps : List (Uuid × String)
  package : Option (Uuid × String)
  members : List String
  deriving DecidableEq, Repr

def putName (xs : List (Uuid × String)) (p : Uuid × String) : List (Uuid × String) :=
  p :: xs.filter (fun q => q.1 != p.1)

/-- `collect_workspace_deps!`, base/precompilation.jl:824-850. -/
def collectWorkspaceDepsAux : Nat → (String → Option WorkspaceProject) →
    List String → List (Uuid × String) → String → List String × List (Uuid × String)
  | 0, _, seen, out, _ => (seen, out)
  | fuel + 1, project, seen, out, file =>
      if file ∈ seen then (seen, out) else
      match project file with
      | none => (file :: seen, out)
      | some p =>
          let out := p.deps.foldl putName out
          let out := match p.package with | some x => putName out x | none => out
          p.members.foldl (fun acc member =>
            collectWorkspaceDepsAux fuel project acc.1 acc.2 member) (file :: seen, out)

/-- `collect_workspace_deps`, base/precompilation.jl:812-822, after the
`base_project` loop selects `root`. -/
def collectWorkspaceDeps (fuel : Nat) (project : String → Option WorkspaceProject)
    (root : String) : List (Uuid × String) :=
  (collectWorkspaceDepsAux fuel project [] [] root).2

structure StdlibFix where
  uuid : Uuid
  deps : List Uuid
  weakdeps : List Uuid
  extensions : List (String × List Uuid)
  discovered : List (Uuid × String)
  deriving DecidableEq, Repr

def replaceDeps (m : DepMap) (u : Uuid) (ds : List Uuid) : DepMap :=
  (u, ds) :: m.filter (fun p => p.1 != u)

/-- `fixup_stdlib_deps!`, base/precompilation.jl:859-911. Each `StdlibFix`
is one validated stdlib Project.toml discovered by the source loop. -/
def fixupStdlibDeps (deps weak : DepMap) (names : List (Uuid × String))
    (fixes : List StdlibFix) : DepMap × DepMap × List (Uuid × String) :=
  fixes.foldl (fun acc f =>
    (replaceDeps acc.1 f.uuid f.deps, replaceDeps acc.2.1 f.uuid f.weakdeps,
      f.discovered.foldl putName acc.2.2)) (deps, weak, names)

/-! ## Dependency graph helpers, lines 916-1204 -/

/-- `full_name`, base/precompilation.jl:916-922. -/
def fullName (parent : Node → Option String) (name : Node → String) (pkg : Node) : String :=
  match parent pkg with | some p => p ++ " → " ++ name pkg | none => name pkg

/-- `excluded_circular_deps_explanation`, lines 924-957, represented by the
ordered cycle and outer-package names that its loops print. -/
def excludedCircularDepsExplanation (circular : List Node) (cycles : List (List Node)) :
    List (List Node) × List Node :=
  (cycles, circular.filter (fun p => !cycles.any (fun c => p ∈ c)))

def insertUnique (x : Node) (xs : List Node) : List Node := if x ∈ xs then xs else x :: xs

/-- `collect_all_deps`, base/precompilation.jl:995-1003. -/
def collectAllDeps : Nat → Graph → Node → List Node → List Node
  | 0, _, _, out => out
  | fuel + 1, g, n, out =>
      (depsOf g n).foldl (fun acc d =>
        if d ∈ acc then acc else collectAllDeps fuel g d (d :: acc)) out

/-- `visit_indirect_deps!`, base/precompilation.jl:1005-1018. -/
def visitIndirectDeps : Nat → Graph → List Node → List Node → Node → List Node × List Node
  | 0, _, visited, all, _ => (visited, all)
  | fuel + 1, g, visited, all, n =>
      if n ∈ visited then (visited, all) else
      (depsOf g n).foldl (fun acc d =>
        if d ∈ acc.2 then acc else visitIndirectDeps fuel g acc.1 (d :: acc.2) d)
        (n :: visited, all)

structure BuildGraphInput where
  direct : Graph
  extensionEdges : Graph
  projectDeps : List Node
  serialDeps : List Node
  deriving DecidableEq, Repr

/-- `build_dep_graph`, base/precompilation.jl:1022-1141. The environment and
extension loops supply their validated direct and extension edges. -/
def buildDepGraph (i : BuildGraphInput) : Graph × List Node × List Node :=
  let direct := i.extensionEdges.foldl (fun g p =>
    (p.1, p.2) :: g.filter (fun q => q.1 != p.1)) i.direct
  (direct, i.projectDeps, i.serialDeps)

/-- `detect_circular_deps!`, base/precompilation.jl:1145-1164. -/
def detectCircularDeps (g : Graph) (serial : List Node) : List Node × List (List Node) :=
  g.foldl (fun acc p =>
    if p.1 ∈ serial then acc else
    let r := scanPkg (g.length + 1) g p.1 ⟨[], [], acc.2⟩
    (if r.1 then insertUnique p.1 acc.1 else acc.1, r.2.cycles)) ([], [])

/-- `filter_dep_graph!`, base/precompilation.jl:1168-1190. -/
def filterDepGraph (g : Graph) (requested : List Node) : Graph :=
  let keep := requested.foldl (fun ks n => collectAllDeps (g.length + 1) g n (insertUnique n ks)) []
  g.filter (fun p => p.1 ∈ keep)

/-- `preresolved_snapshot`, lines 1193-1196. -/
def preresolvedSnapshot (paths : List (Node × List String)) (checked : String → Bool) : List (Node × String) :=
  (paths.filterMap fun p => p.2.head?.map (p.1, ·)).filter (fun p => checked p.2)

/-- `checked_now!`, lines 1199-1204. The Boolean result and remaining
unverified set are both observable state. -/
def checkedNow (path : String) (unverified : List String) (checksumOk : Bool) : Bool × List String :=
  if path ∉ unverified then (true, unverified)
  else if !checksumOk then (false, unverified)
  else (true, unverified.erase path)

/-! ## Public and background lifecycle, lines 1337-2063 -/

structure FrontendArgs where
  timing : Bool
  verbose : Bool
  force : Bool
  forceStdlibs : Bool
  configs : Nat
  deriving DecidableEq, Repr

/-- `precompilepkgs`, base/precompilation.jl:1337-1368. -/
def precompilePkgs (a : FrontendArgs) : FrontendArgs :=
  ⟨a.timing || a.verbose, a.verbose, a.force || a.forceStdlibs, a.forceStdlibs,
    max 1 a.configs⟩

inductive LoadingGate where | disabled | generating | parallelDisabled | run | swallowed | rethrow
  deriving DecidableEq, Repr

/-- `precompile_for_loading`, lines 1384-1395. -/
def precompileForLoading (compiled generating parallelDisabled : Bool)
    (result : Rt Unit) : LoadingGate :=
  if !compiled then .disabled else if generating then .generating else if parallelDisabled then .parallelDisabled
  else match result with
    | .ok _ => .run
    | .error (.errorException _) => .rethrow
    | .error _ => .swallowed

structure LoadingScan where
  identified : List Node
  alreadyLoaded : List Node
  extensions : List Node
  stale : List Node
  deriving DecidableEq, Repr

/-- `_precompile_for_loading`, lines 1397-1455. -/
def precompileForLoadingCore (s : LoadingScan) : List Node :=
  let pkgs := (s.identified.filter (fun p => p ∉ s.alreadyLoaded)).foldl (fun a p => insertUnique p a) []
  let pkgs := s.extensions.foldl (fun a p => insertUnique p a) pkgs
  if pkgs.length ≤ 1 then [] else pkgs.filter (fun p => p ∈ s.stale)

/-- Nested `available`, lines 1417-1418. -/
def available (u : Uuid) (reachable loaded sysimage : List Uuid) : Bool :=
  u ∈ reachable || u ∈ loaded || u ∈ sysimage

/-- Nested `label`, line 1449. -/
def label (pkg : Node) (parent : Node → Option String) (plain : Node → String) : String :=
  fullName parent plain pkg

structure BackgroundState where
  taskPresent : Bool
  taskDone : Bool
  interruptRequested : Bool
  cancelRequested : Bool
  monitoring : Bool
  pending : List (Node × Nat)
  completed : List Node
  signalChannels : Nat
  detachable : Bool
  confirming : Sym
  keyListening : Bool
  foregroundMonitors : Nat
  verbose : Bool
  deriving DecidableEq, Repr

def pendingCount (s : BackgroundState) (p : Node) : Nat :=
  match s.pending.find? (fun q => q.1 = p) with | some q => q.2 | none => 0

/-- `is_precompiling_in_background`, lines 1459-1461. -/
def isPrecompilingInBackground (s : BackgroundState) : Bool := s.taskPresent && !s.taskDone

/-- `is_package_pending`, lines 1466-1472. -/
def isPackagePending (s : BackgroundState) (p : Node) : Bool :=
  s.taskPresent && !s.taskDone && pendingCount s p > 0

/-- `wait_for_pending_package`, lines 1476-1481. -/
def waitForPendingPackage (s : BackgroundState) (p : Node) : Bool := isPackagePending s p

/-- Both `broadcast_signal` methods, lines 1484-1491. -/
def broadcastSignal (s : BackgroundState) (_sig : Int) : Nat := s.signalChannels

/-- `mark_completed_pkgid!`, lines 1495-1501. -/
def markCompletedPkgid (s : BackgroundState) (p : Node) : BackgroundState :=
  { s with completed := insertUnique p s.completed }

/-- `stop_background_precompile`, lines 1503-1517. -/
def stopBackgroundPrecompile (s : BackgroundState) (graceful : Bool) : Bool × BackgroundState :=
  if s.taskPresent && !s.taskDone then
    (true, if graceful then { s with interruptRequested := true }
           else { s with cancelRequested := true })
  else (false, s)

/-- `keyboard_tip`, lines 1535-1548. -/
def keyboardTip (s : BackgroundState) (remaining : Nat) : String :=
  if !s.monitoring || !s.keyListening then ""
  else if s.confirming != "none" then "Press Enter to " ++ s.confirming ++
    " (ignoring in " ++ toString remaining ++ "s)"
  else if s.detachable then "Press `?` for help, `c` to cancel, `d` to detach."
  else "Press `?` for help, `c` to cancel."

/-- `monitor_background_precompile`, lines 1550-1553. -/
def monitorBackgroundPrecompile {α : Type} (stabilize : α → α) (io : α) : α := stabilize io

inductive MonitorAction where | idle | completed | cancel | interrupt | packageDone | detach | normal
  deriving DecidableEq, Repr

/-- `_monitor_background_precompile`, lines 1555-1847, reduced to the same
ordered terminal decisions after its listener and watcher update their flags. -/
def monitorBackgroundCore (s : BackgroundState) (completedAt exit cancel interrupt waitingForPkg : Bool) :
    MonitorAction × BackgroundState :=
  if !s.taskPresent || s.taskDone then (if completedAt then .completed else .idle, s)
  else if cancel then (.cancel, { s with monitoring := false })
  else if interrupt then (.interrupt, s)
  else if exit && waitingForPkg then (.packageDone, s)
  else if exit then (.detach, { s with monitoring := false })
  else (.normal, s)

/-- `stop_monitoring_unless_waited_on`, lines 1852-1858. -/
def stopMonitoringUnlessWaitedOn (s : BackgroundState) (counted : Bool) : Bool × BackgroundState :=
  let others := s.foregroundMonitors > (if counted then 1 else 0)
  (others, if others then s else { s with monitoring := false })

/-- State reset performed by `launch_background_precompile`, lines 1860-1963. -/
def launchBackgroundPrecompile (s : BackgroundState) (verbose : Bool) : BackgroundState :=
  ⟨true, false, false, false, true, [], [], 0, s.detachable, s.confirming,
    s.keyListening, s.foregroundMonitors, verbose⟩

/-- `_collect_reachable!`, lines 1965-1971. -/
def collectReachable (fuel : Nat) (g : Graph) (root : Node) : List Node :=
  collectAllDeps fuel g root [root]

inductive PrecompileDispatch where | inject | launch | injectedLoading | injectedInteractive | detached | finished
  deriving DecidableEq, Repr

/-- `_precompilepkgs`, lines 1973-2063. -/
def precompilePkgsDispatch (canInject fromLoading resultReady : Bool) : PrecompileDispatch :=
  if canInject then
    if fromLoading then .injectedLoading else if resultReady then .injectedInteractive else .detached
  else .launch

/-! ## Process, message and scheduling helpers, lines 2079-2676 -/

structure ProcessStats where
  cpuNs : Nat
  rssBytes : Nat
  deriving DecidableEq, Repr

/-- `process_stats`, lines 2079-2122. Platform parsing succeeds with the two
values or returns the documented zero pair on unsupported/error paths. -/
def processStats (supported parseOk : Bool) (cpu rss : Nat) : ProcessStats :=
  if supported && parseOk then ⟨cpu, rss⟩ else ⟨0, 0⟩

structure PollResult where
  cpuPct : Nat
  rss : Nat
  previousCpu : Nat
  peakRss : Nat
  deriving DecidableEq, Repr

/-- One unique active-PID iteration of `poll_process_stats!`, lines 2126-2154. -/
def pollProcessStats (previous dt : Nat) (s : ProcessStats) (oldPeak : Nat) : PollResult :=
  if s.cpuNs = 0 then ⟨0, 0, previous, oldPeak⟩ else
  let delta := s.cpuNs - previous
  let pct := if dt > 0 then min (delta / dt) 999 else 0
  ⟨pct, s.rssBytes, s.cpuNs, max oldPeak s.rssBytes⟩

/-- One unique active-PID iteration of `sample_peak_rss!`, lines 2159-2175. -/
def samplePeakRss (old sample : Nat) : Nat := max old sample

structure StopState where
  interrupted : Bool
  canceled : Bool
  done : Bool
  deriving DecidableEq, Repr

/-- `should_stop`, lines 2177-2194. -/
def shouldStop (s : StopState) (interrupt cancel : Bool) : Bool × StopState :=
  if interrupt || cancel then
    (true, ⟨s.interrupted || interrupt, s.canceled || cancel, true⟩)
  else (s.done, s)

/-- `make_signal_channel`, lines 2196-2200. -/
def makeSignalChannel (count : Nat) : Nat := count + 1

/-- `describe_pkg`, lines 2202-2217. -/
def describePkg (name flags cacheflags : String) (project serial multi hascolor : Bool) : String :=
  let name := if project then name else colorString name "" "" hascolor
  let name := if serial then name ++ " (serial)" else name
  let name := if multi && !flags.isEmpty then name ++ " `" ++ flags ++ "`" else name
  if multi then name ++ " " ++ cacheflags else name

/-- `format_names_list`, lines 2220-2225. -/
def formatNamesList (names : List String) (maxNames : Nat := 5) : String :=
  if names.length > maxNames then
    String.intercalate ", " (names.take maxNames) ++ ", and " ++
      toString (names.length - maxNames) ++ " more"
  else String.intercalate " and " names

/-- `print_header`, lines 2227-2232. -/
def printHeader (target : String) (verbose : Bool) : String × Bool :=
  ("Precompiling " ++ target ++ if verbose then "\n" ++ formatVerboseTimingHeader else "", true)

/-- `explain_reasons!`, lines 2239-2257. -/
def explainReasons (fromLoading flagsExplained onlyFlags : Bool)
    (newConflicts stacked : List String) : List String × Bool :=
  if !fromLoading then ([], flagsExplained) else
  (newConflicts ++ stacked ++ if !flagsExplained && onlyFlags then ["flags"] else [],
    flagsExplained || onlyFlags)

/-- `loaded_version_differs`, lines 2260-2268. -/
def loadedVersionDiffers (loaded env : Option Nat) : Bool :=
  match loaded, env with | some a, some b => a != b | _, _ => false

/-- `loaded_version_conflicts`, lines 2273-2280. -/
def loadedVersionConflicts (deps loaded differing : List Node) : List Node :=
  deps.filter (fun p => p ∈ loaded && p ∈ differing)

/-- `resolved_version`, lines 2284-2289. -/
def resolvedVersion (loaded located : Option Nat) : Option Nat :=
  match loaded with | some v => some v | none => located

/-- `stacked_version_conflicts`, lines 2295-2322, after its file-system
lookups produce `(environment, dependent, dependency)` triples. -/
def stackedVersionConflicts (rows : List (String × String × String)) : List (String × List String × List String) :=
  rows.foldl (fun out r =>
    match out.find? (fun x => x.1 = r.1) with
    | none => (r.1, [r.2.1], [r.2.2]) :: out
    | some old => (r.1, insertUniqueString r.2.1 old.2.1,
        insertUniqueString r.2.2 old.2.2) :: out.filter (fun x => x.1 != r.1)) []
where
  insertUniqueString (s : String) (xs : List String) := if s ∈ xs then xs else s :: xs

/-- `env_display_name`, lines 2325-2330. -/
def envDisplayName (named : Option String) (contracted : String) : String :=
  match named with | some n => "@" ++ n | none => contracted

def stackedConflictsMessage (dependents deps env : String) (oneDependent oneDep : Bool) : String :=
  dependents ++ (if oneDependent then " is" else " are") ++ " from " ++ env ++
    ", where " ++ deps ++ (if oneDep then " has a different version" else " have different versions")

/-- `only_flags_mismatch`, lines 2346-2349. -/
def onlyFlagsMismatch (hasFlags : Bool) (otherActionable : List Bool) : Bool :=
  hasFlags && !otherActionable.any id

def loadedConflictsMessage (names : String) (one ongoing cancelable defaultEnv : Bool) : String :=
  names ++ (if one then " is loaded at a different version" else " are loaded at different versions") ++
    (if ongoing then " and dependents are being precompiled." else " and dependents were precompiled.") ++
    (if cancelable && ongoing then " Press c to cancel." else "") ++
    (if defaultEnv then " Restart julia." else " Restart julia with --project set.")

inductive PrintLoopResult where | noWork | stopped | rendered deriving DecidableEq, Repr
def spawnPrintLoop (queueEmpty stopped : Bool) : PrintLoopResult :=
  if queueEmpty || stopped then .noWork else .rendered

/-- `precompilepkgs_monitor_std`, lines 2515-2552. -/
def precompilepkgsMonitorStd (readOk : Bool) (chunks : List String) : String × Bool :=
  (String.join chunks, readOk)

/-- `precompile_pkgs_maybe_cachefile_lock`, lines 2560-2597. -/
def maybeCachefileLock {α : Type} (fromLoading lockAcquired : Bool)
    (run : α) (waited : α) : α :=
  if fromLoading && !lockAcquired then waited else run

/-- `precompile_cost_estimate`, lines 2601-2613. -/
def precompileCostEstimate (mtime cacheSize : Option Nat) : Nat :=
  match mtime, cacheSize with | some t, some s => t + s | some t, none => t | _, _ => 0

structure SchedulePriorities where
  direct : Graph
  cost : List (Node × Nat)
  height : List (Node × Nat)
  deriving DecidableEq, Repr

def scheduleHeight : Nat → Graph → Node → Nat
  | 0, _, _ => 0
  | fuel + 1, g, n => 1 + (depsOf g n).foldl (fun h d => max h (scheduleHeight fuel g d)) 0

/-- `SchedulePriorities`, lines 2630-2638. -/
def newSchedulePriorities (g : Graph) (cost : List (Node × Nat)) : SchedulePriorities :=
  ⟨g, cost, g.map (fun p => (p.1, scheduleHeight (g.length + 1) g p.1))⟩

/-- `schedule_priority`, line 2640. -/
def schedulePriority (p : SchedulePriorities) (pkg : Node) : Nat × Nat :=
  ((p.height.find? (fun x => x.1 = pkg)).map (·.2) |>.getD 0,
   (p.cost.find? (fun x => x.1 = pkg)).map (·.2) |>.getD 0)

/-- `schedule_height!`, lines 2643-2654. -/
def scheduleHeightCached (p : SchedulePriorities) (pkg : Node) : Nat := (schedulePriority p pkg).1

/-- `is_stdlib_source`, line 2658. -/
def isStdlibSource (inStdlib : Bool) : Bool := inStdlib

/-- `failed_dependency`, lines 2665-2673. -/
def failedDependency (deps failed : List Node) : Option Node := deps.find? (· ∈ failed)

/-- `unverified_set`, line 2676. -/
def unverifiedSet (fromLoading : Bool) (xs : List String) : List String := if fromLoading then xs else []

/-! ## Task orchestration, lines 2678-3481 -/

structure SpawnSummary where
  spawned : List Node
  skipped : List Node
  deriving DecidableEq, Repr

/-- `spawn_precompile_tasks!`, lines 2678-2925. The lists are its dependency,
cycle and failed-dependency decisions after cache freshness checks. -/
def spawnPrecompileTasks : List Node → List Node → List Node → SpawnSummary
  | [], _, _ => ⟨[], []⟩
  | p :: ps, circular, failed =>
      let out := spawnPrecompileTasks ps circular failed
      if p ∈ circular || p ∈ failed then ⟨out.spawned, out.skipped ++ [p]⟩
      else ⟨out.spawned ++ [p], out.skipped⟩

/-- `drain_work_channel!`, lines 2927-3048. Each injected request contributes
only packages not already present in the session graph. -/
def drainWorkChannel (known : List Node) (requests : List (List Node)) : List Node :=
  requests.foldl (fun ks rs => rs.foldl (fun a p => insertUnique p a) ks) known

inductive ReportResult where | ok | failed | interrupted | canceledLoading deriving DecidableEq, Repr

/-- `report_precompile_results!`, lines 3050-3273. -/
def reportPrecompileResults (failed interrupted canceled fromLoading : Bool) : ReportResult :=
  if failed then .failed else if interrupted then .interrupted
  else if canceled && fromLoading then .canceledLoading else .ok

structure DriverResult where
  tasks : Nat
  fancy : Bool
  brief : Bool
  requested : List Node
  deriving DecidableEq, Repr

/-- `do_precompile`, lines 3276-3481. The model retains the option
normalization and request selection that determine every later branch. -/
def doPrecompile (requested identified : List Node) (windows fromLoading interactive quiet fancy : Bool)
    (envTasks : Option Nat) : DriverResult :=
  let defaultTasks := if windows then 1 else 2
  let tasks := max 1 (envTasks.getD defaultTasks)
  let brief := fromLoading && !interactive && !quiet
  let fancy := fancy && !brief && !quiet
  ⟨tasks, fancy, brief, if requested.isEmpty then identified else requested⟩

end JuliaLean.RuntimeCov.PrecompilationMore
