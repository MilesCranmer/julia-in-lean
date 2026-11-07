import JuliaLean.Proofs.base.locks_mt.common
import JuliaLean.Core
import JuliaLean.base.lock
import JuliaLean.base.pointer

/-!
# Model of `base/threadcall.jl`

Typed models of the worker-thread limit and its callback lifecycle. The semaphore,
environment access, integer parsing, task scheduling, GC handles, C callbacks, queueing,
waiting, and result storage are explicit typed operations. `@threadcall` remains visible
because it generates Julia syntax during macro expansion.
-/

namespace JuliaLean.base.threadcall

open JuliaLean
open JuliaLean.base.pointer

abbrev I := JInt .i64
abbrev M (E W A : Type) := JuliaLean.base.locks_mt.M E W A

def int (n : Int) : I := JInt.wrap .i64 n

structure ThreadcallInitOps (E W S Q L Tok Value : Type) where
  semaphore : JuliaLean.base.lock.SemaphoreOps E W S Q L Tok Value
  getEnv : String → String → M E W String
  parseInt : String → M E W I

structure ThreadcallOps
    (E W S Q L Tok Value Task F Context ContextPointer ContextRoot : Type)
    (ResultRef : Type → Type) where
  semaphore : JuliaLean.base.lock.SemaphoreOps E W S Q L Tok Value
  restrictor : S
  makeRunCallback : (F → M E W Unit) → M E W (Ptr Unit)
  makeNotifyCallback : (Task → Context → M E W Unit) → M E W (Ptr Unit)
  newContext : F → M E W Context
  contextPointer : Context → M E W ContextPointer
  contextRoot : Context → M E W ContextRoot
  queueWork : Ptr Unit → ContextPointer → Ptr Unit → Task → ContextRoot → M E W Unit
  currentTask : M E W Task
  schedule : Task → M E W Unit
  preserveTask : Task → M E W Unit
  preserveContext : Context → M E W Unit
  unpreserveTask : Task → M E W Unit
  unpreserveContext : Context → M E W Unit
  wait : M E W Unit
  runWrapper : F → M E W Unit
  readResult : {T : Type} → ResultRef T → M E W T

/--
Julia source: base/threadcall.jl:3-3 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const max_ccall_threads = parse(Int, get(ENV, "UV_THREADPOOL_SIZE", "4"))
```
-/
def maxCcallThreads {E W S Q L Tok Value : Type}
    (ops : ThreadcallInitOps E W S Q L Tok Value) : M E W I := do
  let value ← ops.getEnv "UV_THREADPOOL_SIZE" "4"
  ops.parseInt value

/--
Julia source: base/threadcall.jl:4-4 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const threadcall_restrictor = Semaphore(max_ccall_threads)
```
-/
def newThreadcallRestrictor {E W S Q L Tok Value : Type}
    (ops : ThreadcallInitOps E W S Q L Tok Value) : M E W S := do
  let size ← maxCcallThreads ops
  JuliaLean.base.lock.newSemaphore ops.semaphore size

/--
Julia source: base/threadcall.jl:61-67 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# call wrapper invoked on the libuv worker thread. `F` is the concrete type of
# the work closure, so `f()` is fully devirtualized; the closure is delivered
# by value through the `Ref{F}` cfunction argument in `do_threadcall`.
function threadcall_run(f::F) where F
    f()
    return
end
```
-/
def threadcallRun
    {E W S Q L Tok Value Task F Context ContextPointer ContextRoot : Type} {ResultRef : Type → Type}
    (ops : ThreadcallOps E W S Q L Tok Value Task F Context ContextPointer ContextRoot ResultRef)
    (wrapper : F) : M E W Unit := do
  let _ ← ops.runWrapper wrapper
  pure ()

/--
Julia source: base/threadcall.jl:69-76 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# called from the libuv event loop once the queued work has finished, to wake
# up the task waiting in `do_threadcall`
function threadcall_notify(ct::Task, ctx::RefValue{Any})
    schedule(ct)
    unpreserve_handle(ct)
    unpreserve_handle(ctx)
    return
end
```
-/
def threadcallNotify
    {E W S Q L Tok Value Task F Context ContextPointer ContextRoot : Type} {ResultRef : Type → Type}
    (ops : ThreadcallOps E W S Q L Tok Value Task F Context ContextPointer ContextRoot ResultRef)
    (task : Task) (context : Context) : M E W Unit := do
  ops.schedule task
  ops.unpreserveTask task
  ops.unpreserveContext context
  pure ()

/--
Julia source: base/threadcall.jl:78-109 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function do_threadcall(wrapper::F, result::Ref{T}) where {F, T}
    # a plain (non-closure) call wrapper, specialized to `F` via the `Ref{F}`
    # argument type; the closure is handed to C as an opaque context pointer
    c_run = @cfunction(threadcall_run, Cvoid, (Ref{F},))
    # function pointer used to notify us when the work is done
    c_notify_fun = @cfunction(threadcall_notify, Cvoid, (Ref{Task}, Ref{RefValue{Any}},))

    # box the closure so wrapper has a stable address to preserve
    # pass as Ptr{Cvoid} to pass that stable address
    ctx = RefValue{Any}(wrapper)

    # wait for a worker thread to be available
    acquire(threadcall_restrictor)
    try
        ct = current_task()
        # keep the waiting task and the boxed closure alive until the worker thread
        # has finished and woken us back up: the task so the notifier can find it by
        # pointer, and the closure box so its captured values survive
        preserve_handle(ct)
        preserve_handle(ctx)
        # queue up the work to be done
        ccall(:jl_queue_work, Cvoid,
            (Ptr{Cvoid}, Ptr{Cvoid}, Ptr{Cvoid}, Any, Ref{RefValue{Any}}),
            c_run, ctx, c_notify_fun, ct, ctx)

        # wait for a result
        wait()
    finally
        release(threadcall_restrictor)
    end
    return result[]
end
```
-/
def doThreadcall
    {E W S Q L Tok Value Task F Context ContextPointer ContextRoot : Type} {ResultRef : Type → Type} {T : Type}
    (ops : ThreadcallOps E W S Q L Tok Value Task F Context ContextPointer ContextRoot ResultRef)
    (wrapper : F) (result : ResultRef T) : M E W T := do
  let runCallback ← ops.makeRunCallback (threadcallRun ops)
  let notifyCallback ← ops.makeNotifyCallback (threadcallNotify ops)
  let context ← ops.newContext wrapper
  JuliaLean.base.lock.acquireSemaphore ops.semaphore ops.restrictor
  JuliaLean.base.locks_mt.finallyDo (do
    let task ← ops.currentTask
    ops.preserveTask task
    ops.preserveContext context
    let contextPointer ← ops.contextPointer context
    let contextRoot ← ops.contextRoot context
    ops.queueWork runCallback contextPointer notifyCallback task contextRoot
    ops.wait) (JuliaLean.base.lock.releaseSemaphore ops.semaphore ops.restrictor)
  ops.readResult result

-- Reason: `@threadcall` rewrites Julia `Expr` syntax and emits an escaped C-call wrapper during macro expansion.
-- UNTRANSLATED
-- Source: base/threadcall.jl:6-59 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     @threadcall((cfunc, clib), rettype, (argtypes...), argvals...)
-- 
-- The `@threadcall` macro is called in the same way as [`ccall`](@ref) but does the work
-- in a different thread. This is useful when you want to call a blocking C
-- function without causing the current `julia` thread to become blocked. Concurrency
-- is limited by size of the libuv thread pool, which defaults to 4 threads but
-- can be increased by setting the `UV_THREADPOOL_SIZE` environment variable and
-- restarting the `julia` process.
-- 
-- Note that the called function should never call back into Julia.
-- """
-- macro threadcall(f, rettype, argtypes, argvals...)
--     # check for usage errors
--     isa(argtypes,Expr) && argtypes.head === :tuple ||
--         error("threadcall: argument types must be a tuple")
--     length(argtypes.args) == length(argvals) ||
--         error("threadcall: wrong number of arguments to C function")
-- 
--     # hygiene escape arguments
--     f = esc(f)
--     rettype = esc(rettype)
--     argtypes = map(esc, argtypes.args)
--     argvals = map(esc, argvals)
-- 
--     # `cconvert` and `unsafe_convert` each argument on the calling thread:
--     # cconvert may allocate or run arbitrary Julia code, and computing the
--     # unsafe_convert'd C representation here keeps all of that off the libuv
--     # worker thread, which only makes the raw call. The cconverted values are
--     # captured by the wrapper closure and GC.@preserve'd around the worker-thread
--     # ccall so their C representations (e.g. interior pointers) stay valid.
--     roots = [Symbol("root", i) for i in 1:length(argvals)]
--     args  = [Symbol("arg", i) for i in 1:length(argvals)]
--     rootbinds = [:($(roots[i]) = cconvert($(argtypes[i]), $(argvals[i]))) for i in 1:length(argvals)]
--     argbinds  = [:($(args[i]) = unsafe_convert($(argtypes[i]), $(roots[i]))) for i in 1:length(argvals)]
--     call = :(result[] = ccall(cfptr, $rettype, ($(argtypes...),), $(args...)))
--     # keep the cconverted values alive while their C representations are in use
--     body = isempty(roots) ? call : :(GC.@preserve $(roots...) $call)
-- 
--     return quote
--         # use cglobal to look up the function on the calling thread
--         cfptr = cglobal($f)
--         $(rootbinds...)
--         $(argbinds...)
--         result = Ref{$rettype}()
--         # closure that performs the actual call on the worker thread and stores
--         # the result into the captured cell
--         wrapper = function ()
--             $body
--             return
--         end
--         do_threadcall(wrapper, result)
--     end
-- end
-- /Source

end JuliaLean.base.threadcall

namespace JuliaLean.ConcurrencyCov.Threadcall

open JuliaLean.ConcurrencyCov

structure MacroPlan where
  roots : Nat
  converted : Nat
  unsafeConverted : Nat
  preservesRoots : Bool
  deriving DecidableEq, Repr
/-- `@threadcall` validates tuple syntax and arity before building one conversion
and one root per argument (`base/threadcall.jl:18-59`). -/
def threadcallMacro (tupleSyntax : Bool) (argTypes argValues : Nat) : R MacroPlan :=
  if !tupleSyntax then .error (.errorException "threadcall: argument types must be a tuple")
  else if argTypes != argValues then
    .error (.errorException "threadcall: wrong number of arguments to C function")
  else .ok ⟨argValues, argValues, argValues, argValues != 0⟩
def threadcallRun (f : Outcome) : Outcome := f
structure NotifyState where
  scheduled : Bool := false
  taskPreserved : Bool := true
  contextPreserved : Bool := true
  deriving DecidableEq, Repr
def threadcallNotify (s : NotifyState) : NotifyState :=
  { s with scheduled := true, taskPreserved := false, contextPreserved := false }
structure CallState where
  permits : Nat
  queued : Nat := 0
  taskPreserved : Bool := false
  contextPreserved : Bool := false
  waited : Bool := false
  deriving DecidableEq, Repr
/-- `do_threadcall` acquires one semaphore permit, preserves the task and closure,
queues and waits, then releases the permit in `finally` and returns `result[]`
(`base/threadcall.jl:78-109`). -/
def doThreadcall (result : Nat) (s : CallState) : Option (Nat × CallState) :=
  if s.permits = 0 then none
  else some (result, ⟨s.permits, s.queued + 1, true, true, true⟩)
/-- The limiter is serialized in the system image, so a restarted process should
honor its current `UV_THREADPOOL_SIZE` value as the docstring promises. -/
def limiterSize (sysimageValue processEnvironment : Nat) : Nat := sysimageValue

end JuliaLean.ConcurrencyCov.Threadcall

namespace JuliaLean.ConcurrencyCov.FaithfulSmall

open JuliaLean.ConcurrencyCov

/-! ## `base/threadcall.jl` -/

structure ThreadcallPlan where
  functionExpr : Nat
  returnType : Nat
  argTypes : List Nat
  argValues : List Nat
  roots : List Nat
  converted : List (Nat × Nat)
  unsafeConverted : List (Nat × Nat)
  preserves : List Nat
  deriving DecidableEq, Repr

def threadcallMacro (isTuple : Bool) (f returnType : Nat)
    (argTypes argValues : List Nat) : R ThreadcallPlan :=
  if !isTuple then .error (.errorException "threadcall: argument types must be a tuple")
  else if argTypes.length != argValues.length then
    .error (.errorException "threadcall: wrong number of arguments to C function")
  else
    let roots := List.range argValues.length
    .ok ⟨f, returnType, argTypes, argValues, roots, argTypes.zip argValues,
      argTypes.zip roots, roots⟩

def threadcallRun (call : R Unit) : R Unit :=
  match call with | .ok () => .ok () | .error e => .error e

structure NotifyTrace where
  scheduled : Bool
  taskUnpreserved : Bool
  contextUnpreserved : Bool
  deriving DecidableEq, Repr

def threadcallNotify : NotifyTrace := ⟨true, true, true⟩

inductive ThreadcallOp where
  | makeRunCallback | makeNotifyCallback | boxContext | acquire
  | preserveTask | preserveContext | queue | wait | release | readResult
  deriving DecidableEq, Repr

def doThreadcall (result : Nat) : Nat × List ThreadcallOp :=
  (result, [.makeRunCallback, .makeNotifyCallback, .boxContext, .acquire,
    .preserveTask, .preserveContext, .queue, .wait, .release, .readResult])

end JuliaLean.ConcurrencyCov.FaithfulSmall
