import JuliaLean.Proofs.base.locks_mt.common
import JuliaLean.base.locks_mt
import JuliaLean.base.expr

/-!
# Typed model of `base/threadingconstructs.jl`

Runtime queries retain their C integer widths. The scheduler, cancellation tree,
mutable task vectors, and atomic accesses are explicit world-passing primitives.
Thread bodies remain typed functions. Macro helper functions use the expression
model, while `@threads` and `@spawn` expansion stays untranslated.
-/
namespace JuliaLean.base.threadingconstructs
open JuliaLean
open JuliaLean.base.locks_mt (M MemoryOrder loop finallyDo liftFrame runFrame getFrame setFrame)
open JuliaLean.base.expr
abbrev I := JInt .i64
abbrev I8 := JInt .i8
abbrev I16 := JInt .i16
abbrev CInt := JInt .i32
def int (n : Int) : I := JInt.wrap .i64 n

inductive Pool where
  | interactive | default | foreign | other (name : String)
  deriving DecidableEq, Repr

def Pool.name : Pool → String
  | .interactive => "interactive"
  | .default => "default"
  | .foreign => "foreign"
  | .other name => name

structure PoolCountsRef where
  identity : Nat

structure Queries (E W : Type) where
  threadId : M E W I16
  maxThreadId : MemoryOrder → M E W CInt
  poolCounts : M E W PoolCountsRef
  loadPoolCount : PoolCountsRef → I → M E W CInt
  threadPoolId : I16 → M E W I8
  threadPoolCount : M E W CInt
  gcThreadCount : M E W CInt
  collectRange : I → I → M E W (List I)
  argumentError : String → E
  error : String → E
  juliaError : JlError → E

def liftResult {E W A : Type} : Except E A → M E W A
  | .ok value => pure value
  | .error error => throw error

def forRange {E W : Type} (first last : I) (body : I → M E W Unit) : M E W Unit := do
  if first.val > last.val then return ()
  loop (fun index => do
    body index
    if index.val == last.val then return .inl ()
    pure (.inr (index + int 1))) first

inductive WaitResult where
  | completed | cancelled (severity : UInt8)
  deriving DecidableEq, Repr

structure ThreadsFun (F : Type) where
  callable : F

structure Scheduler (E W Task Tasks Source Token V : Type) where
  queries : Queries E W
  inThreadedRegion : M E W CInt
  enterThreadedRegion : M E W Unit
  exitThreadedRegion : M E W Unit
  newTaskVector : I → M E W Tasks
  defaultCancelToken : M E W (Option Token)
  newCancellationSource : Option Token → M E W Source
  cancellationToken : Source → Token
  withToken : Token → M E W Unit → M E W Unit
  newTask : M E W V → M E W Task
  setSticky : Task → Bool → M E W Unit
  setTaskThreadId : Task → I → M E W CInt
  setTaskThreadPoolId : Task → I8 → M E W CInt
  setTask : Tasks → I → Task → M E W Unit
  getTask : Tasks → I → M E W Task
  schedule : Task → M E W Unit
  waitTask : Task → Token → UInt8 → Bool → M E W WaitResult
  isTaskFailed : Task → M E W Bool
  filterTasks : (Task → M E W Bool) → Tasks → M E W (List Task)
  compositeTaskFailures : List Task → E
  cancellationRequest : UInt8 → E
  abandonAll : UInt8
  assertionError : String → E

structure Comprehension (E W Arr Value Ty : Type) where
  isEmpty : Arr → M E W Bool
  promoteTypejoinUnion : Ty → M E W Ty
  elementType : Arr → M E W Ty
  sameType : Ty → Ty → Bool
  similar : Arr → Ty → M E W Arr
  concreteType : Ty → Bool
  first : Arr → M E W Value
  firstIndex : Arr → M E W I
  lastIndex : Arr → M E W I
  getInbounds : Arr → I → M E W Value
  typeOf : Value → Ty
  isa : Value → Ty → Bool
  promoteTypejoin : Ty → Ty → M E W Ty
  copyTo : Arr → Arr → M E W Arr

/-- Julia expression values used by the threaded macro helpers. -/
abbrev ThreadAst (L : Type) := JuliaLean.base.expr.Value L
abbrev ThreadAstResult (α : Type) := JuliaLean.base.expr.ExprResult α

structure ThreadExprOps (L State : Type) where
  leaves : JuliaLean.base.expr.LeafOps L
  coreModule : L
  iteratorsModule : L
  threadingModule : L
  sourceFile : ThreadAst L
  positiveInfinity : L
  gensym : JuliaLean.base.expr.GensymOps State
  stringBytes : String → JuliaLean.base.expr.Bytes

private def astExpr {L : Type} (head : String) (args : List (ThreadAst L)) : ThreadAst L :=
  .expr head args
private def astSym {L : Type} (name : String) : ThreadAst L := .symbol name
private def astCall {L : Type} (callee : ThreadAst L) (args : List (ThreadAst L)) : ThreadAst L :=
  .expr "call" (callee :: args)
private def astAssign {L : Type} (lhs rhs : ThreadAst L) : ThreadAst L := .expr "=" [lhs, rhs]
private def astBlock {L : Type} (body : List (ThreadAst L)) : ThreadAst L := .expr "block" body
private def astLocal {L : Type} (binding : ThreadAst L) : ThreadAst L := .expr "local" [binding]
private def astLet {L : Type} (bindings : List (ThreadAst L)) (body : ThreadAst L) : ThreadAst L :=
  match bindings with
  | [binding] => .expr "let" [binding, body]
  | _ => .expr "let" [astBlock bindings, body]
private def astIf {L : Type} (condition yes no : ThreadAst L) : ThreadAst L :=
  .expr "if" [condition, yes, no]
private def astIfNoElse {L : Type} (condition body : ThreadAst L) : ThreadAst L :=
  .expr "if" [condition, body]
private def astFor {L : Type} (varName iterator body : ThreadAst L) : ThreadAst L :=
  .expr "for" [astAssign varName iterator, body]
private def astFunction {L : Type} (name : String) (args : List (ThreadAst L))
    (body : ThreadAst L) : ThreadAst L :=
  .expr "function" [astCall (.symbol name) args, body]
private def astBaseGlobal {L State : Type} (ops : ThreadExprOps L State) (name : String) : ThreadAst L :=
  .globalRef ops.leaves.base name
private def astCoreGlobal {L State : Type} (ops : ThreadExprOps L State) (name : String) : ThreadAst L :=
  .globalRef ops.coreModule name
private def astThreadsGlobal {L State : Type} (ops : ThreadExprOps L State) (name : String) : ThreadAst L :=
  .globalRef ops.threadingModule name
private def astBaseCall {L State : Type} (ops : ThreadExprOps L State) (name : String)
    (args : List (ThreadAst L)) : ThreadAst L := astCall (astBaseGlobal ops name) args
private def astCoreCall {L State : Type} (ops : ThreadExprOps L State) (name : String)
    (args : List (ThreadAst L)) : ThreadAst L := astCall (astCoreGlobal ops name) args
private def astThreadsCall {L State : Type} (ops : ThreadExprOps L State) (name : String)
    (args : List (ThreadAst L)) : ThreadAst L := astCall (astThreadsGlobal ops name) args
private def astBool {L State : Type} (ops : ThreadExprOps L State) (value : Bool) : ThreadAst L :=
  .leaf (ops.leaves.ofBool value)
private def astInt {L State : Type} (ops : ThreadExprOps L State) (value : Int) : ThreadAst L :=
  .leaf (ops.leaves.ofInt (JuliaLean.base.expr.i64 value))
private def astIsTrue {L State : Type} (ops : ThreadExprOps L State) (value : ThreadAst L) : Bool :=
  match value with
  | .leaf leaf => ops.leaves.asBool leaf == some true
  | _ => false
private def astInbounds {L State : Type} (ops : ThreadExprOps L State) (line : Nat)
    (expression : ThreadAst L) : ThreadAst L :=
  .expr "macrocall" [
    .globalRef ops.leaves.base "@inbounds",
    .lineNumberNode (JuliaLean.base.expr.i64 (Int.ofNat line)) ops.sourceFile,
    expression]
private def astRange {L : Type} (first last : ThreadAst L) : ThreadAst L :=
  astCall (.symbol "colon") [first, last]
private def astTuple {L : Type} (values : List (ThreadAst L)) : ThreadAst L := .expr "tuple" values
private def astRef {L : Type} (array index : ThreadAst L) : ThreadAst L := .expr "ref" [array, index]

-- Source: base/threadingconstructs.jl:1-35 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- export threadid, nthreads, @threads, @spawn,
--        threadpool, nthreadpools
-- 
-- public Condition, threadpoolsize, ngcthreads
-- 
-- """
--     Threads.threadid([t::Task])::Int
-- 
-- Get the ID number of the current thread of execution, or the thread of task
-- `t`. The master thread has ID `1`.
-- 
-- # Examples
-- ```julia-repl
-- julia> Threads.threadid()
-- 1
-- 
-- julia> Threads.@threads for i in 1:4
--           println(Threads.threadid())
--        end
-- 4
-- 2
-- 5
-- 4
-- 
-- julia> Threads.threadid(Threads.@spawn "foo")
-- 2
-- ```
-- 
-- !!! note
--     The thread that a task runs on may change if the task yields, which is known as [`Task Migration`](@ref man-task-migration).
--     For this reason in most cases it is not safe to use `threadid([task])` to index into, say, a vector of buffers or stateful
--     objects.
-- """
-- /Source

-- Source: base/threadingconstructs.jl:37-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # lower bound on the largest threadid()
-- """
--     Threads.maxthreadid()::Int
-- 
-- Get a lower bound on the number of threads (across all thread pools) available
-- to the Julia process, with atomic-acquire semantics. The result will always be
-- greater than or equal to [`threadid()`](@ref) as well as `threadid(task)` for
-- any task you were able to observe before calling `maxthreadid`.
-- """
-- /Source

-- Source: base/threadingconstructs.jl:48-59 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Threads.nthreads(:default | :interactive)::Int
-- 
-- Get the current number of threads within the specified thread pool. The threads in `:interactive`
-- have id numbers `1:nthreads(:interactive)`, and the threads in `:default` have id numbers in
-- `nthreads(:interactive) .+ (1:nthreads(:default))`.
-- 
-- See also `BLAS.get_num_threads` and `BLAS.set_num_threads` in the [`LinearAlgebra`](@ref
-- man-linalg) standard library, and `nprocs()` in the [`Distributed`](@ref man-distributed)
-- standard library and [`Threads.maxthreadid()`](@ref).
-- """
-- /Source

-- Source: base/threadingconstructs.jl:61-61 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/threadingconstructs.jl:66-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/threadingconstructs.jl:78-78 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/threadingconstructs.jl:90-95 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Threads.threadpool(tid = threadid())::Symbol
-- 
-- Return the specified thread's threadpool; either `:default`, `:interactive`, or `:foreign`.
-- """
-- /Source

-- Source: base/threadingconstructs.jl:100-105 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Threads.threadpooldescription(tid = threadid())::String
-- 
-- Return the specified thread's threadpool name with extended description where appropriate.
-- """
-- /Source

-- Source: base/threadingconstructs.jl:118-123 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Threads.nthreadpools()::Int
-- 
-- Return the number of threadpools currently configured.
-- """
-- /Source

-- Source: base/threadingconstructs.jl:125-135 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Threads.threadpoolsize(pool::Symbol = :default)::Int
-- 
-- Get the number of threads available to the default thread pool (or to the
-- specified thread pool).
-- 
-- See also: `BLAS.get_num_threads` and `BLAS.set_num_threads` in the
-- [`LinearAlgebra`](@ref man-linalg) standard library, and `nprocs()` in the
-- [`Distributed`](@ref man-distributed) standard library.
-- """
-- /Source

-- Source: base/threadingconstructs.jl:146-151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     threadpooltids(pool::Symbol)
-- 
-- Return a vector of IDs of threads in the given pool.
-- """
-- /Source

-- Source: base/threadingconstructs.jl:162-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Threads.ngcthreads()::Int
-- 
-- Return the number of GC threads currently configured.
-- This includes both mark threads and concurrent sweep threads.
-- """
-- /Source

-- Source: base/threadingconstructs.jl:170-181 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # `fun` is captured by the scope closure and, inside it, by every task closure. Lowering
-- # only keeps a `@nospecialize` argument untyped for a direct capture (#58426), not for the
-- # nested one, so hold it in a struct with an untyped field. Then the closures and the runner
-- # have the same types at every `@threads` site and compile once into the sysimage.
-- # The cost is one dynamic dispatch per task at start.
-- struct _ThreadsFun
--     fun
-- end
-- 
-- # Isolate the dynamic dispatch so that `--trim` checks the loop body at each call of the
-- # runner, where its type is known. The runner must stay out of line for that call to exist.
-- /Source

-- Source: base/threadingconstructs.jl:183-183 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/threadingconstructs.jl:252-256 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Helper to generate the threading run call. Keep the expansion free of `ccall`s: a
-- # foreigncall in a top-level thunk forces the whole thunk through codegen, even under
-- # `--compile=min`, so a top-level `@threads` would otherwise make the interpreter
-- # unusable for everything around it.
-- /Source

-- Source: base/threadingconstructs.jl:260-260 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/threadingconstructs.jl:277-277 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/threadingconstructs.jl:300-300 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/threadingconstructs.jl:327-330 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # A one-argument function computing the body, so that a destructuring loop variable such as
-- # `(a, b)` becomes a destructuring argument rather than two arguments. It is all user code,
-- # so it is escaped as a whole.
-- /Source

-- Source: base/threadingconstructs.jl:332-336 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # The element type inferred for the serial comprehension over `iter`, as `collect` infers it
-- # before widening unions, so that every result fits and an empty result gets the serial type.
-- # `pred` is the filter function, or `true` without a filter. The serial iterator is built as
-- # lowering builds it, only for its type.
-- /Source

-- Source: base/threadingconstructs.jl:343-345 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # The filter as a separate function of the item, as in a serial comprehension, so that an
-- # assignment to the loop variable in the condition does not reach the body.
-- /Source

-- Source: base/threadingconstructs.jl:349-350 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Add the results for one item to `dest` with `add!` (`push!` or `put!`).
-- /Source

-- Source: base/threadingconstructs.jl:353-355 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Give an untyped comprehension result the element type a serial comprehension would have.
-- # `ET` is the inferred element type the result was allocated with.
-- /Source

-- Source: base/threadingconstructs.jl:365-367 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Widen `T` over the elements from linear index `i` on, as a serial `collect` does. The scan
-- # is specialized on `T`, so `el isa T` stays cheap, and restarts only when `T` widens.
-- /Source

-- Source: base/threadingconstructs.jl:375-375 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/threadingconstructs.jl:390-394 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Fast path for non-filtered, non-greedy comprehensions: pre-allocate and write directly.
-- # Non-AbstractArray iterators (e.g. Iterators.flatten) are collected into an array
-- # because the parallel work distribution indexes into items with r[i].
-- # AbstractArrays and Tuples are used directly to preserve their index space (e.g. OffsetArrays).
-- /Source

-- Source: base/threadingconstructs.jl:425-426 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- 
-- /Source

-- Source: base/threadingconstructs.jl:443-443 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/threadingconstructs.jl:482-483 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Helper function to generate work distribution code
-- /Source

-- Source: base/threadingconstructs.jl:512-512 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/threadingconstructs.jl:528-528 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/threadingconstructs.jl:566-788 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Threads.@threads [schedule] for ... end
--     Threads.@threads [schedule] [expr for ... end]
--     Threads.@threads [schedule] T[expr for ... end]
-- 
-- A macro to execute a `for` loop or array comprehension in parallel. The iteration space is distributed to
-- coarse-grained tasks. This policy can be specified by the `schedule` argument. The
-- execution of the loop waits for the evaluation of all iterations.
-- 
-- For `for` loops, the macro executes the loop body in parallel but does not return a value.
-- For array comprehensions, the macro executes the comprehension in parallel and returns
-- the collected results as an array.
-- 
-- Tasks spawned by `@threads` are scheduled on the `:default` threadpool. This means that
-- `@threads` will not use threads from the `:interactive` threadpool, even if called from
-- the main thread or from a task in the interactive pool. The `:default` threadpool is
-- intended for compute-intensive parallel workloads.
-- 
-- See also: [`@spawn`](@ref Threads.@spawn) and
-- `pmap` in [`Distributed`](@ref man-distributed).
-- For more information on threadpools, see the chapter on [threadpools](@ref man-threadpools).
-- 
-- # Extended help
-- 
-- ## Semantics
-- 
-- Unless stronger guarantees are specified by the scheduling option, the loop executed by
-- `@threads` macro have the following semantics.
-- 
-- The `@threads` macro executes the loop body in an unspecified order and potentially
-- concurrently. It does not specify the exact assignments of the tasks and the worker threads.
-- The assignments can be different for each execution. The loop body code (including any code
-- transitively called from it) must not make any assumptions about the distribution of
-- iterations to tasks or the worker thread in which they are executed. The loop body for each
-- iteration must be able to make forward progress independent of other iterations and be free
-- from data races. As such, invalid synchronizations across iterations may deadlock while
-- unsynchronized memory accesses may result in undefined behavior.
-- 
-- For example, the above conditions imply that:
-- 
-- - A lock taken in an iteration *must* be released within the same iteration.
-- - Communicating between iterations using blocking primitives like `Channel`s is incorrect.
-- - Write only to locations not shared across iterations (unless a lock or atomic operation is
--   used).
-- - Unless the `:static` schedule is used, the value of [`threadid()`](@ref Threads.threadid)
--   may change even within a single iteration. See [`Task Migration`](@ref man-task-migration).
-- 
-- !!! note
--     The number of tasks created by `@threads` depends on the number of threads. Since each
--     task has its own random number stream (see `Random.TaskLocalRNG`), results that use the
--     default random number generator can change with the number of threads, even when it is
--     seeded (and with the `:greedy` scheduler, they can also vary between runs). For results
--     that do not depend on the number of threads, spawn one task per iteration (e.g.
--     `@sync for x in xs; Threads.@spawn f(x); end`) or use a separate, explicitly seeded
--     random number generator for each iteration.
-- 
-- ## Schedulers
-- 
-- Without the scheduler argument, the exact scheduling is unspecified and varies across Julia
-- releases. Currently, `:dynamic` is used when the scheduler is not specified.
-- 
-- !!! compat "Julia 1.5"
--     The `schedule` argument is available as of Julia 1.5.
-- 
-- ### `:dynamic` (default)
-- 
-- `:dynamic` scheduler executes iterations dynamically to available worker threads. Current
-- implementation assumes that the workload for each iteration is uniform. However, this
-- assumption may be removed in the future.
-- 
-- This scheduling option is merely a hint to the underlying execution mechanism. However, a
-- few properties can be expected. The number of `Task`s used by `:dynamic` scheduler is
-- bounded by a small constant multiple of the number of available worker threads
-- ([`Threads.threadpoolsize()`](@ref)). Each task processes contiguous regions of the
-- iteration space. Thus, `@threads :dynamic for x in xs; f(x); end` is typically more
-- efficient than `@sync for x in xs; @spawn f(x); end` if `length(xs)` is significantly
-- larger than the number of the worker threads and the run-time of `f(x)` is relatively
-- smaller than the cost of spawning and synchronizing a task (typically less than 10
-- microseconds).
-- 
-- !!! compat "Julia 1.8"
--     The `:dynamic` option for the `schedule` argument is available and the default as of Julia 1.8.
-- 
-- ### `:greedy`
-- 
-- `:greedy` scheduler spawns up to [`Threads.threadpoolsize()`](@ref) tasks, each greedily working on
-- the given iterated values as they are produced. As soon as one task finishes its work, it takes
-- the next value from the iterator. Work done by any individual task is not necessarily on
-- contiguous values from the iterator. The given iterator may produce values forever, only the
-- iterator interface is required (no indexing).
-- 
-- This scheduling option is generally a good choice if the workload of individual iterations
-- is not uniform/has a large spread.
-- 
-- !!! compat "Julia 1.11"
--     The `:greedy` option for the `schedule` argument is available as of Julia 1.11.
-- 
-- ### `:static`
-- 
-- `:static` scheduler creates one task per thread and divides the iterations equally among
-- them, assigning each task specifically to each thread. In particular, the value of
-- [`threadid()`](@ref Threads.threadid) is guaranteed to be constant within one iteration.
-- Specifying `:static` is an error if used from inside another `@threads` loop or from a
-- thread other than 1.
-- 
-- !!! note
--     `:static` scheduling exists for supporting transition of code written before Julia 1.3.
--     In newly written library functions, `:static` scheduling is discouraged because the
--     functions using this option cannot be called from arbitrary worker threads.
-- 
-- ## Examples
-- 
-- ### For loops
-- 
-- To illustrate of the different scheduling strategies, consider the following function
-- `busywait` containing a non-yielding timed loop that runs for a given number of seconds.
-- 
-- ```julia-repl
-- julia> function busywait(seconds)
--             tstart = time_ns()
--             while (time_ns() -% tstart) / 1e9 < seconds
--             end
--         end
-- 
-- julia> @time begin
--             Threads.@spawn busywait(5)
--             Threads.@threads :static for i in 1:Threads.threadpoolsize()
--                 busywait(1)
--             end
--         end
-- 6.003001 seconds (16.33 k allocations: 899.255 KiB, 0.25% compilation time)
-- 
-- julia> @time begin
--             Threads.@spawn busywait(5)
--             Threads.@threads :dynamic for i in 1:Threads.threadpoolsize()
--                 busywait(1)
--             end
--         end
-- 2.012056 seconds (16.05 k allocations: 883.919 KiB, 0.66% compilation time)
-- ```
-- 
-- The `:dynamic` example takes 2 seconds since one of the non-occupied threads is able
-- to run two of the 1-second iterations to complete the for loop.
-- 
-- ### Array comprehensions
-- 
-- The `@threads` macro also supports array comprehensions, which return the collected results.
-- The result has the same element type and shape as the serial comprehension. Array
-- comprehensions preserve element order for `:static` and `:dynamic` (default) scheduling.
-- The `:greedy` scheduler does not guarantee element order, since tasks consume work items as
-- they become available. Multi-dimensional comprehensions preserve the dimensions of the
-- original comprehension (e.g., `[f(i,j) for i in 1:n, j in 1:m]` returns an `n×m` matrix).
-- Typed comprehensions (`T[expr for ...]`) are also supported and return an array with the
-- specified element type. In a comprehension with several `for` clauses, such as
-- `[f(i,j) for i in 1:n for j in 1:i]`, the work is divided over the outermost iterator.
-- 
-- A comprehension with one `for` clause and no filter, scheduled with `:static` or `:dynamic`,
-- writes into a pre-allocated result, which is the fastest form.
-- 
-- !!! tip "Performance tip"
--     For best performance, use typed comprehensions (`T[expr for ...]`) when the element type
--     is known. Untyped comprehensions use the compiler's inferred element type; if that is not
--     a concrete type, the results are copied to the element type a serial comprehension
--     would produce, which may be slower.
-- 
-- !!! warning
--     The body expression of a threaded comprehension may execute on any thread and may
--     migrate between threads. Do not rely on [`threadid()`](@ref Threads.threadid) or
--     [`task_local_storage()`](@ref) returning consistent values within the body expression.
-- 
-- ```julia-repl
-- julia> Threads.@threads [i^2 for i in 1:5] # Simple comprehension
-- 5-element Vector{Int64}:
--    1
--    4
--    9
--   16
--   25
-- 
-- julia> Threads.@threads [i^2 for i in 1:5 if iseven(i)] # Filtered comprehension
-- 2-element Vector{Int64}:
--    4
--   16
-- 
-- julia> Threads.@threads [i + j for i in 1:3, j in 1:3] # Multiple loops
-- 3×3 Matrix{Int64}:
--  2  3  4
--  3  4  5
--  4  5  6
-- 
-- julia> Threads.@threads Float64[i^2 for i in 1:5] # Typed comprehension
-- 5-element Vector{Float64}:
--   1.0
--   4.0
--   9.0
--  16.0
--  25.0
-- ```
-- 
-- When the iterator doesn't have a known length, such as a channel, the `:greedy` scheduling
-- option can be used.
-- ```julia-repl
-- julia> c = Channel(5, spawn=true) do ch
--            foreach(i -> put!(ch, i), 1:5)
--        end;
-- 
-- julia> Threads.@threads :greedy [i^2 for i in c if iseven(i)]
-- 2-element Vector{Int64}:
--   4
--  16
-- 
-- julia> # Non-indexable iterators are also supported
--        Threads.@threads [i for i in Iterators.flatten([1:3, 4:6])]
-- 6-element Vector{Int64}:
--  1
--  2
--  3
--  4
--  5
--  6
-- ```
-- """
-- /Source

-- Source: base/threadingconstructs.jl:825-825 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/threadingconstructs.jl:835-879 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Threads.@spawn [:default|:interactive|:samepool] expr
-- 
-- Create a [`Task`](@ref) and [`schedule`](@ref) it to run on any available
-- thread in the specified threadpool: `:default`, `:interactive`, or `:samepool`
-- to use the same as the caller. `:default` is used if unspecified. The task is
-- allocated to a thread once one becomes available. To wait for the task to
-- finish, call [`wait`](@ref) on the result of this macro, or call
-- [`fetch`](@ref) to wait and then obtain its return value.
-- 
-- Values can be interpolated into `@spawn` via `\$`, which copies the value
-- directly into the constructed underlying closure. This allows you to insert
-- the _value_ of a variable, isolating the asynchronous code from changes to
-- the variable's value in the current task.
-- 
-- !!! note
--     The thread that the task runs on may change if the task yields, therefore `threadid()` should not
--     be treated as constant for a task. See [`Task Migration`](@ref man-task-migration), and the broader
--     [multi-threading](@ref man-multithreading) manual for further important caveats.
--     See also the chapter on [threadpools](@ref man-threadpools).
-- 
-- !!! compat "Julia 1.3"
--     This macro is available as of Julia 1.3.
-- 
-- !!! compat "Julia 1.4"
--     Interpolating values via `\$` is available as of Julia 1.4.
-- 
-- !!! compat "Julia 1.9"
--     A threadpool may be specified as of Julia 1.9.
-- 
-- !!! compat "Julia 1.12"
--     The same threadpool may be specified as of Julia 1.12.
-- 
-- # Examples
-- ```julia-repl
-- julia> t() = println("Hello from ", Threads.threadid());
-- 
-- julia> tasks = fetch.([Threads.@spawn t() for i in 1:4]);
-- Hello from 1
-- Hello from 1
-- Hello from 3
-- Hello from 4
-- ```
-- """
-- /Source

-- Source: base/threadingconstructs.jl:921-928 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # This is a stub that can be overloaded for downstream structures like `Channel`
-- function foreach end
-- 
-- # Scheduling traits that can be employed for downstream overloads
-- abstract type AbstractSchedule end
-- struct StaticSchedule <: AbstractSchedule end
-- struct FairSchedule <: AbstractSchedule end
-- /Source

/--
Julia source: base/threadingconstructs.jl:36-36 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
threadid() = Int(ccall(:jl_threadid, Int16, ())+1)
```
-/
def threadid {E W : Type} (r : Queries E W) : M E W I := do
  pure (int ((← r.threadId).val + 1))

/--
Julia source: base/threadingconstructs.jl:47-47 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
maxthreadid() = Int(unsafe_load(cglobal(:jl_n_threads, Cint), :acquire))
```
-/
def maxthreadid {E W : Type} (r : Queries E W) : M E W I := do
  pure (int (← r.maxThreadId .acquire).val)

/--
Julia source: base/threadingconstructs.jl:62-65 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _nthreads_in_pool(tpid::Int8)
    p = unsafe_load(cglobal(:jl_n_threads_per_pool, Ptr{Cint}))
    return Int(unsafe_load(p, tpid + 1))
end
```
-/
def nthreadsInPool {E W : Type} (r : Queries E W) (tpid : I8) : M E W I := do
  let pointer ← r.poolCounts
  pure (int (← r.loadPoolCount pointer (int (tpid.val + 1))).val)

/--
Julia source: base/threadingconstructs.jl:67-77 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _tpid_to_sym(tpid::Int8)
    if tpid == 0
        return :interactive
    elseif tpid == 1
        return :default
    elseif tpid == -1
        return :foreign
    else
        throw(ArgumentError(LazyString("Unrecognized threadpool id ", tpid)))
    end
end
```
-/
def tpidToSym {E : Type} (argumentError : String → E) (tpid : I8) : Except E Pool :=
  if tpid.val == 0 then .ok .interactive
  else if tpid.val == 1 then .ok .default
  else if tpid.val == -1 then .ok .foreign
  else .error (argumentError ("Unrecognized threadpool id " ++ toString tpid.val))

/--
Julia source: base/threadingconstructs.jl:79-89 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _sym_to_tpid(tp::Symbol)
    if tp === :interactive
        return Int8(0)
    elseif tp === :default
        return Int8(1)
    elseif tp == :foreign
        return Int8(-1)
    else
        throw(ArgumentError(LazyString("Unrecognized threadpool name `", tp, "`")))
    end
end
```
-/
def symToTpid {E : Type} (argumentError : String → E) (pool : Pool) : Except E I8 :=
  match pool with
  | .interactive => .ok (JInt.wrap .i8 0)
  | .default => .ok (JInt.wrap .i8 1)
  | .foreign => .ok (JInt.wrap .i8 (-1))
  | .other name => .error (argumentError ("Unrecognized threadpool name `" ++ name ++ "`"))

/--
Julia source: base/threadingconstructs.jl:96-99 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function threadpool(tid = threadid())
    tpid = ccall(:jl_threadpoolid, Int8, (Int16,), tid-1)
    return _tpid_to_sym(tpid)
end
```
-/
def threadpool {E W : Type} (r : Queries E W) (tid : Option I := none) : M E W Pool := do
  let tid ← match tid with | some tid => pure tid | none => threadid r
  let ctid ← liftResult ((JInt.convert "Int16" .i16 (tid - int 1).val).mapError r.juliaError)
  let tpid ← r.threadPoolId ctid
  liftResult (tpidToSym r.argumentError tpid)

/--
Julia source: base/threadingconstructs.jl:124-124 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
nthreadpools() = Int(unsafe_load(cglobal(:jl_n_threadpools, Cint)))
```
-/
def nthreadpools {E W : Type} (r : Queries E W) : M E W I := do
  pure (int (← r.threadPoolCount).val)

/--
Julia source: base/threadingconstructs.jl:136-145 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function threadpoolsize(pool::Symbol = :default)
    if pool === :default || pool === :interactive
        tpid = _sym_to_tpid(pool)
    elseif pool == :foreign
        error("Threadpool size of `:foreign` is indeterminant")
    else
        error("invalid threadpool specified")
    end
    return _nthreads_in_pool(tpid)
end
```
-/
def threadpoolsize {E W : Type} (r : Queries E W) (pool : Pool := .default) : M E W I := do
  let tpid ← match pool with
    | .interactive | .default => liftResult (symToTpid r.argumentError pool)
    | .foreign => throw (r.error "Threadpool size of `:foreign` is indeterminant")
    | .other _ => throw (r.error "invalid threadpool specified")
  nthreadsInPool r tpid

/--
Julia source: base/threadingconstructs.jl:60-60 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
nthreads(pool::Symbol) = threadpoolsize(pool)
```
-/
def nthreads {E W : Type} (r : Queries E W) (pool : Pool) : M E W I :=
  threadpoolsize r pool

/--
Julia source: base/threadingconstructs.jl:152-161 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function threadpooltids(pool::Symbol)
    ni = _nthreads_in_pool(Int8(0))
    if pool === :interactive
        return collect(1:ni)
    elseif pool === :default
        return collect(ni+1:ni+_nthreads_in_pool(Int8(1)))
    else
        error("invalid threadpool specified")
    end
end
```
-/
def threadpooltids {E W : Type} (r : Queries E W) (pool : Pool) : M E W (List I) := do
  let ni ← nthreadsInPool r (JInt.wrap .i8 0)
  match pool with
  | .interactive => r.collectRange (int 1) ni
  | .default =>
    let nd ← nthreadsInPool r (JInt.wrap .i8 1)
    r.collectRange (ni + int 1) (ni + nd)
  | _ => throw (r.error "invalid threadpool specified")

/--
Julia source: base/threadingconstructs.jl:169-169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ngcthreads() = Int(unsafe_load(cglobal(:jl_n_gcthreads, Cint))) + 1
```
-/
def ngcthreads {E W : Type} (r : Queries E W) : M E W I := do
  pure (int (← r.gcThreadCount).val + int 1)

/--
Julia source: base/threadingconstructs.jl:106-117 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function threadpooldescription(tid = threadid())
    threadpool_name = threadpool(tid)
    if threadpool_name == :foreign
        # TODO: extend tls to include a field to add a description to a foreign thread and make this more general
        n_others = nthreads(:interactive) + nthreads(:default)
        # Assumes GC threads come first in the foreign thread pool
        if tid > n_others && tid <= n_others + ngcthreads()
            return "foreign: gc"
        end
    end
    return string(threadpool_name)
end
```
-/
def threadpooldescription {E W : Type} (r : Queries E W) (tid : Option I := none) : M E W String := do
  let tid ← match tid with | some tid => pure tid | none => threadid r
  let pool ← threadpool r (some tid)
  if pool == .foreign then
    let others := (← nthreads r .interactive) + (← nthreads r .default)
    if tid.val > others.val then
      let gc ← ngcthreads r
      if tid.val ≤ (others + gc).val then return "foreign: gc"
  pure pool.name

/--
Julia source: base/threadingconstructs.jl:182-182 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline _threads_call(tfun::_ThreadsFun, i::Int) = tfun.fun(i)
```
-/
def threadsCall {E W V : Type} (f : ThreadsFun (I → M E W V)) (i : I) : M E W V := f.callable i

/--
Julia source: base/threadingconstructs.jl:826-834 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _spawn_set_thrpool(t::Task, tp::Symbol)
    tpid = _sym_to_tpid(tp)
    if tpid == -1 || _nthreads_in_pool(tpid) == 0
        tpid = _sym_to_tpid(:default)
    end
    _result = ccall(:jl_set_task_threadpoolid, Cint, (Any, Int8), t, tpid)
    @assert _result == 1 "_result != 1"
    nothing
end
```
-/
def spawnSetThreadpool {E W Task Tasks Source Token V : Type}
    (r : Scheduler E W Task Tasks Source Token V) (task : Task) (pool : Pool) : M E W Unit := do
  let mut tpid ← liftResult (symToTpid r.queries.argumentError pool)
  if tpid.val == -1 then
    tpid ← liftResult (symToTpid r.queries.argumentError .default)
  else if (← nthreadsInPool r.queries tpid).val == 0 then
    tpid ← liftResult (symToTpid r.queries.argumentError .default)
  let result ← r.setTaskThreadPoolId task tpid
  if result.val != 1 then throw (r.assertionError "_result != 1")

/--
Julia source: base/threadingconstructs.jl:368-374 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _comprehension_widened_eltype(result::AbstractArray, ::Type{T}, i::Int) where T
    for j in i:lastindex(result)
        el = @inbounds result[j]
        el isa T || return _comprehension_widened_eltype(result, Base.promote_typejoin(T, typeof(el)), j + 1)
    end
    return T
end
```
-/
def comprehensionWidenedEltype {E W Arr V Ty : Type}
    (r : Comprehension E W Arr V Ty) (array : Arr) (initialType : Ty) (first : I) : M E W Ty :=
  loop (fun (state : Ty × I) => do
    let last ← r.lastIndex array
    let result ← loop (fun index => do
      if index.val > last.val then return .inl (Sum.inl state.1)
      let value ← r.getInbounds array index
      if !(r.isa value state.1) then
        let widened ← r.promoteTypejoin state.1 (r.typeOf value)
        return .inl (Sum.inr (widened, index + int 1))
      if index.val == last.val then return .inl (Sum.inl state.1)
      pure (.inr (index + int 1))) state.2
    pure result) (initialType, first)

/--
Julia source: base/threadingconstructs.jl:356-364 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _comprehension_result(result::AbstractArray, @nospecialize(ET))
    if isempty(result)
        T = Base.promote_typejoin_union(ET)
        return eltype(result) === T ? result : similar(result, T)
    end
    isconcretetype(ET) && return result
    T = _comprehension_widened_eltype(result, typeof(first(result)), firstindex(result) + 1)
    return eltype(result) === T ? result : copyto!(similar(result, T), result)
end
```
-/
def comprehensionResult {E W Arr V Ty : Type}
    (r : Comprehension E W Arr V Ty) (array : Arr) (elementType : Ty) : M E W Arr := do
  if ← r.isEmpty array then
    let t ← r.promoteTypejoinUnion elementType
    if r.sameType (← r.elementType array) t then return array
    return ← r.similar array t
  if r.concreteType elementType then return array
  let t ← comprehensionWidenedEltype r array (r.typeOf (← r.first array)) ((← r.firstIndex array) + int 1)
  if r.sameType (← r.elementType array) t then return array
  r.copyTo (← r.similar array t) array

/--
Julia source: base/threadingconstructs.jl:184-251 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline Base.@nospecializeinfer function threading_run(@nospecialize(fun), static::Bool)
    tfun = _ThreadsFun(fun)
    if static && ccall(:jl_in_threaded_region, Cint, ()) != 0
        error("`@threads :static` cannot be used concurrently or nested")
    end
    ccall(:jl_enter_threaded_region, Cvoid, ())
    n = threadpoolsize()
    tid_offset = threadpoolsize(:interactive)
    tasks = Vector{Task}(undef, n)
    # The workers run in a new dynamic scope carrying the token of a fresh
    # cancellation source, so that cancellation of the enclosing scope reaches
    # every worker through the token tree.
    src = Base.CancellationTokenSource(Base.default_cancel_token())
    tok = Base.CancellationToken(src)
    cr = nothing
    try
        Base.ScopedValues.with(Base.CANCEL_TOKEN => tok) do
            for i = 1:n
                t = Task(() -> _threads_call(tfun, i)) # pass in tid
                t.sticky = static
                if static
                    ccall(:jl_set_task_tid, Cint, (Any, Cint), t, tid_offset + i-1)
                else
                    # TODO: this should be the current pool (except interactive) if there
                    # are ever more than two pools.
                    _result = ccall(:jl_set_task_threadpoolid, Cint, (Any, Int8), t, _sym_to_tpid(:default))
                    @assert _result == 1 "_result != 1"
                end
                tasks[i] = t
                schedule(t)
            end
        end
        for i = 1:n
            r = Base._wait(tasks[i], tok; cancel_value=true)
            if r isa Base.CancellationRequest
                # Our own scope was cancelled; the workers observe the same
                # cancellation through the tree. Await their unwind rather
                # than unwinding out of the `@threads` while workers are
                # still running; a severity escalation completes these
                # teardown waits (value-mode) and is adopted, re-arming
                # them (at ABANDON_ALL the workers were frozen; nothing to
                # wait for).
                cr = r
                sev = Base.severity(r)
                for j = i:n
                    while sev < Base.CANCEL_REQUEST_ABANDON_ALL.request
                        r2 = Base._wait(tasks[j], tok; min_severity=sev + 0x01,
                                        cancel_value=true)
                        r2 isa Base.CancellationRequest || break
                        cr = r2
                        sev = Base.severity(r2)
                    end
                end
                break
            end
        end
    finally
        ccall(:jl_exit_threaded_region, Cvoid, ())
    end
    failed_tasks = filter!(istaskfailed, tasks)
    if !isempty(failed_tasks)
        throw(CompositeException(map(TaskFailedException, failed_tasks)))
    end
    # The block's scope was cancelled but every worker happened to complete
    # cleanly - the request must still surface at this cancellation-aware
    # boundary rather than be swallowed.
    cr === nothing || throw(cr)
end
```
-/
def threadingRun {E W Task Tasks Source Token V : Type}
    (r : Scheduler E W Task Tasks Source Token V) (f : I → M E W V) (static : Bool) : M E W Unit := do
  let tfun : ThreadsFun (I → M E W V) := ⟨f⟩
  if static then
    if (← r.inThreadedRegion).val != 0 then
      throw (r.queries.error "`@threads :static` cannot be used concurrently or nested")
  r.enterThreadedRegion
  let n ← threadpoolsize r.queries
  let offset ← threadpoolsize r.queries .interactive
  let tasks ← r.newTaskVector n
  let source ← r.newCancellationSource (← r.defaultCancelToken)
  let token := r.cancellationToken source
  runFrame (none : Option UInt8) do
    finallyDo (do
      liftFrame (r.withToken token (forRange (int 1) n (fun i => do
        let t ← r.newTask (threadsCall tfun i)
        r.setSticky t static
        if static then
          let _ ← r.setTaskThreadId t (offset + i - int 1)
        else
          let tpid ← liftResult (symToTpid r.queries.argumentError .default)
          let result ← r.setTaskThreadPoolId t tpid
          if result.val != 1 then throw (r.assertionError "_result != 1")
        r.setTask tasks i t
        r.schedule t)))
      if n.val ≥ 1 then
        loop (fun i => do
          let t ← liftFrame (r.getTask tasks i)
          match ← liftFrame (r.waitTask t token 0 true) with
          | .completed =>
            if i.val == n.val then return .inl ()
            pure (.inr (i + int 1))
          | .cancelled severity =>
            setFrame (some severity)
            loop (fun (state : I × UInt8) => do
              let t ← liftFrame (r.getTask tasks state.1)
              let severity ← loop (fun severity => do
                if severity ≥ r.abandonAll then return .inl severity
                match ← liftFrame (r.waitTask t token (severity + 1) true) with
                | .completed => pure (.inl severity)
                | .cancelled next =>
                  setFrame (some next)
                  pure (.inr next)) state.2
              if state.1.val == n.val then return .inl ()
              pure (.inr (state.1 + int 1, severity))) (i, severity)
            pure (.inl ())) (int 1)) (liftFrame r.exitThreadedRegion)
    let failed ← liftFrame (r.filterTasks r.isTaskFailed tasks)
    if !failed.isEmpty then throw (r.compositeTaskFailures failed)
    match ← getFrame with
    | some severity => throw (r.cancellationRequest severity)
    | none => pure ()

/--
Julia source: base/threadingconstructs.jl:257-259 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _threading_run_expr(schedule)
    :(threading_run(threadsfor_fun, $(schedule === :static)))
end
```
-/
def _threading_run_expr {L State : Type} (ops : ThreadExprOps L State) (schedule : String) :
    ThreadAst L :=
  astThreadsCall ops "threading_run" [astSym "threadsfor_fun", astBool ops (schedule == "static")]

/--
Julia source: base/threadingconstructs.jl:331-331 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_comprehension_body_func(lidx, body) = esc(Expr(:->, Expr(:tuple, lidx), Expr(:block, body)))
```
-/
def _comprehension_body_func {L : Type} (lidx body : ThreadAst L) : ThreadAst L :=
  JuliaLean.base.expr.esc (astExpr "->" [astTuple [lidx], astBlock [body]])

/--
Julia source: base/threadingconstructs.jl:337-342 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _comprehension_eltype_expr(lidx, body, pred, flatten, iter)
    src = pred === true ? iter : :(Base.Filter($pred, $iter))
    gen = :(Base.Generator($(_comprehension_body_func(lidx, body)), $src))
    flatten && (gen = :(Base.Flatten($gen)))
    return :(Base._return_type(Base._iterator_upper_bound, Tuple{typeof($gen)}))
end
```
-/
def _comprehension_eltype_expr {L State : Type} (ops : ThreadExprOps L State)
    (lidx body pred : ThreadAst L) (flatten : Bool) (iter : ThreadAst L) : ThreadAst L :=
  let source := if astIsTrue ops pred then iter else astBaseCall ops "Filter" [pred, iter]
  let generated := astBaseCall ops "Generator" [_comprehension_body_func lidx body, source]
  let generated := if flatten then astBaseCall ops "Flatten" [generated] else generated
  let tupleType := astExpr "curly" [astSym "Tuple", astCoreCall ops "typeof" [generated]]
  astBaseCall ops "_return_type" [astBaseGlobal ops "_iterator_upper_bound", tupleType]

/--
Julia source: base/threadingconstructs.jl:346-347 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_comprehension_pred_expr(lidx, condition) =
    condition === true ? nothing : :(local pred = $(_comprehension_body_func(lidx, condition)))
```
-/
def _comprehension_pred_expr {L State : Type} (ops : ThreadExprOps L State)
    (lidx condition : ThreadAst L) : Option (ThreadAst L) :=
  if astIsTrue ops condition then none
  else some (astLocal (astAssign (astSym "pred") (_comprehension_body_func lidx condition)))

/--
Julia source: base/threadingconstructs.jl:348-348 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_comprehension_test_expr(condition) = condition === true ? true : :(pred(item))
```
-/
def _comprehension_test_expr {L State : Type} (ops : ThreadExprOps L State)
    (condition : ThreadAst L) : ThreadAst L :=
  if astIsTrue ops condition then astBool ops true else astCall (astSym "pred") [astSym "item"]

/--
Julia source: base/threadingconstructs.jl:351-352 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_comprehension_add_expr(add!, dest, esc_body, flatten) =
    flatten ? :(for v in $esc_body; $add!($dest, v); end) : :($add!($dest, $esc_body))
```
-/
def _comprehension_add_expr {L : Type} (add dest escapedBody : ThreadAst L) (flatten : Bool) :
    ThreadAst L :=
  if flatten then
    astFor (astSym "v") escapedBody (astBlock [astCall add [dest, astSym "v"]])
  else astCall add [dest, escapedBody]

/--
Julia source: base/threadingconstructs.jl:484-511 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _work_distribution_code()
    quote
        r = items # Load into local variable
        lenr = length(r)
        # divide loop iterations among threads
        len, rem = divrem(lenr, threadpoolsize())
        # not enough iterations for all the threads?
        if len == 0
            if tid > rem
                return
            end
            len, rem = 1, 0
        end
        # compute this thread's iterations
        loop_first = firstindex(r) + ((tid-1) * len)
        loop_last = loop_first + len - 1
        # distribute remaining iterations evenly
        if rem > 0
            if tid <= rem
                loop_first = loop_first + (tid-1)
                loop_last = loop_last + tid
            else
                loop_first = loop_first + rem
                loop_last = loop_last + rem
            end
        end
    end
end
```
-/
def _work_distribution_code {L State : Type} (ops : ThreadExprOps L State) : ThreadAst L :=
  let r := astSym "r"
  let items := astSym "items"
  let lenr := astSym "lenr"
  let len := astSym "len"
  let rem := astSym "rem"
  let tid := astSym "tid"
  let loopFirst := astSym "loop_first"
  let loopLast := astSym "loop_last"
  let one := astInt ops 1
  let zero := astInt ops 0
  let quotient := astCall (astSym "divrem") [lenr, astThreadsCall ops "threadpoolsize" []]
  let shortPartition := astBlock [
    astIfNoElse (astCall (astSym ">") [tid, rem]) (.expr "return" []),
    astAssign (astTuple [len, rem]) (astTuple [astInt ops 1, zero])]
  let remainderPartition := astIf (astCall (astSym "<=") [tid, rem])
    (astBlock [
      astAssign loopFirst (astCall (astSym "+") [loopFirst,
        astCall (astSym "-") [tid, one]]),
      astAssign loopLast (astCall (astSym "+") [loopLast, tid])])
    (astBlock [
      astAssign loopFirst (astCall (astSym "+") [loopFirst, rem]),
      astAssign loopLast (astCall (astSym "+") [loopLast, rem])])
  astBlock [
    astAssign r items,
    astAssign lenr (astBaseCall ops "length" [r]),
    astAssign (astTuple [len, rem]) quotient,
    astIfNoElse (astCall (astSym "==") [len, zero]) shortPartition,
    astAssign loopFirst (astCall (astSym "+") [astBaseCall ops "firstindex" [r],
      astCall (astSym "*") [astCall (astSym "-") [tid, one], len]]),
    astAssign loopLast (astCall (astSym "-") [astCall (astSym "+") [loopFirst, len], one]),
    astIfNoElse (astCall (astSym ">") [rem, zero]) remainderPartition]

/--
Julia source: base/threadingconstructs.jl:427-442 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function greedy_func(itr, lidx, lbody)
    quote
        let iter = $itr, c = Channel{eltype(iter)}(threadpoolsize(), spawn=true) do ch
            for item in iter
                put!(ch, item)
            end
        end
        function threadsfor_fun(tid)
            for item in c
                local $(esc(lidx)) = item
                $(esc(lbody))
            end
        end
        end
    end
end
```
-/
def greedy_func {L State : Type} (ops : ThreadExprOps L State)
    (iterator index body : ThreadAst L) : ThreadAst L :=
  let iter := astSym "iter"
  let channel := astSym "c"
  let channelType := astExpr "curly" [astBaseGlobal ops "Channel", astBaseCall ops "eltype" [iter]]
  let spawnKeyword := astExpr "parameters" [astExpr "kw" [astSym "spawn", astBool ops true]]
  let channelCall := astCall channelType [spawnKeyword, astThreadsCall ops "threadpoolsize" []]
  let channelBody := astExpr "do" [channelCall, astExpr "->" [astSym "ch",
    astBlock [astFor (astSym "item") iter (astBlock [
      astBaseCall ops "put!" [astSym "ch", astSym "item"]])]]]
  let worker := astFunction "threadsfor_fun" [astSym "tid"] (astBlock [
    astFor (astSym "item") channel (astBlock [
      astLocal (astAssign (JuliaLean.base.expr.esc index) (astSym "item")),
      JuliaLean.base.expr.esc body])])
  astLet [astAssign iter iterator, astAssign channel channelBody] (astBlock [worker])

/--
Julia source: base/threadingconstructs.jl:513-527 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function default_func(itr, lidx, lbody)
    work_dist = _work_distribution_code()
    quote
        let items = $itr
        function threadsfor_fun(tid = 1)
            # Reads: items, tid. Defines: r, loop_first, loop_last.
            $work_dist
            for i = loop_first:loop_last
                local $(esc(lidx)) = @inbounds r[i]
                $(esc(lbody))
            end
        end
        end
    end
end
```
-/
def default_func {L State : Type} (ops : ThreadExprOps L State)
    (iterator index body : ThreadAst L) : ThreadAst L :=
  let items := astSym "items"
  let loop := astFor (astSym "i") (astRange (astSym "loop_first") (astSym "loop_last")) (astBlock [
    astLocal (astAssign (JuliaLean.base.expr.esc index)
      (astInbounds ops 521 (astRef (astSym "r") (astSym "i")))),
    JuliaLean.base.expr.esc body])
  let signature := astCall (astSym "threadsfor_fun") [astExpr "kw" [astSym "tid", astInt ops 1]]
  let worker := astExpr "function" [signature, astBlock [_work_distribution_code ops, loop]]
  astLet [astAssign items iterator] (astBlock [worker])

/--
Julia source: base/threadingconstructs.jl:395-424 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _threadsfor_comprehension_fast(esc_range, lidx, body, schedule, result_type)
    esc_lidx = esc(lidx)
    esc_body = esc(body)
    work_dist = _work_distribution_code()
    ET_expr = result_type === nothing ?
        _comprehension_eltype_expr(lidx, body, true, false, :iter) : esc(result_type)
    final_expr = result_type === nothing ? :(_comprehension_result(result, _ET)) : :result
    return quote
        let iter = $esc_range
        local items = iter isa Union{Tuple, AbstractArray} ? iter : collect(iter)
        local _ET = $ET_expr
        local result = similar(Vector{_ET}, axes(items))
        if !isempty(items)
            let items = items, result = result
            local threadsfor_fun
            function threadsfor_fun(tid = 1)
                # Reads: items, tid. Defines: r, loop_first, loop_last.
                $work_dist
                for i = loop_first:loop_last
                    local $esc_lidx = @inbounds r[i]
                    @inbounds result[i] = $esc_body
                end
            end
            $(_threading_run_expr(schedule))
            end
        end
        $final_expr
        end
    end
end
```
-/
def _threadsfor_comprehension_fast {L State : Type} (ops : ThreadExprOps L State)
    (escapedRange index body : ThreadAst L) (schedule : String) (resultType : Option (ThreadAst L)) :
    ThreadAst L := Id.run do
  let escapedIndex := JuliaLean.base.expr.esc index
  let escapedBody := JuliaLean.base.expr.esc body
  let iter := astSym "iter"
  let items := astSym "items"
  let et := astSym "_ET"
  let result := astSym "result"
  let resultTypeExpr := match resultType with
    | some value => JuliaLean.base.expr.esc value
    | none => _comprehension_eltype_expr ops index body (astBool ops true) false iter
  let finalExpr := match resultType with
    | some _ => result
    | none => astCall (astSym "_comprehension_result") [result, et]
  let arrayType := astExpr "curly" [astSym "Vector", et]
  let allocated := astBaseCall ops "similar" [arrayType, astBaseCall ops "axes" [items]]
  let unionType := astExpr "curly" [astCoreGlobal ops "Union", astCoreGlobal ops "Tuple",
    astBaseGlobal ops "AbstractArray"]
  let itemsExpr := astIf (astCoreCall ops "isa" [iter, unionType]) iter
    (astBaseCall ops "collect" [iter])
  let writeLoop := astFor (astSym "i") (astRange (astSym "loop_first") (astSym "loop_last"))
    (astBlock [
      astLocal (astAssign escapedIndex (astInbounds ops 414 (astRef (astSym "r") (astSym "i")))),
      astInbounds ops 415 (astAssign (astRef result (astSym "i")) escapedBody)])
  let signature := astCall (astSym "threadsfor_fun") [astExpr "kw" [astSym "tid", astInt ops 1]]
  let worker := astExpr "function" [signature, astBlock [_work_distribution_code ops, writeLoop]]
  let threadedBody := astBlock [astLocal (astSym "threadsfor_fun"), worker,
    _threading_run_expr ops schedule]
  let nonempty := astLet [astAssign items items, astAssign result result] threadedBody
  let resultBody := astBlock [
    astLocal (astAssign items itemsExpr),
    astLocal (astAssign et resultTypeExpr),
    astLocal (astAssign result allocated),
    astIfNoElse (astCall (astSym "!") [astBaseCall ops "isempty" [items]]) nonempty,
    finalExpr]
  return astLet [astAssign iter escapedRange] resultBody

/--
Julia source: base/threadingconstructs.jl:444-481 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function greedy_comprehension_expr(esc_range, lidx, body, condition, schedule, result_type, flatten)
    esc_lidx = esc(lidx)
    esc_body = esc(body)
    pred = condition === true ? true : :pred
    ET_expr = result_type === nothing ?
        _comprehension_eltype_expr(lidx, body, pred, flatten, :iter) : esc(result_type)
    vals_expr = result_type === nothing ?
        :(_comprehension_result(collect(result_channel), _ET)) : :(collect(result_channel))
    # With one result per item, the result has the shape of the iterator as in a serial
    # comprehension, although the elements are in arrival order.
    shape_expr = !flatten && condition === true ?
        :(Base.IteratorSize(iter) isa Base.HasShape ? reshape(vals, axes(iter)) : vals) : :vals
    quote
        let iter = $esc_range
            $(_comprehension_pred_expr(lidx, condition))
            local _ET = $ET_expr
            local c = Channel{eltype(iter)}(threadpoolsize(), spawn=true) do ch
                for item in iter
                    put!(ch, item)
                end
            end
            local result_channel = Channel{_ET}(Inf)
            local threadsfor_fun
            function threadsfor_fun(tid)
                for item in c
                    if $(_comprehension_test_expr(condition))
                        local $esc_lidx = item
                        $(_comprehension_add_expr(:put!, :result_channel, esc_body, flatten))
                    end
                end
            end
            $(_threading_run_expr(schedule))
            close(result_channel)
            local vals = $vals_expr
            $shape_expr
        end
    end
end
```
-/
def greedy_comprehension_expr {L State : Type} (ops : ThreadExprOps L State)
    (escapedRange index body condition : ThreadAst L) (schedule : String)
    (resultType : Option (ThreadAst L)) (flatten : Bool) : ThreadAst L := Id.run do
  let escapedIndex := JuliaLean.base.expr.esc index
  let escapedBody := JuliaLean.base.expr.esc body
  let iter := astSym "iter"
  let et := astSym "_ET"
  let channel := astSym "c"
  let resultChannel := astSym "result_channel"
  let vals := astSym "vals"
  let predicate := if astIsTrue ops condition then astBool ops true else astSym "pred"
  let etExpr := match resultType with
    | some value => JuliaLean.base.expr.esc value
    | none => _comprehension_eltype_expr ops index body predicate flatten iter
  let valsExpr := match resultType with
    | some _ => astBaseCall ops "collect" [resultChannel]
    | none => astCall (astSym "_comprehension_result")
        [astBaseCall ops "collect" [resultChannel], et]
  let shapeExpr := if !flatten && astIsTrue ops condition then
    let shape := astCoreCall ops "isa" [astBaseCall ops "IteratorSize" [iter], astBaseGlobal ops "HasShape"]
    astIf shape (astBaseCall ops "reshape" [vals, astBaseCall ops "axes" [iter]]) vals
  else vals
  let inputChannelType := astExpr "curly" [astBaseGlobal ops "Channel", astBaseCall ops "eltype" [iter]]
  let spawnKeyword := astExpr "parameters" [astExpr "kw" [astSym "spawn", astBool ops true]]
  let inputChannelCall := astCall inputChannelType [spawnKeyword, astThreadsCall ops "threadpoolsize" []]
  let inputChannelBody := astExpr "do" [inputChannelCall, astExpr "->" [astSym "ch",
    astBlock [astFor (astSym "item") iter (astBlock [astBaseCall ops "put!" [astSym "ch", astSym "item"]])]]]
  let resultChannelType := astExpr "curly" [astBaseGlobal ops "Channel", et]
  let resultChannelCall := astCall resultChannelType [.leaf ops.positiveInfinity]
  let conditionBody := astIfNoElse (_comprehension_test_expr ops condition)
    (astBlock [astLocal (astAssign escapedIndex (astSym "item")),
      _comprehension_add_expr (astBaseGlobal ops "put!") resultChannel escapedBody flatten])
  let worker := astFunction "threadsfor_fun" [astSym "tid"]
    (astBlock [astFor (astSym "item") channel (astBlock [conditionBody])])
  let predicateExpr := (_comprehension_pred_expr ops index condition).getD (.leaf ops.leaves.nothing)
  astLet [astAssign iter escapedRange] (astBlock [
    predicateExpr,
    astLocal (astAssign et etExpr),
    astLocal (astAssign channel inputChannelBody),
    astLocal (astAssign resultChannel resultChannelCall),
    astLocal (astSym "threadsfor_fun"),
    worker,
    _threading_run_expr ops schedule,
    astBaseCall ops "close" [resultChannel],
    astLocal (astAssign vals valsExpr),
    shapeExpr])

/--
Julia source: base/threadingconstructs.jl:529-565 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function default_comprehension_expr(esc_range, lidx, body, condition, schedule, result_type, flatten)
    esc_lidx = esc(lidx)
    esc_body = esc(body)
    pred = condition === true ? true : :pred
    work_dist = _work_distribution_code()
    ET_expr = result_type === nothing ?
        _comprehension_eltype_expr(lidx, body, pred, flatten, :iter) : esc(result_type)
    final_expr = result_type === nothing ? :(_comprehension_result(result, _ET)) : :result
    quote
        let iter = $esc_range
        local items = iter isa Union{Tuple, AbstractArray} ? iter : collect(iter)
        $(_comprehension_pred_expr(lidx, condition))
        local _ET = $ET_expr
        # One buffer per task-id; tasks process contiguous ranges so concatenating
        # in tid order preserves iteration order without a sort step.
        local local_bufs = [Vector{_ET}() for _ in 1:threadpoolsize()]
        let items = items, local_bufs = local_bufs
        local threadsfor_fun
        function threadsfor_fun(tid = 1)
            # Reads: items, tid. Defines: r, loop_first, loop_last.
            $work_dist
            local buf = local_bufs[tid]
            for i = loop_first:loop_last
                local item = @inbounds r[i]
                if $(_comprehension_test_expr(condition))
                    local $esc_lidx = item
                    $(_comprehension_add_expr(:push!, :buf, esc_body, flatten))
                end
            end
        end
        $(_threading_run_expr(schedule))
        end
        local result = vcat(local_bufs...)::Vector{_ET}
        $final_expr
        end
    end
end
```
-/
def default_comprehension_expr {L State : Type} (ops : ThreadExprOps L State)
    (escapedRange index body condition : ThreadAst L) (schedule : String)
    (resultType : Option (ThreadAst L)) (flatten : Bool) : ThreadAst L := Id.run do
  let escapedIndex := JuliaLean.base.expr.esc index
  let escapedBody := JuliaLean.base.expr.esc body
  let iter := astSym "iter"
  let items := astSym "items"
  let et := astSym "_ET"
  let localBuffers := astSym "local_bufs"
  let result := astSym "result"
  let predicate := if astIsTrue ops condition then astBool ops true else astSym "pred"
  let etExpr := match resultType with
    | some value => JuliaLean.base.expr.esc value
    | none => _comprehension_eltype_expr ops index body predicate flatten iter
  let finalExpr := match resultType with
    | some _ => result
    | none => astCall (astSym "_comprehension_result") [result, et]
  let vectorType := astExpr "curly" [astSym "Vector", et]
  let vectorConstructor := astCall vectorType []
  let localBufferGenerator := astExpr "comprehension" [astExpr "generator" [vectorConstructor,
    astAssign (astSym "_") (astRange (astInt ops 1) (astThreadsCall ops "threadpoolsize" []))]]
  let unionType := astExpr "curly" [astCoreGlobal ops "Union", astCoreGlobal ops "Tuple",
    astBaseGlobal ops "AbstractArray"]
  let itemsExpr := astIf (astCoreCall ops "isa" [iter, unionType]) iter
    (astBaseCall ops "collect" [iter])
  let loop := astFor (astSym "i") (astRange (astSym "loop_first") (astSym "loop_last")) (astBlock [
    astLocal (astAssign (astSym "item") (astInbounds ops 552 (astRef (astSym "r") (astSym "i")))),
    astIfNoElse (_comprehension_test_expr ops condition) (astBlock [
      astLocal (astAssign escapedIndex (astSym "item")),
      _comprehension_add_expr (astBaseGlobal ops "push!") (astSym "buf") escapedBody flatten])])
  let signature := astCall (astSym "threadsfor_fun") [astExpr "kw" [astSym "tid", astInt ops 1]]
  let worker := astExpr "function" [signature, astBlock [
    _work_distribution_code ops,
    astLocal (astAssign (astSym "buf") (astRef localBuffers (astSym "tid"))),
    loop]]
  let threadedBody := astLet [astAssign items items, astAssign localBuffers localBuffers]
    (astBlock [astLocal (astSym "threadsfor_fun"), worker, _threading_run_expr ops schedule])
  let body := astBlock [
    astLocal (astAssign items itemsExpr),
    (_comprehension_pred_expr ops index condition).getD (.leaf ops.leaves.nothing),
    astLocal (astAssign et etExpr),
    astLocal (astAssign localBuffers localBufferGenerator),
    threadedBody,
    astLocal (astAssign result (astExpr "::" [
      astBaseCall ops "vcat" [astExpr "..." [localBuffers]], vectorType])),
    finalExpr]
  astLet [astAssign iter escapedRange] body

/--
Julia source: base/threadingconstructs.jl:376-389 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _threadsfor_single_iterator(body, iterator, condition, schedule; result_type=nothing, flatten=false)
    lidx = iterator.args[1]
    range = iterator.args[2]
    esc_range = esc(range)

    if schedule === :greedy
        return greedy_comprehension_expr(esc_range, lidx, body, condition, schedule, result_type, flatten)
    elseif condition === true && !flatten
        # One result per item: pre-allocate and write directly
        return _threadsfor_comprehension_fast(esc_range, lidx, body, schedule, result_type)
    else
        return default_comprehension_expr(esc_range, lidx, body, condition, schedule, result_type, flatten)
    end
end
```
-/
def _threadsfor_single_iterator {L State : Type} (ops : ThreadExprOps L State)
    (body iterator condition : ThreadAst L) (schedule : String)
    (resultType : Option (ThreadAst L) := none) (flatten : Bool := false) :
    ThreadAstResult (ThreadAst L) := do
  let (_, args) ← JuliaLean.base.expr.asExpr iterator
  let index ← JuliaLean.base.expr.argAt args 1
  let range ← JuliaLean.base.expr.argAt args 2
  let escapedRange := JuliaLean.base.expr.esc range
  if schedule == "greedy" then
    pure (greedy_comprehension_expr ops escapedRange index body condition schedule resultType flatten)
  else if astIsTrue ops condition && !flatten then
    pure (_threadsfor_comprehension_fast ops escapedRange index body schedule resultType)
  else pure (default_comprehension_expr ops escapedRange index body condition schedule resultType flatten)

/--
Julia source: base/threadingconstructs.jl:278-299 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _threadsfor_multi_iterator(body, iterators, condition, schedule, result_type, flatten)
    vars = [iter.args[1] for iter in iterators]
    ranges = [iter.args[2] for iter in iterators]

    tuple_var = gensym("iter_tuple")
    assignments = [:($(vars[i]) = $(tuple_var)[$i]) for i in 1:length(vars)]
    # Use let blocks so destructured variables are local to each iteration,
    # avoiding data races when multiple threads execute the body concurrently.
    new_body = Expr(:let, Expr(:block, assignments...), body)
    new_condition = if condition === true
        true
    else
        Expr(:let, Expr(:block, assignments...), condition)
    end

    # The product has the shape of the serial comprehension, so the result takes its
    # shape from it, and each iterator expression is evaluated once.
    product_expr = Expr(:call, GlobalRef(Base.Iterators, :product), ranges...)
    synthetic_iter = :($(tuple_var) = $(product_expr))

    return _threadsfor_single_iterator(new_body, synthetic_iter, new_condition, schedule; result_type, flatten)
end
```
-/
def _threadsfor_multi_iterator {L State : Type} (ops : ThreadExprOps L State)
    (state : State) (body : ThreadAst L) (iterators : List (ThreadAst L))
    (condition : ThreadAst L) (schedule : String) (resultType : Option (ThreadAst L))
    (flatten : Bool) : ThreadAstResult (ThreadAst L × State) := do
  let mut variables : List (ThreadAst L) := []
  let mut ranges : List (ThreadAst L) := []
  for iterator in iterators do
    let (_, args) ← JuliaLean.base.expr.asExpr iterator
    variables := variables ++ [← JuliaLean.base.expr.argAt args 1]
    ranges := ranges ++ [← JuliaLean.base.expr.argAt args 2]
  let (tupleName, state) := JuliaLean.base.expr.gensymString ops.gensym state
    (ops.stringBytes "iter_tuple")
  let tupleVar := astSym tupleName
  let mut assignments : List (ThreadAst L) := []
  for (varName, index) in variables.zipIdx do
    assignments := assignments ++ [astAssign varName (astRef tupleVar (astInt ops (Int.ofNat (index + 1))))]
  let newBody := astLet [astBlock assignments] body
  let newCondition := if astIsTrue ops condition then astBool ops true else astLet [astBlock assignments] condition
  let product := astCall (.globalRef ops.iteratorsModule "product") ranges
  let syntheticIterator := astAssign tupleVar product
  let result ← _threadsfor_single_iterator ops newBody syntheticIterator newCondition schedule resultType flatten
  pure (result, state)

/--
Julia source: base/threadingconstructs.jl:301-326 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _threadsfor_comprehension(gen::Expr, schedule, result_type=nothing)
    # `[f(x, y) for x in a for y in b(x)]`: the outer generator's body is the inner iterator,
    # whose elements are collected in order. The work is split over the outer iterator.
    flatten = gen.head === :flatten
    if flatten
        gen = gen.args[1]
    end
    @assert gen.head === :generator "gen.head === :generator"

    body = gen.args[1]

    # Check if the second arg is a filter (handles both single and multi-loop with filters)
    iter_or_filter = gen.args[2]
    if isa(iter_or_filter, Expr) && iter_or_filter.head === :filter
        condition = iter_or_filter.args[1]
        iterators = iter_or_filter.args[2:end]
    else
        condition = true
        iterators = gen.args[2:end]
    end
    if length(iterators) == 1
        return _threadsfor_single_iterator(body, iterators[1], condition, schedule; result_type, flatten)
    else
        return _threadsfor_multi_iterator(body, iterators, condition, schedule, result_type, flatten)
    end
end
```
-/
def _threadsfor_comprehension {L State : Type} (ops : ThreadExprOps L State)
    (state : State) (generator : ThreadAst L) (schedule : String)
    (resultType : Option (ThreadAst L) := none) : ThreadAstResult (ThreadAst L × State) := do
  let (head, args) ← JuliaLean.base.expr.asExpr generator
  let (generator, flatten) ← if head == "flatten" then
    pure (← JuliaLean.base.expr.argAt args 1, true)
  else pure (generator, false)
  let (head, args) ← JuliaLean.base.expr.asExpr generator
  if head != "generator" then throw .typeError
  let body ← JuliaLean.base.expr.argAt args 1
  let iteratorOrFilter ← JuliaLean.base.expr.argAt args 2
  let trueValue : ThreadAst L := .leaf (ops.leaves.ofBool true)
  let (condition, iterators) ← match iteratorOrFilter with
    | .expr "filter" filterArgs => do
      let filterCondition ← JuliaLean.base.expr.argAt filterArgs 1
      pure (filterCondition, filterArgs.drop 1)
    | _ => pure (trueValue, args.drop 1)
  match iterators with
  | [iterator] => do
    let result ← _threadsfor_single_iterator ops body iterator condition schedule resultType flatten
    pure (result, state)
  | _ => _threadsfor_multi_iterator ops state body iterators condition schedule resultType flatten

/--
Julia source: base/threadingconstructs.jl:261-276 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _threadsfor(iter, lbody, schedule)
    lidx = iter.args[1]         # index
    range = iter.args[2]
    esc_range = esc(range)
    func = if schedule === :greedy
        greedy_func(esc_range, lidx, lbody)
    else
        default_func(esc_range, lidx, lbody)
    end
    quote
        local threadsfor_fun
        $func
        $(_threading_run_expr(schedule))
        nothing
    end
end
```
-/
def _threadsfor {L State : Type} (ops : ThreadExprOps L State)
    (iterator body : ThreadAst L) (schedule : String) : ThreadAstResult (ThreadAst L) := do
  let (_, args) ← JuliaLean.base.expr.asExpr iterator
  let index ← JuliaLean.base.expr.argAt args 1
  let range ← JuliaLean.base.expr.argAt args 2
  let escapedRange := JuliaLean.base.expr.esc range
  let function := if schedule == "greedy" then greedy_func ops escapedRange index body
    else default_func ops escapedRange index body
  pure (astBlock [astLocal (astSym "threadsfor_fun"), function,
    _threading_run_expr ops schedule, .leaf ops.leaves.nothing])

-- UNTRANSLATED
-- Source: base/threadingconstructs.jl:789-824 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro threads(args...)
--     na = length(args)
--     if na == 2
--         sched, ex = args
--         if sched isa QuoteNode
--             sched = sched.value
--         elseif sched isa Symbol
--             # for now only allow quoted symbols
--             sched = nothing
--         end
--         if sched !== :static && sched !== :dynamic && sched !== :greedy
--             throw(ArgumentError("unsupported schedule argument in @threads"))
--         end
--     elseif na == 1
--         sched = :default
--         ex = args[1]
--     else
--         throw(ArgumentError("wrong number of arguments in @threads"))
--     end
--     if isa(ex, Expr) && (ex.head === :comprehension || ex.head === :typed_comprehension)
--         # Handle array comprehensions (typed and untyped)
--         if ex.head === :typed_comprehension
--             return _threadsfor_comprehension(ex.args[2], sched, ex.args[1])
--         else
--             return _threadsfor_comprehension(ex.args[1], sched)
--         end
--     elseif isa(ex, Expr) && ex.head === :for
--         # Handle for loops
--         if !(ex.args[1] isa Expr && ex.args[1].head === :(=))
--             throw(ArgumentError("nested outer loops are not currently supported by @threads"))
--         end
--         return _threadsfor(ex.args[1], ex.args[2], sched)
--     else
--         throw(ArgumentError("@threads requires a `for` loop or comprehension expression"))
--     end
-- end
-- /Source
-- Reason: The @threads macro validates and emits Julia syntax, including escaped user expressions; macro expansion is not modelled.

-- UNTRANSLATED
-- Source: base/threadingconstructs.jl:880-920 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro spawn(args...)
--     tp = QuoteNode(:default)
--     na = length(args)
--     if na == 2
--         ttype, ex = args
--         if ttype isa QuoteNode
--             ttype = ttype.value
--             if !in(ttype, (:interactive, :default, :samepool))
--                 throw(ArgumentError(LazyString("unsupported threadpool in @spawn: ", ttype)))
--             end
--             tp = QuoteNode(ttype)
--         else
--             tp = ttype
--         end
--     elseif na == 1
--         ex = args[1]
--     else
--         throw(ArgumentError("wrong number of arguments in @spawn"))
--     end
-- 
--     letargs = Base._lift_one_interp!(ex)
-- 
--     thunk = Base.replace_linenums!(:(()->($(esc(ex)))), __source__)
--     var = esc(Base.sync_varname)
--     quote
--         let $(letargs...)
--             local task = Task($thunk)
--             task.sticky = false
--             local tp = $(esc(tp))
--             if tp == :samepool
--                 tp = Threads.threadpool()
--             end
--             _spawn_set_thrpool(task, tp)
--             if $(Expr(:islocal, var))
--                 put!($var, task)
--             end
--             schedule(task)
--             task
--         end
--     end
-- end
-- /Source
-- Reason: The @spawn macro constructs and escapes a closure and task-scheduling syntax; macro expansion is not modelled.


end JuliaLean.base.threadingconstructs

namespace JuliaLean.Channels

set_option maxRecDepth 4096

private abbrev ti (x : Int) : JInt .i64 := JInt.lit .i64 x

/-- `base/threadingconstructs.jl:498-509` (master): the wrapping endpoint
arithmetic after the short-range branch of `_work_distribution_code`. -/
def threadsEndpoints (f len rem tid : JInt .i64) : JInt .i64 × JInt .i64 :=
  let loop_first := f + ((tid - ti 1) * len)
  let loop_last := loop_first + len - ti 1
  if rem.val > 0 then
    if tid ≤ rem then (loop_first + (tid - ti 1), loop_last + tid)
    else (loop_first + rem, loop_last + rem)
  else (loop_first, loop_last)

/-- `base/threadingconstructs.jl:484-510` (master): checked `divrem`, the
short-range return, and the endpoint arithmetic, in source order. -/
def threadsWorkDistribution (f lenr n tid : JInt .i64) :
    Jl (Option (JInt .i64 × JInt .i64)) := do
  let len ← JInt.div lenr n
  let rem ← JInt.remInt lenr n
  if len.val = 0 then
    if tid > rem then return none
    else return some (threadsEndpoints f (ti 1) (ti 0) tid)
  else return some (threadsEndpoints f len rem tid)

/-- Mathematical observation of a Julia `UnitRange`, `base/threadingconstructs.jl:520`:
its values increase by one, and it is empty when the last endpoint is smaller. -/
def threadsUnitRange (first last : JInt .i64) : List Int :=
  (List.range (last.val - first.val + 1).toNat).map (fun k : Nat => first.val + (k : Int))

/-- `base/threadingconstructs.jl:491-520` (master): one task returns immediately
or iterates its inclusive Julia `UnitRange`. Errors remain observable. -/
def threadsIterations (f lenr n tid : JInt .i64) : Jl (List Int) := do
  let bounds ← threadsWorkDistribution f lenr n tid
  return match bounds with
    | none => []
    | some (first, last) => threadsUnitRange first last

/-- Task-order concatenation for tids `1,...,count`. This is an observation of
`base/threadingconstructs.jl:498-520`, not a claim about execution order. -/
def threadsPrefix (f lenr n : JInt .i64) : Nat → Jl (List Int)
  | 0 => .ok []
  | k + 1 => do
    let earlier ← threadsPrefix f lenr n k
    let current ← threadsIterations f lenr n (ti ((k : Int) + 1))
    return earlier ++ current




end JuliaLean.Channels

namespace JuliaLean.ConcurrencyCov.Threads

open JuliaLean JuliaLean.ConcurrencyCov

/-! ## Thread and threadpool queries, lines 36-169 -/

/-- The runtime tables read by the queries. -/
structure ThreadRt where
  /-- `jl_threadid()` of the running task's thread (0-based). -/
  cur : Nat
  /-- `jl_n_threads`. -/
  nThreads : Nat
  /-- `jl_n_threads_per_pool[i]` for `i = 0, 1, ...` (`0` interactive, `1` default). -/
  perPool : List Nat
  /-- `jl_n_gcthreads`. -/
  nGcThreads : Nat
  deriving DecidableEq, Repr

/-- `threadid()`, line 36: `Int(Int16 + 1)`. -/
def threadid (rt : ThreadRt) : I64 := i64 ((rt.cur : Int) + 1)

/-- `maxthreadid()`, line 47. -/
def maxthreadid (rt : ThreadRt) : I64 := i64 rt.nThreads

/-- `_nthreads_in_pool(tpid)`, lines 62-65: `unsafe_load(p, tpid + 1)`; `none`
is a read outside the C array. -/
def nthreadsInPool (tpid : I8) (rt : ThreadRt) : Option I64 :=
  if 0 ≤ tpid.val then (rt.perPool[tpid.val.toNat]?).map fun n => i64 n else none

/-- `_tpid_to_sym(tpid)`, lines 67-77. -/
def tpidToSym (tpid : I8) : R String :=
  if tpid.val = 0 then .ok "interactive"
  else if tpid.val = 1 then .ok "default"
  else if tpid.val = -1 then .ok "foreign"
  else .error (.argumentError s!"Unrecognized threadpool id {tpid.val}")

/-- `_sym_to_tpid(tp)`, lines 79-89. -/
def symToTpid (tp : String) : R I8 :=
  if tp = "interactive" then .ok (i8 0)
  else if tp = "default" then .ok (i8 1)
  else if tp = "foreign" then .ok (i8 (-1))
  else .error (.argumentError s!"Unrecognized threadpool name `{tp}`")

/-- `jl_threadpoolid(tid)`, `src/threading.c:324-337`. -/
def jlThreadpoolid (tid : I16) (rt : ThreadRt) : R I8 :=
  if tid.val < 0 ∨ rt.nThreads ≤ tid.val then .error (.errorException "invalid tid")
  else
    let rec go (i : Nat) (n : Nat) : List Nat → I8
      | [] => i8 (-1)
      | k :: ks => if tid.val < (n + k : Nat) then i8 i else go (i + 1) (n + k) ks
    .ok (go 0 0 rt.perPool)

/-- The `Int16` argument conversion of the `ccall`. -/
def toI16 (x : I64) : R I16 :=
  if IntTy.min .i16 ≤ x.val ∧ x.val ≤ IntTy.max .i16 then .ok (JInt.lit .i16 x.val)
  else .error .inexactError

/-- `threadpool(tid = threadid())`, lines 96-99. -/
def threadpool (tid : I64) (rt : ThreadRt) : R String := do
  let t ← toI16 (tid - i64 1)
  let tpid ← jlThreadpoolid t rt
  tpidToSym tpid

/-- `ngcthreads()`, line 169. -/
def ngcthreads (rt : ThreadRt) : I64 := i64 rt.nGcThreads + i64 1

/-- `threadpoolsize(pool = :default)`, lines 136-145. -/
def threadpoolsize (pool : String) (rt : ThreadRt) : R (Option I64) :=
  if pool = "default" ∨ pool = "interactive" then do
    let tpid ← symToTpid pool
    return nthreadsInPool tpid rt
  else if pool = "foreign" then .error (.errorException "Threadpool size of `:foreign` is indeterminant")
  else .error (.errorException "invalid threadpool specified")

/-- `nthreads(pool)`, line 60. -/
def nthreads (pool : String) (rt : ThreadRt) : R (Option I64) := threadpoolsize pool rt

/-- `threadpooldescription(tid = threadid())`, lines 106-117. -/
def threadpooldescription (tid : I64) (rt : ThreadRt) : R String := do
  let name ← threadpool tid rt
  if name = "foreign" then
    let ni ← nthreads "interactive" rt
    let nd ← nthreads "default" rt
    match ni, nd with
    | some ni, some nd =>
      let n_others := ni + nd
      if n_others.val < tid.val ∧ tid.val ≤ (n_others + ngcthreads rt).val then
        return "foreign: gc"
      else return name
    | _, _ => return name
  else return name

/-- `nthreadpools()`, line 124. -/
def nthreadpools (rt : ThreadRt) : I64 := i64 rt.perPool.length

/-- `collect(a:b)` as Julia `Int`s. -/
def unitRange (a b : Int) : List I64 :=
  (List.range (b - a + 1).toNat).map fun (k : Nat) => i64 (a + (k : Int))

/-- `threadpooltids(pool)`, lines 152-161. -/
def threadpooltids (pool : String) (rt : ThreadRt) : R (List I64) :=
  let ni := (nthreadsInPool (i8 0) rt).getD (i64 0)
  if pool = "interactive" then .ok (unitRange 1 ni.val)
  else if pool = "default" then
    let nd := (nthreadsInPool (i8 1) rt).getD (i64 0)
    .ok (unitRange (ni.val + 1) (ni.val + nd.val))
  else .error (.errorException "invalid threadpool specified")

/-! ## Running the loop tasks, lines 171-259 -/

/-- `_threads_call(tfun, i)`, line 182: the stored function applied to the tid. -/
def threadsCall {β : Type} (tfun : Nat → β) (i : Nat) : β := tfun i

/-- What `_threading_run_expr(schedule)` emits, lines 257-259: the call
`threading_run(threadsfor_fun, schedule === :static)`. -/
structure RunCall where
  static : Bool
  deriving DecidableEq, Repr

def threadingRunExpr (schedule : String) : RunCall := ⟨schedule = "static"⟩

/-- The tids of the tasks `threading_run` starts (lines 201-214): `1:n`. -/
def runTids (n : Nat) : List Nat := (List.range n).map (· + 1)

/-- The per-task work of a `threadsfor_fun`: what one task's call with `tid`
produces (an index list, results, or a thrown exception). -/
def runAll {β : Type} (n : Nat) (task : Nat → R β) : R (List β) := (runTids n).mapM task

/-! ## Comprehension front end, lines 261-389 -/

/-- A comprehension's syntax as `@threads` receives it. `iters` are the `for`
clauses' iteration specs as (variable, range) names; `cond` is the filter, if any;
`flatten` marks an `Expr(:flatten, ...)` around the generator. -/
structure CompSyntax where
  flatten : Bool
  iters : List (String × String)
  cond : Option String
  deriving DecidableEq, Repr

/-- The forms of generated code. -/
inductive Path where
  | fast
  | default
  | greedy
  deriving DecidableEq, Repr

/-- The decisions the generator functions take for one comprehension: the code
path, whether the iterators were combined with `Iterators.product`, and whether
the filter is applied. -/
structure Plan where
  path : Path
  product : Bool
  filtered : Bool
  flatten : Bool
  static : Bool
  typed : Bool
  deriving DecidableEq, Repr

/-- `_threadsfor_single_iterator`, lines 376-389. -/
def singleIterator (filtered schedule flatten product typed : Bool) (sched : String) : Plan :=
  let path := if schedule then .greedy else if !filtered && !flatten then .fast else .default
  ⟨path, product, filtered, flatten, sched = "static", typed⟩

/-- `_threadsfor_multi_iterator`, lines 278-299: a synthetic iterator over
`Iterators.product(ranges...)`, with the destructuring in `let` blocks. -/
def multiIterator (c : CompSyntax) (sched : String) (typed : Bool) : Plan :=
  singleIterator c.cond.isSome (sched = "greedy") c.flatten true typed sched

/-- `_threadsfor_comprehension(gen, schedule, result_type)`, lines 301-326. -/
def threadsforComprehension (c : CompSyntax) (sched : String) (typed : Bool) : R Plan :=
  match c.iters with
  | [] => .error (.assertionError "gen.head === :generator")
  | [_] => .ok (singleIterator c.cond.isSome (sched = "greedy") c.flatten false typed sched)
  | _ :: _ :: _ => .ok (multiIterator c sched typed)

/-! ## Semantics of the generated code, lines 328-565 -/

/-- An iterator after `collect`: its elements in iteration order and its shape. -/
structure Items (α : Type) where
  elems : List α
  /-- `axes(items)` as lengths; `[n]` for a vector or a collected `SizeUnknown`
  iterator, `[]` for a zero-dimensional array. -/
  shape : List Nat
  deriving DecidableEq, Repr

/-- A result array: its elements in linear order and its shape. -/
structure Arr (β : Type) where
  elems : List β
  shape : List Nat
  deriving DecidableEq, Repr

/-- `Iterators.product(xs, ys, ...)`: column-major tuples, shape the lengths. -/
def product {α : Type} : List (List α) → List (List α)
  | [] => [[]]
  | xs :: rest => (product rest).flatMap fun t => xs.map fun x => x :: t

/-- `_comprehension_body_func(lidx, body)`, line 331: the body as a one-argument
function of the item. -/
def bodyFunc {α β : Type} (body : α → β) : α → β := fun x => body x

/-- `_comprehension_pred_expr`/`_comprehension_test_expr`, lines 346-348: the filter
as a function of the item, or `true`. -/
def predExpr {α : Type} (cond : Option (α → Bool)) : α → Bool :=
  match cond with
  | none => fun _ => true
  | some p => fun x => p x

/-- `_comprehension_add_expr(add!, dest, body, flatten)`, lines 351-352: push the
result, or every element of it. -/
def addExpr {β : Type} (dest : List β) (vals : List β) : List β := dest ++ vals

/-- The indices one task processes: `loop_first:loop_last` of
`_work_distribution_code` with `threadpoolsize() = n` (lines 484-511), using the
Channels area's model, as 0-based positions. `firstindex(r)` is `1`. -/
def taskRange (len n tid : Nat) : List Nat :=
  match JuliaLean.Channels.threadsIterations (i64 1) (i64 len) (i64 n) (i64 tid) with
  | .ok is => is.map fun i => (i - 1).toNat
  | .error _ => []

/-- The fast path, lines 395-424: `result[i] = body(r[i])` for each task's
indices, into `similar(Vector{_ET}, axes(items))`. Slots no task writes stay
`none` (`#undef`). -/
def fastRun {α β : Type} (items : Items α) (body : α → β) (n : Nat) : Arr (Option β) :=
  let len := items.elems.length
  let written : List Nat := (runTids n).flatMap (taskRange len n)
  { elems := (List.range len).map fun i =>
      if i ∈ written then (items.elems[i]?).map body else none,
    shape := items.shape }

/-- One task of the default comprehension path, lines 547-558: a local buffer of
the filtered results of its indices. -/
def defaultTask {α β : Type} (items : Items α) (pred : α → Bool) (vals : α → List β)
    (n tid : Nat) : List β :=
  (taskRange items.elems.length n tid).foldl (fun buf i =>
    match items.elems[i]? with
    | some x => if pred x then addExpr buf (vals x) else buf
    | none => buf) []

/-- The default comprehension path, lines 529-565: `vcat(local_bufs...)` in tid
order, a vector. -/
def defaultRun {α β : Type} (items : Items α) (pred : α → Bool) (vals : α → List β) (n : Nat) :
    Arr β :=
  let bufs := (runTids n).map (defaultTask items pred vals n)
  { elems := bufs.flatten, shape := [bufs.flatten.length] }

/-- The greedy comprehension path, lines 444-481. The producer task puts the items
into `c` in iteration order; the worker tasks take them in the scheduler's order
`takeOrder` (a permutation of the item positions) and put their results into
`result_channel`; `collect` returns them in arrival order. With one result per
item and a `HasShape` iterator the vector is reshaped to the iterator's axes. -/
def greedyRun {α β : Type} (items : Items α) (hasShape : Bool) (pred : α → Bool)
    (vals : α → List β) (oneEach : Bool) (takeOrder : List Nat) : Arr β :=
  let out := takeOrder.flatMap fun i =>
    match items.elems[i]? with
    | some x => if pred x then vals x else []
    | none => []
  { elems := out, shape := if oneEach && hasShape then items.shape else [out.length] }

/-- The serial comprehension the threaded one must agree with: `collect` of
`Generator(body, iter)` (one result per item, the iterator's shape), of a
filtered generator, or of a flattened one (vectors). -/
def serial {α β : Type} (items : Items α) (pred : Option (α → Bool)) (vals : α → List β)
    (oneEach : Bool) : Arr β :=
  let out := items.elems.flatMap fun x => if predExpr pred x then vals x else []
  { elems := out, shape := if oneEach && pred.isNone then items.shape else [out.length] }

/-! ### Element types, lines 333-374

Julia types are modelled by an abstract type algebra: `typeof` of each value,
`promote_typejoin`, `isa` and `isconcretetype`. -/

structure TyAlg (τ β : Type) where
  typeOf : β → τ
  join : τ → τ → τ
  isa : β → τ → Bool
  concrete : τ → Bool
  /-- `promote_typejoin_union`. -/
  joinUnion : τ → τ

/-- `_comprehension_widened_eltype(result, T, i)`, lines 368-374: the loop over the
elements from position `i` on, restarting with the widened type. -/
def widenedEltype {τ β : Type} (A : TyAlg τ β) (T : τ) : List β → τ
  | [] => T
  | el :: rest => if A.isa el T then widenedEltype A T rest
    else widenedEltype A (A.join T (A.typeOf el)) rest

/-- `_comprehension_result(result, ET)`, lines 356-364: the element type of the
returned array. `ET` is the inferred type the result was allocated with. -/
def comprehensionResultType {τ β : Type} (A : TyAlg τ β) (ET : τ) (elems : List β) : τ :=
  match elems with
  | [] => A.joinUnion ET
  | x :: rest => if A.concrete ET then ET else widenedEltype A (A.typeOf x) rest

/-- The element type of a serial `collect` (base/array.jl `collect(::Generator)`,
`collect_to_with_first!`, `grow_to!`): `promote_typejoin_union` of the inferred type
for an empty result, otherwise the type of the first value widened over the rest. -/
def serialEltype {τ β : Type} (A : TyAlg τ β) (ET : τ) (elems : List β) : τ :=
  match elems with
  | [] => A.joinUnion ET
  | x :: rest => widenedEltype A (A.typeOf x) rest

/-! ## The `@threads` and `@spawn` macros, lines 789-920 -/

/-- The macro arguments `@threads` inspects. -/
inductive TArg where
  | quoted (s : String)
  | sym (s : String)
  /-- `for <it> ... end`; `assign` is `it.head === :(=)` (a single `x = range`). -/
  | forLoop (assign : Bool)
  | comprehension (c : CompSyntax)
  | typedComprehension (c : CompSyntax)
  | other
  deriving DecidableEq, Repr

/-- The expansions of `@threads`. -/
inductive Expansion where
  /-- `_threadsfor(iter, body, sched)`: `greedy_func` for `:greedy`, else `default_func`. -/
  | loop (greedy : Bool) (run : RunCall)
  | comp (p : Plan)
  deriving DecidableEq, Repr

/-- `_threadsfor(iter, lbody, schedule)`, lines 261-276. -/
def threadsfor (schedule : String) : Expansion :=
  .loop (schedule = "greedy") (threadingRunExpr schedule)

/-- The argument checks of `@threads`, lines 789-806: the schedule and the loop. -/
def threadsArgs (args : List TArg) : R (String × TArg) :=
  match args with
  | [s, ex] =>
    let sched : Option String := match s with
      | .quoted q => some q
      | _ => none
    if sched = some "static" ∨ sched = some "dynamic" ∨ sched = some "greedy" then
      .ok (sched.getD "", ex)
    else .error (.argumentError "unsupported schedule argument in @threads")
  | [ex] => .ok ("default", ex)
  | _ => .error (.argumentError "wrong number of arguments in @threads")

/-- The expansion of `@threads` after the argument checks, lines 807-824. -/
def threadsExpand (sched : String) (ex : TArg) : R Expansion :=
  match ex with
  | .typedComprehension c => .comp <$> threadsforComprehension c sched true
  | .comprehension c => .comp <$> threadsforComprehension c sched false
  | .forLoop assign =>
    if !assign then .error (.argumentError "nested outer loops are not currently supported by @threads")
    else .ok (threadsfor sched)
  | _ => .error (.argumentError "@threads requires a `for` loop or comprehension expression")

/-- `@threads args...`, lines 789-824. -/
def threadsMacro (args : List TArg) : R Expansion := do
  let (sched, ex) ← threadsArgs args
  threadsExpand sched ex

/-- `_nthreads_in_pool(tpid) == 0`; a read outside the C array is not `0`. -/
def zeroCount (n : Option I64) : Bool :=
  match n with
  | some k => k.val = 0
  | none => false

/-- `_spawn_set_thrpool(t, tp)`, lines 826-834: the pool id stored in the task. -/
def spawnSetThrpool (tp : String) (rt : ThreadRt) : R I8 := do
  let tpid ← symToTpid tp
  let n := nthreadsInPool tpid rt
  if tpid.val = -1 ∨ zeroCount n then return i8 1
  else return tpid

/-- The threadpool argument of `@spawn`: a quoted symbol or a runtime value. -/
inductive PoolArg where
  | quoted (s : String)
  | value (s : String)
  deriving DecidableEq, Repr

/-- What the `@spawn` expansion does when it runs (lines 880-920): the task's pool
id, whether it is pushed to the enclosing `@sync`, and that it is scheduled
non-sticky. -/
structure Spawned where
  tpid : I8
  synced : Bool
  sticky : Bool
  deriving DecidableEq, Repr

/-- The argument checks of `@spawn [tp] ex`, lines 880-900: the pool name. -/
def spawnArgs (args : List (Option PoolArg)) : R String :=
  match args with
  | [some (.quoted t), _] =>
    if t ∈ ["interactive", "default", "samepool"] then .ok t
    else .error (.argumentError s!"unsupported threadpool in @spawn: {t}")
  | [some (.value t), _] => .ok t
  | [none, _] => .error (.argumentError "unsupported threadpool in @spawn")
  | [_] => .ok "default"
  | _ => .error (.argumentError "wrong number of arguments in @spawn")

/-- `@spawn [tp] ex`, lines 880-920: argument checks at expansion, then the run
time of the expansion with `inSync` telling whether a `@sync` variable is local. -/
def spawnMacro (args : List (Option PoolArg)) (inSync : Bool) (rt : ThreadRt) : R Spawned := do
  let tp ← spawnArgs args
  let tp ← (if tp = "samepool" then threadpool (threadid rt) rt else pure tp)
  let tpid ← spawnSetThrpool tp rt
  return ⟨tpid, inSync, false⟩

end JuliaLean.ConcurrencyCov.Threads

namespace JuliaLean.ConcurrencyCov.FaithfulThreads

open JuliaLean JuliaLean.ConcurrencyCov

def threadidM := Threads.threadid
def maxthreadidM := Threads.maxthreadid
def nthreadsM := Threads.nthreads
def nthreadsInPoolM := Threads.nthreadsInPool
def tpidToSymM := Threads.tpidToSym
def symToTpidM := Threads.symToTpid
def threadpoolM := Threads.threadpool
def threadpoolDescriptionM := Threads.threadpooldescription
def nthreadpoolsM := Threads.nthreadpools
def threadpoolsizeM := Threads.threadpoolsize
def threadpooltidsM := Threads.threadpooltids
def ngcthreadsM := Threads.ngcthreads
def threadsCallM := @Threads.threadsCall
inductive RunPhase where | enter | create (tid : Nat) | schedule (tid : Nat) | wait (tid : Nat) | exit
  deriving DecidableEq, Repr
inductive WorkerOutcome where | ok | failed | cancelled (severity : Nat)
  deriving DecidableEq, Repr
structure RunTrace where
  phases : List RunPhase
  result : R Unit
  deriving Repr
def threadingRun (static nested : Bool) (outcomes : List WorkerOutcome) : RunTrace :=
  if static && nested then ⟨[], .error (.errorException "`@threads :static` cannot be used concurrently or nested")⟩
  else
    let tids := Threads.runTids outcomes.length
    let phases := [.enter] ++ tids.map .create ++ tids.map .schedule ++ tids.map .wait ++ [.exit]
    let failed := (List.range outcomes.length).filter fun i => outcomes[i]? = some .failed
    match outcomes.find? fun x => match x with | .cancelled _ => true | _ => false with
    | some (.cancelled severity) => ⟨phases, .error (.cancellation severity)⟩
    | _ => if failed.isEmpty then ⟨phases, .ok ()⟩ else ⟨phases, .error (.composite failed)⟩
def threadingRunExprM := Threads.threadingRunExpr
def threadsforM := Threads.threadsfor
def multiIteratorM := Threads.multiIterator
def comprehensionM := Threads.threadsforComprehension
def bodyFuncM := @Threads.bodyFunc
def comprehensionEltypeM := @Threads.comprehensionResultType
def predExprM := @Threads.predExpr
def testExprM := @Threads.predExpr
def addExprM := @Threads.addExpr
def resultM := @Threads.comprehensionResultType
def widenedM := @Threads.widenedEltype
def singleIteratorM := Threads.singleIterator
def fastComprehensionM := @Threads.fastRun
def fastWorkerM := @Threads.fastRun
def greedyFuncM := @Threads.greedyRun
def greedyWorkerM := @Threads.greedyRun
def greedyComprehensionM := @Threads.greedyRun
def greedyComprehensionWorkerM := @Threads.greedyRun
def workDistributionM := JuliaLean.Channels.threadsIterations
def defaultFuncM := @Threads.defaultTask
def defaultFuncWorkerM := @Threads.defaultTask
def defaultComprehensionM := @Threads.defaultRun
def defaultComprehensionWorkerM := @Threads.defaultTask
def threadsMacroM := Threads.threadsMacro
def spawnSetPoolM := Threads.spawnSetThrpool
def spawnMacroM := Threads.spawnMacro

end JuliaLean.ConcurrencyCov.FaithfulThreads
