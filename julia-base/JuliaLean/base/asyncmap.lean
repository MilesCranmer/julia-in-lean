import JuliaLean.Core
import JuliaLean.base.int
import JuliaLean.base.iterators
import JuliaLean.base.abstractarray
import JuliaLean.base.channels

/-!
# Model of `base/asyncmap.jl`

Typed models of asynchronous collection mapping. Channel storage, task creation,
fetching, user calls, source iteration, and collection operations are explicit
interfaces. Collector and generator state is threaded through the world action,
which preserves writes and errors across task operations.
-/

namespace JuliaLean.base.asyncmap

open JuliaLean

abbrev I64 := JInt .i64
abbrev M (E Task W A : Type) := JuliaLean.base.channels.M E Task W A

def int (value : Int) : I64 := JInt.lit .i64 value

-- UNTRANSLATED
-- Reason: License text and module imports are represented by repository metadata and Lean imports.
-- Source: base/asyncmap.jl:1-4 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- using Base.Iterators: Enumerate
-- 
-- /Source

inductive AsyncMapSource (TupleSource ArraySource GenericSource : Type) where
  | tuple : TupleSource → AsyncMapSource TupleSource ArraySource GenericSource
  | array : ArraySource → AsyncMapSource TupleSource ArraySource GenericSource
  | generic : GenericSource → AsyncMapSource TupleSource ArraySource GenericSource

inductive BatchSizeState (BatchArg : Type) where
  | raw : Option BatchArg → BatchSizeState BatchArg
  | checked : Option I64 → BatchSizeState BatchArg

/--
Julia source: base/asyncmap.jl:194-204 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

mutable struct AsyncCollector
    f
    results
    enumerator::Enumerate
    ntasks
    batch_size
    nt_check::Bool     # check number of tasks on every iteration

    AsyncCollector(f, r, en::Enumerate, ntasks, batch_size) = new(f, r, en, ntasks, batch_size, isa(ntasks, Function))
end
```
-/
structure AsyncCollector (Source F Results NT BatchArg : Type) where
  f : F
  results : Results
  enumerator : JuliaLean.base.iterators.Enumerate Source
  ntasks : NT
  batchSize : BatchSizeState BatchArg
  ntCheck : Bool

/--
Julia source: base/asyncmap.jl:229-236 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

mutable struct AsyncCollectorState
    chnl::Channel
    worker_tasks::Vector{Task}
    exec_func
    batch_size
    enum_state      # enumerator state
end
```
-/
structure AsyncCollectorState (Channel Task Exec SourceState : Type) where
  channel : Channel
  workerTasks : Array Task
  execFunc : Exec
  batchSize : Option I64
  enumState : Option (I64 × SourceState)

inductive AsyncExec (F Results : Type) where
  | batch : F → Results → AsyncExec F Results
  | single : F → Results → AsyncExec F Results

inductive WorkerOutcome (Captured : Type) where
  | completed
  | failed : Captured → WorkerOutcome Captured

abbrev MapSource (TupleSource ArraySource GenericSource : Type) := AsyncMapSource TupleSource ArraySource GenericSource
abbrev EnumerateSource (TupleSource ArraySource GenericSource : Type) := JuliaLean.base.iterators.Enumerate (MapSource TupleSource ArraySource GenericSource)

structure SourceOps (E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState : Type) where
  collectionLength : Inputs → M E Task W I64
  firstCollection : Inputs → M E Task W Collection
  fromCollection : Collection → M E Task W (AsyncMapSource TupleSource ArraySource GenericSource)
  zip : Inputs → M E Task W (AsyncMapSource TupleSource ArraySource GenericSource)
  hasLength : AsyncMapSource TupleSource ArraySource GenericSource → M E Task W Bool
  length : AsyncMapSource TupleSource ArraySource GenericSource → M E Task W I64
  enumeratorHasLength : JuliaLean.base.iterators.Enumerate (AsyncMapSource TupleSource ArraySource GenericSource) → M E Task W Bool
  enumeratorLength : JuliaLean.base.iterators.Enumerate (AsyncMapSource TupleSource ArraySource GenericSource) → M E Task W I64
  iterate : AsyncMapSource TupleSource ArraySource GenericSource → Option SourceState → M E Task W (Option (Args × SourceState))

structure KeywordOps (E Task W NT BatchArg : Type) where
  isNumber : NT → Bool
  isFunction : NT → Bool
  nonnegative : NT → M E Task W Bool
  equalZero : NT → M E Task W Bool
  showNt : NT → M E Task W String
  ntasksToInt : NT → M E Task W I64
  callNtFunction : NT → M E Task W I64
  fromInt : I64 → NT
  batchIsNumber : BatchArg → Bool
  batchToInt : BatchArg → M E Task W I64
  showBatchArg : BatchArg → M E Task W String

structure FunctionOps (E Task W F Args Value BatchResult BatchState : Type) where
  apply : F → Args → M E Task W Value
  applyBatch : F → Array Args → M E Task W BatchResult
  iterateBatch : BatchResult → Option BatchState → M E Task W (Option (Value × BatchState))
  batchIndex : Array I64 → I64 → M E Task W I64

structure StoreOps (E Task W Results Value : Type) where
  setResult : Results → I64 → Value → M E Task W Unit

structure TaskOps (E Task W Channel Cond Lock Waiter Token Ref Pool Backtrace Captured WorkItem : Type) where
  channelRuntime : JuliaLean.base.channels.Runtime E W Channel Cond Lock Task Waiter Token WorkItem
  taskRuntime : JuliaLean.base.channels.TaskRuntime (E := E) (Task := Task) (W := W) Ref Pool
  fetchTask : Task → M E Task W (WorkerOutcome Captured)
  catchBacktrace : M E Task W Backtrace
  captureException : JuliaLean.base.channels.Error E Task → Backtrace → M E Task W Captured
  throwCaptured : Captured → M E Task W Unit

structure AsyncMapRuntime
    (E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState F Value BatchResult BatchState NT BatchArg Channel Cond Lock Waiter Token Ref Pool Backtrace Captured : Type) where
  sources : SourceOps E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState
  keywords : KeywordOps E Task W NT BatchArg
  functions : FunctionOps E Task W F Args Value BatchResult BatchState
  tasks : TaskOps E Task W Channel Cond Lock Waiter Token Ref Pool Backtrace Captured (I64 × Args)

structure AsyncMapOutputOps (E Task W Vector Dict Value : Type) where
  newVector : I64 → M E Task W Vector
  setVector : Vector → I64 → Value → M E Task W Unit
  newDict : M E Task W Dict
  setDict : Dict → I64 → Value → M E Task W Unit
  dictLength : Dict → M E Task W I64
  dictGet : Dict → I64 → M E Task W Value
  dictHasKey : Dict → I64 → M E Task W Bool
  dictDelete : Dict → I64 → M E Task W Unit
  dictIsEmpty : Dict → M E Task W Bool

inductive AsyncResults (Vector Dict : Type) where
  | vector : Vector → AsyncResults Vector Dict
  | dict : Dict → AsyncResults Vector Dict

inductive AsyncMapOutput (TupleResult ArrayResult GenericResult : Type) where
  | tuple : TupleResult → AsyncMapOutput TupleResult ArrayResult GenericResult
  | array : ArrayResult → AsyncMapOutput TupleResult ArrayResult GenericResult
  | generic : GenericResult → AsyncMapOutput TupleResult ArrayResult GenericResult

structure AsyncMapResultOps
    (E Task W Vector TupleSource ArraySource GenericSource Axes Reshaped Generator TupleResult ArrayResult GenericResult : Type) where
  mapIdentity : Vector → M E Task W Vector
  tuple : Vector → M E Task W TupleResult
  axesArray : ArraySource → M E Task W Axes
  axesGeneric : GenericSource → M E Task W Axes
  reshape : Vector → Axes → M E Task W Reshaped
  identityGenerator : Reshaped → Generator
  collectSimilar : ArraySource → Generator → M E Task W ArrayResult
  collect : Generator → M E Task W GenericResult
  iteratorSize : GenericSource → M E Task W JuliaLean.base.iterators.IteratorSizeTag
  mapIdentityGeneric : Vector → M E Task W GenericResult

structure AsyncStringOps (E Task W String CharVector Inputs : Type) where
  length : String → M E Task W I64
  allocateCharVector : I64 → M E Task W CharVector
  singletonInput : String → Inputs
  toString : CharVector → M E Task W String

/--
Julia source: base/asyncmap.jl:292-308 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

"""
    AsyncGenerator(f, c...; ntasks=0, batch_size=nothing) -> iterator

Apply `f` to each element of `c` using at most `ntasks` asynchronous tasks.

Keyword args `ntasks` and `batch_size` have the same behavior as in
[`asyncmap`](@ref). If `batch_size` is specified, `f` must
be a function which operates on an array of argument tuples.

!!! note
    `collect(AsyncGenerator(f, c...; ntasks=1))` is equivalent to
    `map(f, c...)`.
"""
mutable struct AsyncGenerator
    collector::AsyncCollector
end
```
-/
structure AsyncGenerator (Collector : Type) where
  collector : Collector

/--
Julia source: base/asyncmap.jl:313-318 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

mutable struct AsyncGeneratorState
    i::Int
    collector_done::Bool
    collector_state::Union{AsyncCollectorState, Nothing}
end
```
-/
structure AsyncGeneratorState (CollectorState : Type) where
  i : I64
  collectorDone : Bool
  collectorState : Option CollectorState

structure ActionIterator (E Task W State Elem : Type) where
  initial : State
  next : State → M E Task W (Option (Elem × State))

instance {E Task W State Elem : Type} : ForIn (M E Task W) (ActionIterator E Task W State Elem) Elem where
  forIn iterator initial step :=
    JuliaLean.base.channels.loop (fun (state, result) => do
      match ← iterator.next state with
      | none => pure (.inl result)
      | some (value, nextState) =>
          match ← step value result with
          | .yield nextResult => pure (.inr (nextState, nextResult))
          | .done finalResult => pure (.inl finalResult)) (iterator.initial, initial)

def iterateEnumerated
    {E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState : Type}
    (sources : SourceOps E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState)
    (enumerator : JuliaLean.base.iterators.Enumerate (AsyncMapSource TupleSource ArraySource GenericSource))
    (state : Option (I64 × SourceState)) : M E Task W (Option ((I64 × Args) × (I64 × SourceState))) := do
  let (index, sourceState) := match state with
    | none => (int 1, none)
    | some (index, sourceState) => (index, some sourceState)
  match ← sources.iterate enumerator.itr sourceState with
  | none => pure none
  | some (value, nextState) => pure (some ((index, value), (index + int 1, nextState)))

/--
Julia source: base/asyncmap.jl:102-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
batch_size_err_str(batch_size) = string("batch_size must be specified as a positive integer. batch_size=", batch_size)
```
-/
def batchSizeErrStr {E Task W BatchArg : Type}
    (showValue : BatchArg → M E Task W String) (batchSize : BatchArg) : M E Task W String := do
  pure ("batch_size must be specified as a positive integer. batch_size=" ++ (← showValue batchSize))

/--
Julia source: base/asyncmap.jl:103-113 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function verify_batch_size(batch_size)
    if batch_size === nothing
        return batch_size
    elseif isa(batch_size, Number)
        batch_size = Int(batch_size)
        batch_size < 1 && throw(ArgumentError(batch_size_err_str(batch_size)))
        return batch_size
    else
        throw(ArgumentError(batch_size_err_str(batch_size)))
    end
end
```
-/
def verifyBatchSize {E Task W NT BatchArg : Type}
    (ops : KeywordOps E Task W NT BatchArg) (batchSize : Option BatchArg) : M E Task W (Option I64) := do
  match batchSize with
  | none => pure none
  | some value =>
      if ops.batchIsNumber value then
        let size ← ops.batchToInt value
        if size.val < 1 then
          let message ← batchSizeErrStr (fun n => pure (toString n.val)) size
          throw (.julia (.argumentError message))
        pure (some size)
      else
        let message ← batchSizeErrStr ops.showBatchArg value
        throw (.julia (.argumentError message))

/--
Julia source: base/asyncmap.jl:114-130 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia


function verify_ntasks(iterable, ntasks)
    if !((isa(ntasks, Number) && (ntasks >= 0)) || isa(ntasks, Function))
        err = string("ntasks must be specified as a positive integer or a 0-arg function. ntasks=", ntasks)
        throw(ArgumentError(err))
    end

    if ntasks == 0
        if haslength(iterable)
            ntasks = max(1,min(100, length(iterable)))
        else
            ntasks = 100
        end
    end
    return ntasks
end
```
-/
def verifyNtTasks
    {E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState F Value BatchResult BatchState NT BatchArg Channel Cond Lock Waiter Token Ref Pool Backtrace Captured : Type}
    (runtime : AsyncMapRuntime E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState
      F Value BatchResult BatchState NT BatchArg Channel Cond Lock Waiter Token Ref Pool Backtrace Captured)
    (enumerator : JuliaLean.base.iterators.Enumerate (AsyncMapSource TupleSource ArraySource GenericSource))
    (ntasks : NT) : M E Task W NT := do
  let numberIsValid ← if runtime.keywords.isNumber ntasks then runtime.keywords.nonnegative ntasks else pure false
  if !(numberIsValid || runtime.keywords.isFunction ntasks) then
    let message := "ntasks must be specified as a positive integer or a 0-arg function. ntasks=" ++ (← runtime.keywords.showNt ntasks)
    throw (.julia (.argumentError message))
  if ← runtime.keywords.equalZero ntasks then
    if ← runtime.sources.enumeratorHasLength enumerator then
      let length ← runtime.sources.enumeratorLength enumerator
      let bounded := if length.val < 1 then 1 else if length.val > 100 then 100 else length.val
      pure (runtime.keywords.fromInt (JInt.wrap .i64 bounded))
    else
      pure (runtime.keywords.fromInt (int 100))
  else
    pure ntasks

def storeAsyncResults
    {E Task W Vector Dict Value : Type}
    (ops : AsyncMapOutputOps E Task W Vector Dict Value) :
    StoreOps E Task W (AsyncResults Vector Dict) Value :=
  { setResult := fun results index value =>
      match results with
      | .vector vector => ops.setVector vector index value
      | .dict dict => ops.setDict dict index value }

def dictionaryResultsVector
    {E Task W Vector Dict Value : Type}
    (ops : AsyncMapOutputOps E Task W Vector Dict Value) (dict : Dict) : M E Task W Vector := do
  let count ← ops.dictLength dict
  let vector ← ops.newVector count
  let limit := count.val.toNat
  let _ ← JuliaLean.base.channels.loop (fun index : Nat => do
    if index >= limit then
      pure (.inl ())
    else
      let position := JInt.lit .i64 (Int.ofNat (index + 1))
      let value ← ops.dictGet dict position
      ops.setVector vector position value
      pure (.inr (index + 1))) 0
  pure vector

/--
Julia source: base/asyncmap.jl:203-203 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    AsyncCollector(f, r, en::Enumerate, ntasks, batch_size) = new(f, r, en, ntasks, batch_size, isa(ntasks, Function))
```
-/
def asyncCollectorInner
    {Source F Results NT BatchArg : Type}
    (isFunction : NT → Bool) (f : F) (results : Results)
    (enumerator : JuliaLean.base.iterators.Enumerate Source) (ntasks : NT)
    (batchSize : Option BatchArg) : AsyncCollector Source F Results NT BatchArg :=
  { f := f, results := results, enumerator := enumerator, ntasks := ntasks,
    batchSize := .raw batchSize, ntCheck := isFunction ntasks }

/--
Julia source: base/asyncmap.jl:205-228 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

"""
    AsyncCollector(f, results, c...; ntasks=0, batch_size=nothing) -> iterator

Return an iterator which applies `f` to each element of `c` asynchronously
and collects output into `results`.

Keyword args `ntasks` and `batch_size` have the same behavior as in
[`asyncmap`](@ref). If `batch_size` is specified, `f` must
be a function which operates on an array of argument tuples.

!!! note
    `iterate(::AsyncCollector, state) -> (nothing, state)`. A successful return
    from `iterate` indicates that the next element from the input collection is
    being processed asynchronously. It blocks until a free worker task becomes
    available.

!!! note
    `for _ in AsyncCollector(f, results, c...; ntasks=1) end` is equivalent to
    `map!(f, results, c...)`.
"""
function AsyncCollector(f, results, c...; ntasks=0, batch_size=nothing)
    AsyncCollector(f, results, enumerate(zip(c...)), ntasks, batch_size)
end
```
-/
def makeAsyncCollector
    {E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState F Results NT BatchArg Channel Cond Lock Waiter Token Ref Pool Backtrace Captured BatchResult BatchState : Type}
    (runtime : AsyncMapRuntime E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState F Value BatchResult BatchState NT BatchArg Channel Cond Lock Waiter Token Ref Pool Backtrace Captured)
    (f : F) (results : Results) (inputs : Inputs) (ntasks : NT) (batchSize : Option BatchArg) :
    M E Task W (AsyncCollector (MapSource TupleSource ArraySource GenericSource) F Results NT BatchArg) := do
  let zipped ← runtime.sources.zip inputs
  let enumerator := JuliaLean.base.iterators.enumerateModel zipped
  pure (asyncCollectorInner runtime.keywords.isFunction f results enumerator ntasks batchSize)

def runBatchExec
    {E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState F Results Value BatchResult BatchState NT BatchArg Channel Cond Lock Waiter Token Ref Pool Backtrace Captured : Type}
    (runtime : AsyncMapRuntime E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState F Value BatchResult BatchState NT BatchArg Channel Cond Lock Waiter Token Ref Pool Backtrace Captured)
    (store : StoreOps E Task W Results Value)
    (f : F) (results : Results) (batch : Array (I64 × Args)) : M E Task W Unit := do
  let indices := batch.map Prod.fst
  let batchedArgs := batch.map Prod.snd
  let values ← runtime.functions.applyBatch f batchedArgs
  let _ ← JuliaLean.base.channels.loop (fun (index, state) => do
    match ← runtime.functions.iterateBatch values state with
    | none => pure (.inl ())
    | some (value, nextState) => do
        let resultIndex ← runtime.functions.batchIndex indices index
        store.setResult results resultIndex value
        pure (.inr (index + int 1, some nextState))) (int 1, none)
  pure ()

def runSingleExec
    {E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState F Results Value BatchResult BatchState NT BatchArg Channel Cond Lock Waiter Token Ref Pool Backtrace Captured : Type}
    (runtime : AsyncMapRuntime E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState F Value BatchResult BatchState NT BatchArg Channel Cond Lock Waiter Token Ref Pool Backtrace Captured)
    (store : StoreOps E Task W Results Value)
    (f : F) (results : Results) (index : I64) (args : Args) : M E Task W Unit := do
  let value ← runtime.functions.apply f args
  store.setResult results index value

def executeBatchExec
    {E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState F Results Value BatchResult BatchState NT BatchArg Channel Cond Lock Waiter Token Ref Pool Backtrace Captured : Type}
    (runtime : AsyncMapRuntime E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState F Value BatchResult BatchState NT BatchArg Channel Cond Lock Waiter Token Ref Pool Backtrace Captured)
    (store : StoreOps E Task W Results Value)
    (exec : AsyncExec F Results) (batch : Array (I64 × Args)) : M E Task W Unit := do
  match exec with
  | .batch f results => runBatchExec runtime store f results batch
  | .single _ _ => throw (.julia (.methodError "asyncmap"))

def executeSingleExec
    {E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState F Results Value BatchResult BatchState NT BatchArg Channel Cond Lock Waiter Token Ref Pool Backtrace Captured : Type}
    (runtime : AsyncMapRuntime E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState F Value BatchResult BatchState NT BatchArg Channel Cond Lock Waiter Token Ref Pool Backtrace Captured)
    (store : StoreOps E Task W Results Value)
    (exec : AsyncExec F Results) (item : I64 × Args) : M E Task W Unit := do
  match exec with
  | .single f results => runSingleExec runtime store f results item.1 item.2
  | .batch _ _ => throw (.julia (.methodError "asyncmap"))

def collectChannelBatch
    {E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState F Value BatchResult BatchState NT BatchArg Channel Cond Lock Waiter Token Ref Pool Backtrace Captured : Type}
    (runtime : AsyncMapRuntime E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState F Value BatchResult BatchState NT BatchArg Channel Cond Lock Waiter Token Ref Pool Backtrace Captured)
    (channel : Channel) (batchSize : I64) : M E Task W (Array (I64 × Args) × I64) := do
  JuliaLean.base.channels.loop (fun (batch, count) => do
    match ← JuliaLean.base.channels.iterate runtime.tasks.channelRuntime channel with
    | none => pure (.inl (batch, count))
    | some (item, _) => do
        let batch := batch.push item
        let count := count + int 1
        if count == batchSize then pure (.inl (batch, count)) else pure (.inr (batch, count))) (#[], int 0)

def runWorkerLoop
    {E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState F Results Value BatchResult BatchState NT BatchArg Channel Cond Lock Waiter Token Ref Pool Backtrace Captured : Type}
    (runtime : AsyncMapRuntime E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState F Value BatchResult BatchState NT BatchArg Channel Cond Lock Waiter Token Ref Pool Backtrace Captured)
    (store : StoreOps E Task W Results Value)
    (exec : AsyncExec F Results) (channel : Channel) (batchSize : Option I64) : M E Task W Unit := do
  match batchSize with
  | some size =>
      let _ ← JuliaLean.base.channels.loop (fun (_ : Unit) => do
        if !(← JuliaLean.base.channels.isopen runtime.tasks.channelRuntime channel) then
          pure (.inl ())
        else
          let (batch, count) ← collectChannelBatch runtime channel size
          if count.val > 0 then executeBatchExec runtime store exec batch
          pure (.inr ())) ()
      pure ()
  | none =>
      let _ ← JuliaLean.base.channels.loop (fun (_ : Unit) => do
        match ← JuliaLean.base.channels.iterate runtime.tasks.channelRuntime channel with
        | none => pure (.inl ())
        | some (item, _) => do
            executeSingleExec runtime store exec item
            pure (.inr ())) ()
      pure ()

def asyncWorker
    {E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState F Results Value BatchResult BatchState NT BatchArg Channel Cond Lock Waiter Token Ref Pool Backtrace Captured : Type}
    (runtime : AsyncMapRuntime E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState F Value BatchResult BatchState NT BatchArg Channel Cond Lock Waiter Token Ref Pool Backtrace Captured)
    (store : StoreOps E Task W Results Value)
    (exec : AsyncExec F Results) (channel : Channel) (batchSize : Option I64) : M E Task W (WorkerOutcome Captured) := do
  tryCatch
    (do
      runWorkerLoop runtime store exec channel batchSize
      pure .completed)
    (fun error => do
      JuliaLean.base.channels.closeDefault runtime.tasks.channelRuntime channel
      let trace ← runtime.tasks.catchBacktrace
      let captured ← runtime.tasks.captureException error trace
      pure (.failed captured))

/--
Julia source: base/asyncmap.jl:153-186 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function start_worker_task!(worker_tasks, exec_func, chnl, batch_size=nothing)
    t = @async begin
        retval = nothing

        try
            if isa(batch_size, Number)
                while isopen(chnl)
                    # The mapping function expects an array of input args, as it processes
                    # elements in a batch.
                    batch_collection=Any[]
                    n = 0
                    for exec_data in chnl
                        push!(batch_collection, exec_data)
                        n += 1
                        (n == batch_size) && break
                    end
                    if n > 0
                        exec_func(batch_collection)
                    end
                end
            else
                for exec_data in chnl
                    exec_func(exec_data...)
                end
            end
        catch e
            close(chnl)
            retval = capture_exception(e, catch_backtrace())
        end
        retval
    end
    push!(worker_tasks, t)
end
```
-/
def startWorkerTask
    {E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState F Results Value BatchResult BatchState NT BatchArg Channel Cond Lock Waiter Token Ref Pool Backtrace Captured : Type}
    (runtime : AsyncMapRuntime E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState F Value BatchResult BatchState NT BatchArg Channel Cond Lock Waiter Token Ref Pool Backtrace Captured)
    (store : StoreOps E Task W Results Value)
    (exec : AsyncExec F Results) (channel : Channel) (batchSize : Option I64)
    (workerTasks : Array Task) : M E Task W (Array Task) := do
  let task ← runtime.tasks.taskRuntime.newTask (fun _ => asyncWorker runtime store exec channel batchSize)
  pure (workerTasks.push task)

/--
Julia source: base/asyncmap.jl:131-152 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia


function setup_chnl_and_tasks(exec_func, ntasks, batch_size=nothing)
    if isa(ntasks, Function)
        nt = ntasks()::Int
        # start at least one worker task.
        if nt == 0
            nt = 1
        end
    else
        nt = ntasks::Int
    end

    # Use an unbuffered channel for communicating with the worker tasks. In the event
    # of an error in any of the worker tasks, the channel is closed. This
    # results in the `put!` in the driver task failing immediately.
    chnl = Channel(0)
    worker_tasks = Task[]
    foreach(_ -> start_worker_task!(worker_tasks, exec_func, chnl, batch_size), 1:nt)
    yield()
    return (chnl, worker_tasks)
end
```
-/
def setupChannelAndTasks
    {E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState F Results Value BatchResult BatchState NT BatchArg Channel Cond Lock Waiter Token Ref Pool Backtrace Captured : Type}
    (runtime : AsyncMapRuntime E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState F Value BatchResult BatchState NT BatchArg Channel Cond Lock Waiter Token Ref Pool Backtrace Captured)
    (store : StoreOps E Task W Results Value)
    (exec : AsyncExec F Results) (ntasks : NT) (batchSize : Option I64) :
    M E Task W (Channel × Array Task) := do
  let nt ← if runtime.keywords.isFunction ntasks then
      runtime.keywords.callNtFunction ntasks
    else
      runtime.keywords.ntasksToInt ntasks
  let nt := if nt.val == 0 then int 1 else nt
  let channel ← JuliaLean.base.channels.constructDefault runtime.tasks.channelRuntime (int 0)
  let count := if nt.val > 0 then nt.val.toNat else 0
  let workerTasks ← JuliaLean.base.channels.loop (fun (index, tasks) => do
    if index >= count then
      pure (.inl tasks)
    else
      let tasks ← startWorkerTask runtime store exec channel batchSize tasks
      pure (.inr (index + 1, tasks))) (0, #[])
  runtime.tasks.channelRuntime.yieldCurrent
  pure (channel, workerTasks)

structure CollectorIteration (Collector State : Type) where
  collector : Collector
  state : State
  yielded : Bool

/--
Julia source: base/asyncmap.jl:256-263 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function wait_done(state::AsyncCollectorState)
    close(state.chnl)

    # wait for all tasks to finish
    foreach(x->(v=fetch(x); isa(v, Exception) && throw(v)), state.worker_tasks)
    empty!(state.worker_tasks)
end
```
-/
def waitDone
    {E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState F Results Value BatchResult BatchState NT BatchArg Channel Cond Lock Waiter Token Ref Pool Backtrace Captured : Type}
    (runtime : AsyncMapRuntime E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState F Value BatchResult BatchState NT BatchArg Channel Cond Lock Waiter Token Ref Pool Backtrace Captured)
    (state : AsyncCollectorState Channel Task (AsyncExec F Results) SourceState) : M E Task W (AsyncCollectorState Channel Task (AsyncExec F Results) SourceState) := do
  JuliaLean.base.channels.closeDefault runtime.tasks.channelRuntime state.channel
  let _ ← JuliaLean.base.abstractarray.foreach (fun task => do
    match ← runtime.tasks.fetchTask task with
    | .completed => pure ()
    | .failed captured => runtime.tasks.throwCaptured captured) state.workerTasks
  pure { state with workerTasks := #[] }

/--
Julia source: base/asyncmap.jl:264-291 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function iterate(itr::AsyncCollector, state::AsyncCollectorState)
    if itr.nt_check && (length(state.worker_tasks) < itr.ntasks())
        start_worker_task!(state.worker_tasks, state.exec_func, state.chnl, state.batch_size)
    end

    # Get index and mapped function arguments from enumeration iterator.
    y = !isnothing(state.enum_state) ?
        iterate(itr.enumerator, state.enum_state) :
        iterate(itr.enumerator)
    if isnothing(y)
        wait_done(state)
        return nothing
    end
    (i, args), state.enum_state = y
    try
        put!(state.chnl, (i, args))
    catch
        # Prefer throwing a worker exception over the put! failure.
        for t in state.worker_tasks
            v = fetch(t)
            isa(v, Exception) && throw(v)
        end
        rethrow()
    end

    return (nothing, state)
end
```
-/
def asyncCollectorStep
    {E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState F Results Value BatchResult BatchState NT BatchArg Channel Cond Lock Waiter Token Ref Pool Backtrace Captured : Type}
    (runtime : AsyncMapRuntime E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState F Value BatchResult BatchState NT BatchArg Channel Cond Lock Waiter Token Ref Pool Backtrace Captured)
    (store : StoreOps E Task W Results Value)
    (collector : AsyncCollector (MapSource TupleSource ArraySource GenericSource) F Results NT BatchArg)
    (state : AsyncCollectorState Channel Task (AsyncExec F Results) SourceState) : M E Task W (CollectorIteration (AsyncCollector (MapSource TupleSource ArraySource GenericSource) F Results NT BatchArg) (AsyncCollectorState Channel Task (AsyncExec F Results) SourceState)) := do
  let state ← if collector.ntCheck then do
    let nt ← runtime.keywords.callNtFunction collector.ntasks
    let workerCount := JInt.wrap .i64 (Int.ofNat state.workerTasks.size)
    if workerCount.val < nt.val then
      let tasks ← startWorkerTask runtime store state.execFunc state.channel state.batchSize state.workerTasks
      pure { state with workerTasks := tasks }
    else
      pure state
  else
    pure state
  match ← iterateEnumerated runtime.sources collector.enumerator state.enumState with
  | none =>
      let state ← waitDone runtime state
      pure ⟨collector, state, false⟩
  | some ((index, args), enumState) => do
      let state := { state with enumState := some enumState }
      let _ ← tryCatch
        (do
          let _ ← JuliaLean.base.channels.put runtime.tasks.channelRuntime (fun item => pure item) state.channel (index, args)
          pure ())
        (fun putError => do
          let _ ← JuliaLean.base.abstractarray.foreach (fun task => do
            match ← runtime.tasks.fetchTask task with
            | .completed => pure ()
            | .failed captured => runtime.tasks.throwCaptured captured) state.workerTasks
          throw putError)
      pure ⟨collector, state, true⟩

/--
Julia source: base/asyncmap.jl:237-255 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function iterate(itr::AsyncCollector)
    itr.ntasks = verify_ntasks(itr.enumerator, itr.ntasks)
    itr.batch_size = verify_batch_size(itr.batch_size)

    if itr.batch_size !== nothing
        exec_func = batch -> begin
            indices = map(x -> x[1], batch)
            batched_args = map(x -> x[2], batch)
            res = itr.f(batched_args)
            foreach(((j, v),) -> (itr.results[indices[j]] = v), enumerate(res))
        end
    else
        exec_func = (i, args) -> (itr.results[i] = itr.f(args...))
    end

    chnl, worker_tasks = setup_chnl_and_tasks(exec_func, itr.ntasks, itr.batch_size)
    return iterate(itr, AsyncCollectorState(chnl, worker_tasks, exec_func, itr.batch_size, nothing))
end
```
-/
def asyncCollectorStart
    {E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState F Results Value BatchResult BatchState NT BatchArg Channel Cond Lock Waiter Token Ref Pool Backtrace Captured : Type}
    (runtime : AsyncMapRuntime E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState F Value BatchResult BatchState NT BatchArg Channel Cond Lock Waiter Token Ref Pool Backtrace Captured)
    (store : StoreOps E Task W Results Value)
    (collector : AsyncCollector (MapSource TupleSource ArraySource GenericSource) F Results NT BatchArg) : M E Task W (CollectorIteration (AsyncCollector (MapSource TupleSource ArraySource GenericSource) F Results NT BatchArg) (AsyncCollectorState Channel Task (AsyncExec F Results) SourceState)) := do
  let ntasks ← verifyNtTasks runtime collector.enumerator collector.ntasks
  let batchSize ← match collector.batchSize with
    | .raw batchSize => verifyBatchSize runtime.keywords batchSize
    | .checked batchSize => match batchSize with
        | none => pure none
        | some size =>
            if size.val < 1 then
              let message ← batchSizeErrStr (fun n => pure (toString n.val)) size
              throw (.julia (.argumentError message))
            pure (some size)
  let collector := { collector with ntasks := ntasks, batchSize := .checked batchSize }
  let exec := match batchSize with
    | some _ => AsyncExec.batch collector.f collector.results
    | none => AsyncExec.single collector.f collector.results
  let (channel, workerTasks) ← setupChannelAndTasks runtime store exec ntasks batchSize
  let state : AsyncCollectorState Channel Task (AsyncExec F Results) SourceState := {
    channel := channel
    workerTasks := workerTasks
    execFunc := exec
    batchSize := batchSize
    enumState := none
  }
  asyncCollectorStep runtime store collector state

def iterateAsyncCollector
    {E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState F Results Value BatchResult BatchState NT BatchArg Channel Cond Lock Waiter Token Ref Pool Backtrace Captured : Type}
    (runtime : AsyncMapRuntime E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState F Value BatchResult BatchState NT BatchArg Channel Cond Lock Waiter Token Ref Pool Backtrace Captured)
    (store : StoreOps E Task W Results Value)
    (collector : AsyncCollector (MapSource TupleSource ArraySource GenericSource) F Results NT BatchArg)
    (state : Option (AsyncCollectorState Channel Task (AsyncExec F Results) SourceState)) : M E Task W (CollectorIteration (AsyncCollector (MapSource TupleSource ArraySource GenericSource) F Results NT BatchArg) (AsyncCollectorState Channel Task (AsyncExec F Results) SourceState)) := do
  match state with
  | none => asyncCollectorStart runtime store collector
  | some state => asyncCollectorStep runtime store collector state

def collectorActionIterator
    {E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState F Results Value BatchResult BatchState NT BatchArg Channel Cond Lock Waiter Token Ref Pool Backtrace Captured : Type}
    (runtime : AsyncMapRuntime E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState F Value BatchResult BatchState NT BatchArg Channel Cond Lock Waiter Token Ref Pool Backtrace Captured)
    (store : StoreOps E Task W Results Value)
    (collector : AsyncCollector (MapSource TupleSource ArraySource GenericSource) F Results NT BatchArg) :
    ActionIterator E Task W
      (AsyncCollector (MapSource TupleSource ArraySource GenericSource) F Results NT BatchArg ×
        Option (AsyncCollectorState Channel Task (AsyncExec F Results) SourceState)) Unit :=
  { initial := (collector, none)
    next := fun (collector, state) => do
      let result ← iterateAsyncCollector runtime store collector state
      if result.yielded then
        pure (some ((), (result.collector, some result.state)))
      else
        pure none }

/--
Julia source: base/asyncmap.jl:95-96 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Narrow element type and reshape to try to match what `map` would return.
_asyncmap_result(v, c1::Tuple) = Tuple(map(identity, v))
```
-/
def asyncMapResultTuple
    {E Task W Vector TupleSource ArraySource GenericSource Axes Reshaped Generator TupleResult ArrayResult GenericResult : Type}
    (ops : AsyncMapResultOps E Task W Vector TupleSource ArraySource GenericSource Axes Reshaped Generator TupleResult ArrayResult GenericResult)
    (values : Vector) (_source : TupleSource) : M E Task W (AsyncMapOutput TupleResult ArrayResult GenericResult) := do
  let values ← ops.mapIdentity values
  pure (.tuple (← ops.tuple values))

/--
Julia source: base/asyncmap.jl:97-97 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_asyncmap_result(v, c1::AbstractArray) = collect_similar(c1, Generator(identity, reshape(v, axes(c1))))
```
-/
def asyncMapResultArray
    {E Task W Vector TupleSource ArraySource GenericSource Axes Reshaped Generator TupleResult ArrayResult GenericResult : Type}
    (ops : AsyncMapResultOps E Task W Vector TupleSource ArraySource GenericSource Axes Reshaped Generator TupleResult ArrayResult GenericResult)
    (values : Vector) (source : ArraySource) : M E Task W (AsyncMapOutput TupleResult ArrayResult GenericResult) := do
  let axes ← ops.axesArray source
  let reshaped ← ops.reshape values axes
  let generator := ops.identityGenerator reshaped
  pure (.array (← ops.collectSimilar source generator))

/--
Julia source: base/asyncmap.jl:99-99 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_asyncmap_result(v, c1, ::HasShape) = collect(Generator(identity, reshape(v, axes(c1))))
```
-/
def asyncMapResultHasShape
    {E Task W Vector TupleSource ArraySource GenericSource Axes Reshaped Generator TupleResult ArrayResult GenericResult : Type}
    (ops : AsyncMapResultOps E Task W Vector TupleSource ArraySource GenericSource Axes Reshaped Generator TupleResult ArrayResult GenericResult)
    (values : Vector) (source : GenericSource) (_dimensions : Nat) : M E Task W (AsyncMapOutput TupleResult ArrayResult GenericResult) := do
  let axes ← ops.axesGeneric source
  let reshaped ← ops.reshape values axes
  let generator := ops.identityGenerator reshaped
  pure (.generic (← ops.collect generator))

/--
Julia source: base/asyncmap.jl:100-101 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_asyncmap_result(v, _, _) = map(identity, v)

```
-/
def asyncMapResultOther
    {E Task W Vector TupleSource ArraySource GenericSource Axes Reshaped Generator TupleResult ArrayResult GenericResult : Type}
    (ops : AsyncMapResultOps E Task W Vector TupleSource ArraySource GenericSource Axes Reshaped Generator TupleResult ArrayResult GenericResult)
    (values : Vector) (_source : GenericSource) (_iteratorSize : JuliaLean.base.iterators.IteratorSizeTag) : M E Task W (AsyncMapOutput TupleResult ArrayResult GenericResult) := do
  pure (.generic (← ops.mapIdentityGeneric values))

/--
Julia source: base/asyncmap.jl:98-98 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_asyncmap_result(v, c1) = _asyncmap_result(v, c1, IteratorSize(c1))
```
-/
def asyncMapResultGeneric
    {E Task W Vector TupleSource ArraySource GenericSource Axes Reshaped Generator TupleResult ArrayResult GenericResult : Type}
    (ops : AsyncMapResultOps E Task W Vector TupleSource ArraySource GenericSource Axes Reshaped Generator TupleResult ArrayResult GenericResult)
    (values : Vector) (source : GenericSource) : M E Task W (AsyncMapOutput TupleResult ArrayResult GenericResult) := do
  let iteratorSize ← ops.iteratorSize source
  match iteratorSize with
  | .hasShape dimensions => asyncMapResultHasShape ops values source dimensions
  | other => asyncMapResultOther ops values source other

def asyncMapResultDispatch
    {E Task W Vector TupleSource ArraySource GenericSource Axes Reshaped Generator TupleResult ArrayResult GenericResult : Type}
    (ops : AsyncMapResultOps E Task W Vector TupleSource ArraySource GenericSource Axes Reshaped Generator TupleResult ArrayResult GenericResult)
    (values : Vector) (source : AsyncMapSource TupleSource ArraySource GenericSource) :
    M E Task W (AsyncMapOutput TupleResult ArrayResult GenericResult) := do
  match source with
  | .tuple tuple => asyncMapResultTuple ops values tuple
  | .array array => asyncMapResultArray ops values array
  | .generic generic => asyncMapResultGeneric ops values generic

/--
Julia source: base/asyncmap.jl:344-356 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

"""
    asyncmap!(f, results, c...; ntasks=0, batch_size=nothing)

Like [`asyncmap`](@ref), but stores output in `results` rather than
returning a collection.

$(_DOCS_ALIASING_WARNING)
"""
function asyncmap!(f, r, c1, c...; ntasks=0, batch_size=nothing)
    foreach(identity, AsyncCollector(f, r, c1, c...; ntasks=ntasks, batch_size=batch_size))
    r
end
```
-/
def asyncmapBang
    {E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState F Results Value BatchResult BatchState NT BatchArg Channel Cond Lock Waiter Token Ref Pool Backtrace Captured : Type}
    (runtime : AsyncMapRuntime E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState F Value BatchResult BatchState NT BatchArg Channel Cond Lock Waiter Token Ref Pool Backtrace Captured)
    (store : StoreOps E Task W Results Value)
    (f : F) (results : Results) (inputs : Inputs) (ntasks : NT) (batchSize : Option BatchArg) : M E Task W Results := do
  let collector ← makeAsyncCollector runtime f results inputs ntasks batchSize
  let iterator := collectorActionIterator runtime store collector
  let _ ← JuliaLean.base.abstractarray.foreach (fun _ => pure ()) iterator
  pure results

/--
Julia source: base/asyncmap.jl:5-94 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    asyncmap(f, c...; ntasks=0, batch_size=nothing)

Uses multiple concurrent tasks to map `f` over a collection (or multiple
equal length collections). For multiple collection arguments, `f` is
applied elementwise.

The output is guaranteed to be the same order as the elements of the collection(s) `c`.

`ntasks` specifies the number of tasks to run concurrently.
Depending on the length of the collections, if `ntasks` is unspecified,
up to 100 tasks will be used for concurrent mapping.

`ntasks` can also be specified as a zero-arg function. In this case, the
number of tasks to run in parallel is checked before processing every element and a new
task started if the value of `ntasks_func` is greater than the current number
of tasks.

If `batch_size` is specified, the collection is processed in batch mode. `f` must
then be a function that must accept a `Vector` of argument tuples and must
return a vector of results. The input vector will have a length of `batch_size` or less.

The following examples highlight execution in different tasks by returning
the `objectid` of the tasks in which the mapping function is executed.

First, with `ntasks` undefined, each element is processed in a different task.
```julia-repl
julia> tskoid() = objectid(current_task());

julia> asyncmap(x->tskoid(), 1:5)
5-element Vector{UInt64}:
 0x6e15e66c75c75853
 0x440f8819a1baa682
 0x9fb3eeadd0c83985
 0xebd3e35fe90d4050
 0x29efc93edce2b961

julia> length(unique(asyncmap(x->tskoid(), 1:5)))
5
```

With `ntasks=2` all elements are processed in 2 tasks.
```julia-repl
julia> asyncmap(x->tskoid(), 1:5; ntasks=2)
5-element Vector{UInt64}:
 0x027ab1680df7ae94
 0xa23d2f80cd7cf157
 0x027ab1680df7ae94
 0xa23d2f80cd7cf157
 0x027ab1680df7ae94

julia> length(unique(asyncmap(x->tskoid(), 1:5; ntasks=2)))
2
```

With `batch_size` defined, the mapping function needs to be changed to accept an array
of argument tuples and return an array of results. `map` is used in the modified mapping
function to achieve this.
```julia-repl
julia> batch_func(input) = map(x->string("args_tuple: ", x, ", element_val: ", x[1], ", task: ", tskoid()), input)
batch_func (generic function with 1 method)

julia> asyncmap(batch_func, 1:5; ntasks=2, batch_size=2)
5-element Vector{String}:
 "args_tuple: (1,), element_val: 1, task: 9118321258196414413"
 "args_tuple: (2,), element_val: 2, task: 4904288162898683522"
 "args_tuple: (3,), element_val: 3, task: 9118321258196414413"
 "args_tuple: (4,), element_val: 4, task: 4904288162898683522"
 "args_tuple: (5,), element_val: 5, task: 9118321258196414413"
```
"""
function asyncmap(f, c...; ntasks=0, batch_size=nothing)
    src = isone(length(c)) ? c[1] : zip(c...)
    if haslength(src)
        n = length(src)
        results = Vector{Any}(undef, n)
    else
        results = Dict{Int,Any}()
    end

    foreach(identity, AsyncCollector(f, results, c...; ntasks=ntasks, batch_size=batch_size))

    if results isa Dict
        v = Any[results[i] for i in 1:length(results)]
    else
        v = results
    end
    return _asyncmap_result(v, src)
end

````
-/
def asyncmap
    {E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState F Value BatchResult BatchState NT BatchArg Channel Cond Lock Waiter Token Ref Pool Backtrace Captured Vector Dict Axes Reshaped Generator TupleResult ArrayResult GenericResult : Type}
    (runtime : AsyncMapRuntime E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState F Value BatchResult BatchState NT BatchArg Channel Cond Lock Waiter Token Ref Pool Backtrace Captured)
    (storage : AsyncMapOutputOps E Task W Vector Dict Value)
    (resultOps : AsyncMapResultOps E Task W Vector TupleSource ArraySource GenericSource Axes Reshaped Generator TupleResult ArrayResult GenericResult)
    (f : F) (inputs : Inputs) (ntasks : NT) (batchSize : Option BatchArg) :
    M E Task W (AsyncMapOutput TupleResult ArrayResult GenericResult) := do
  let inputCount ← runtime.sources.collectionLength inputs
  let source ← if inputCount.val == 1 then do
      let collection ← runtime.sources.firstCollection inputs
      runtime.sources.fromCollection collection
    else
      runtime.sources.zip inputs
  let results ← if ← runtime.sources.hasLength source then do
      let count ← runtime.sources.length source
      pure (.vector (← storage.newVector count))
    else
      pure (.dict (← storage.newDict))
  let resultStore := storeAsyncResults storage
  let collector ← makeAsyncCollector runtime f results inputs ntasks batchSize
  let iterator := collectorActionIterator runtime resultStore collector
  let _ ← JuliaLean.base.abstractarray.foreach (fun _ => pure ()) iterator
  let values ← match results with
    | .dict dict => dictionaryResultsVector storage dict
    | .vector vector => pure vector
  asyncMapResultDispatch resultOps values source

/--
Julia source: base/asyncmap.jl:187-193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# Special handling for some types.
function asyncmap(f, s::AbstractString; kwargs...)
    s2 = Vector{Char}(undef, length(s))
    asyncmap!(f, s2, s; kwargs...)
    return String(s2)
end
```
-/
def asyncmapString
    {E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState F Value BatchResult BatchState NT BatchArg Channel Cond Lock Waiter Token Ref Pool Backtrace Captured String CharVector : Type}
    (runtime : AsyncMapRuntime E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState F Value BatchResult BatchState NT BatchArg Channel Cond Lock Waiter Token Ref Pool Backtrace Captured)
    (store : StoreOps E Task W CharVector Value)
    (stringOps : AsyncStringOps E Task W String CharVector Inputs)
    (f : F) (source : String) (ntasks : NT) (batchSize : Option BatchArg) : M E Task W String := do
  let result ← stringOps.allocateCharVector (← stringOps.length source)
  let _ ← asyncmapBang runtime store f result (stringOps.singletonInput source) ntasks batchSize
  stringOps.toString result

def dictStoreOps
    {E Task W Vector Dict Value : Type}
    (ops : AsyncMapOutputOps E Task W Vector Dict Value) : StoreOps E Task W Dict Value :=
  ⟨ops.setDict⟩

/--
Julia source: base/asyncmap.jl:309-312 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function AsyncGenerator(f, c...; ntasks=0)
    AsyncGenerator(AsyncCollector(f, Dict{Int,Any}(), c...; ntasks=ntasks))
end
```
-/
def newAsyncGenerator
    {E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState F Value BatchResult BatchState NT BatchArg Channel Cond Lock Waiter Token Ref Pool Backtrace Captured Vector Dict : Type}
    (runtime : AsyncMapRuntime E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState F Value BatchResult BatchState NT BatchArg Channel Cond Lock Waiter Token Ref Pool Backtrace Captured)
    (storage : AsyncMapOutputOps E Task W Vector Dict Value)
    (f : F) (inputs : Inputs) (ntasks : NT) :
    M E Task W (AsyncGenerator (AsyncCollector (MapSource TupleSource ArraySource GenericSource) F Dict NT BatchArg)) := do
  let results ← storage.newDict
  let collector ← makeAsyncCollector runtime f results inputs ntasks none
  pure ⟨collector⟩

def asyncGeneratorInitialState
    {CollectorState : Type} : AsyncGeneratorState CollectorState :=
  { i := int 0, collectorDone := false, collectorState := none }

/--
Julia source: base/asyncmap.jl:319-340 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function iterate(itr::AsyncGenerator, state::AsyncGeneratorState=AsyncGeneratorState(0, false, nothing))
    state.i += 1

    results_dict = itr.collector.results
    while !state.collector_done && !haskey(results_dict, state.i)
        y = !isnothing(state.collector_state) ?
            iterate(itr.collector, state.collector_state) :
            iterate(itr.collector)
        if isnothing(y)
            # All input consumed; async tasks may still be in flight.
            state.collector_done = true
            break
        end
        _, state.collector_state = y
    end
    state.collector_done && isempty(results_dict) && return nothing
    r = results_dict[state.i]
    delete!(results_dict, state.i)

    return (r, state)
end
```
-/
def iterateAsyncGenerator
    {E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState F Value BatchResult BatchState NT BatchArg Channel Cond Lock Waiter Token Ref Pool Backtrace Captured Vector Dict : Type}
    (runtime : AsyncMapRuntime E Task W Inputs Collection TupleSource ArraySource GenericSource Args SourceState F Value BatchResult BatchState NT BatchArg Channel Cond Lock Waiter Token Ref Pool Backtrace Captured)
    (storage : AsyncMapOutputOps E Task W Vector Dict Value)
    (generator : AsyncGenerator (AsyncCollector (MapSource TupleSource ArraySource GenericSource) F Dict NT BatchArg))
    (state : AsyncGeneratorState (AsyncCollectorState Channel Task (AsyncExec F Dict) SourceState) := asyncGeneratorInitialState) :
    M E Task W (AsyncGenerator (AsyncCollector (MapSource TupleSource ArraySource GenericSource) F Dict NT BatchArg) ×
      AsyncGeneratorState (AsyncCollectorState Channel Task (AsyncExec F Dict) SourceState) ×
      Option (Value × AsyncGeneratorState (AsyncCollectorState Channel Task (AsyncExec F Dict) SourceState))) := do
  let state := { state with i := state.i + int 1 }
  let cursor ← JuliaLean.base.channels.loop (fun (collector, state) => do
    if state.collectorDone then
      pure (.inl (collector, state))
    else if ← storage.dictHasKey collector.results state.i then
      pure (.inl (collector, state))
    else
      let iteration ← iterateAsyncCollector runtime (dictStoreOps storage) collector state.collectorState
      let state := { state with collectorState := some iteration.state }
      if iteration.yielded then
        pure (.inr (iteration.collector, state))
      else
        pure (.inl (iteration.collector, { state with collectorDone := true }))) (generator.collector, state)
  let generator := { generator with collector := cursor.1 }
  let state := cursor.2
  if state.collectorDone && (← storage.dictIsEmpty generator.collector.results) then
    pure (generator, state, none)
  else
    let value ← storage.dictGet generator.collector.results state.i
    storage.dictDelete generator.collector.results state.i
    pure (generator, state, some (value, state))

/--
Julia source: base/asyncmap.jl:341-342 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

IteratorSize(::Type{AsyncGenerator}) = SizeUnknown()
```
-/
def asyncGeneratorIteratorSize : JuliaLean.base.iterators.IteratorSizeTag := .sizeUnknown

/--
Julia source: base/asyncmap.jl:343-343 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorEltype(::Type{AsyncGenerator}) = EltypeUnknown()
```
-/
def asyncGeneratorIteratorEltype : JuliaLean.base.iterators.IteratorEltypeTag := .eltypeUnknown

end JuliaLean.base.asyncmap

namespace JuliaLean.Tasks



/-- Default worker count from `base/asyncmap.jl:116-129`. Naturals model the
accepted nonnegative integer `ntasks` values. -/
def normalizedNTasks (length ntasks : Nat) : Nat :=
  if ntasks = 0 then max 1 (min 100 length) else ntasks
/-- Initial worker count when `ntasks` is a function,
`base/asyncmap.jl:133-150`. Julia asserts an `Int`, changes zero to one, then
iterates `1:nt`; that range is empty for a negative result. -/
def dynamicWorkerCount (ntasks : Int) : Nat :=
  if ntasks = 0 then 1 else ntasks.toNat
def validBatchSize : Option Nat → Bool
  | none => true
  | some n => 0 < n
abbrev ResultSlots := Nat → Option Nat
/-- Indexed assignment `results[i] = f(args...)`,
`base/asyncmap.jl:238-250`. Out-of-range jobs are ignored by this total model;
enumeration never generates them. -/
def asyncStore (f : Nat → Nat) (inputs : List Nat) (slots : ResultSlots)
    (index : Nat) : ResultSlots :=
  match inputs[index]? with
  | none => slots
  | some input => fun i => if i = index then some (f input) else slots i
/-- Apply indexed completions in an arbitrary order. Each order is one worker
interleaving, including interleavings made by batching. -/
def asyncRun (f : Nat → Nat) (inputs : List Nat) : List Nat → ResultSlots
  | [] => fun _ => none
  | index :: order => asyncStore f inputs (asyncRun f inputs order) index
/-- The full model keeps the public worker and batch parameters explicit.
They affect which completion orders are possible, while indexed writes make
the result at an input position independent of that order. -/
def asyncmapModel (f : Nat → Nat) (inputs : List Nat) (ntasks : Nat)
    (batchSize : Option Nat) (order : List Nat) : ResultSlots :=
  let _workers := normalizedNTasks inputs.length ntasks
  let _batch := batchSize
  asyncRun f inputs order

end JuliaLean.Tasks

namespace JuliaLean.Tasks



/-! ## base/asyncmap.jl:76-152, public result shaping and validation -/

inductive AsyncShape where | tuple | array (dimensions : List Nat) | linear
  deriving Repr, DecidableEq

def asyncResultShape (shape : AsyncShape) (values : List Nat) : Nat × List Nat :=
  match shape with
  | .tuple => (values.length, values)
  | .array dimensions => (dimensions.foldl (· * ·) 1, values)
  | .linear => (values.length, values)

def verifyBatchSizeBody : Option Int → Except Unit (Option Nat)
  | none => .ok none
  | some size => if size < 1 then .error () else .ok (some size.toNat)

inductive NTasksArgument where | constant (count : Int) | dynamic (initial : Int)
  deriving Repr, DecidableEq

def verifyNTasksBody (length : Option Nat) : NTasksArgument → Except Unit Nat
  | .constant count =>
      if count < 0 then .error ()
      else if count == 0 then .ok (max 1 (min 100 (length.getD 100)))
      else .ok count.toNat
  | .dynamic initial => .ok (if initial == 0 then 1 else initial.toNat)

def asyncStringResult (characters : List Nat) : List Nat := characters

/-! ## base/asyncmap.jl:154-291, workers and AsyncCollector -/

structure CollectorState where
  pending : List (Nat × Nat)
  results : Nat → Option Nat
  workers : Nat

def collectorStart (jobs : List (Nat × Nat)) (workers : Nat) : CollectorState :=
  ⟨jobs, fun _ => none, workers⟩

def collectorComplete (f : Nat → Nat) (state : CollectorState) (index value : Nat) :
    CollectorState :=
  { state with results := fun i => if i == index then some (f value) else state.results i }

def collectorGrow (state : CollectorState) (requested : Nat) : CollectorState :=
  if state.workers < requested then { state with workers := state.workers + 1 } else state

/-! ## base/asyncmap.jl:306-356, AsyncGenerator and asyncmap! -/

structure GeneratorState where
  nextIndex : Nat := 1
  done : Bool := false
  results : Nat → Option Nat := fun _ => none

inductive GeneratorStep where | value (value : Nat) | blocked | finished
  deriving Repr, DecidableEq

def generatorStep (state : GeneratorState) : GeneratorStep × GeneratorState :=
  if state.done && state.results state.nextIndex == none then (.finished, state)
  else
    match state.results state.nextIndex with
    | some value => (.value value, { state with nextIndex := state.nextIndex + 1 })
    | none => (.blocked, state)

def asyncmapBangBody (result : List Nat) : List Nat := result

end JuliaLean.Tasks
