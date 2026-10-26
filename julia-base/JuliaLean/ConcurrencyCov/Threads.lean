import JuliaLean.ConcurrencyCov.Common
import JuliaLean.Channels.ThreadsFor

/-!
# `base/threadingconstructs.jl` (master `bbfa0ce4150`)

The C runtime's thread tables (`jl_n_threads`, `jl_n_threads_per_pool`,
`jl_n_threadpools`, `jl_n_gcthreads`, the current thread's id) are the fields of
`ThreadRt`; `jl_threadpoolid` is mirrored from `src/threading.c:324-337`.

The code-generating helpers of `@threads` are modelled by what the generated code
computes. An iterator is the list of its elements (`collect`ed where the source
collects it) with its shape (`axes`, as dimension lengths); the loop or
comprehension body is a Lean function of the element. A task is identified by its
`tid`; the per-task index ranges are the Channels area's model of
`_work_distribution_code` (`JuliaLean.Channels.threadsIterations`).
-/

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
