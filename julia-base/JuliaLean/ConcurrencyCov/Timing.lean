import JuliaLean.ConcurrencyCov.Common
import JuliaLean.MathFuncs.Log
import JuliaLean.Printf.Model
import JuliaLean.Float.Extras

/-!
# `base/timing.jl` (master `bbfa0ce4150`)

The runtime counters read through `ccall` (`jl_gc_num`, `jl_cumulative_compile_time_ns`,
...) are the fields of `TimingRt`; the reentrant enable counters of the C runtime
(`jl_measure_compile_time_enabled`, `jl_force_trace_compile_timing_enabled`,
`jl_force_trace_dispatch_enabled`, `Base.TIMING_IMPORTS`, `Threads.LOCK_PROFILING`)
are integers incremented and decremented exactly as `src/jlapi.c:843-856` and
`src/gf.c:4233-4245` do.

Floating-point steps use the Float area's IEEE model, `log` the MathFuncs model of
`base/special/log.jl` and `Ryu.writefixed` the Printf model. A printed value is
tagged with its Julia type (`PVal`): `print(::Int64)` writes decimal digits, while
`print(::Float64)` always writes a decimal point or an exponent.
-/

namespace JuliaLean.ConcurrencyCov.Timing

open JuliaLean JuliaLean.Float JuliaLean.ConcurrencyCov

/-! ## GC counters, lines 13-114 -/

/-- The `GC_Num` fields that `timing.jl` reads (all `Int64`). -/
structure GcNum where
  allocd : I64
  deferred_alloc : I64
  total_allocd : I64
  malloc : I64
  realloc : I64
  poolalloc : I64
  bigalloc : I64
  freecall : I64
  total_time : I64
  pause : I64
  full_sweep : I64
  deriving DecidableEq, Repr

/-- `GC_Diff`, lines 82-92. -/
structure GcDiff where
  allocd : I64
  malloc : I64
  realloc : I64
  poolalloc : I64
  bigalloc : I64
  freecall : I64
  total_time : I64
  pause : I64
  full_sweep : I64
  deriving DecidableEq, Repr

/-- `gc_total_bytes(gc_num)`, lines 94-95 (wrapping `Int64` additions). -/
def gcTotalBytes (g : GcNum) : I64 := g.allocd + g.deferred_alloc + g.total_allocd

/-- `GC_Diff(new, old)`, lines 97-110. -/
def gcDiff (new old : GcNum) : GcDiff :=
  let old_allocd := gcTotalBytes old
  let new_allocd := gcTotalBytes new
  { allocd := new_allocd - old_allocd, malloc := new.malloc - old.malloc,
    realloc := new.realloc - old.realloc, poolalloc := new.poolalloc - old.poolalloc,
    bigalloc := new.bigalloc - old.bigalloc, freecall := new.freecall - old.freecall,
    total_time := new.total_time - old.total_time, pause := new.pause - old.pause,
    full_sweep := new.full_sweep - old.full_sweep }

/-- `gc_alloc_count(diff)`, lines 112-114. -/
def gcAllocCount (d : GcDiff) : I64 := d.malloc + d.realloc + d.poolalloc + d.bigalloc

/-! ## Runtime queries, lines 79 and 116-197 -/

/-- The C runtime state that `timing.jl` reads and writes. -/
structure TimingRt where
  gcNum : GcNum
  /-- `jl_cumulative_compile_time_ns()` and `jl_cumulative_recompile_time_ns()`. -/
  compileNs : U64
  recompileNs : U64
  /-- `jl_measure_compile_time_enabled`, a reentrancy counter. -/
  compileTiming : Int
  /-- `jl_gc_total_hrtime()`. -/
  gcHrtime : U64
  /-- `jl_gc_live_bytes()`. -/
  liveBytes : I64
  /-- `jl_gc_page_utilization_stats`, `JL_GC_N_MAX_POOLS = 51` doubles. -/
  pageUtil : List F64
  /-- `jl_full_sweep_reasons`, one `UInt64` per reason. -/
  sweepReasons : List U64
  /-- `jl_jit_total_bytes()`. -/
  jitBytes : U64
  /-- `jl_gc_get_total_bytes` result. -/
  totalBytes : I64
  /-- `jl_force_trace_compile_timing_enabled`, `jl_force_trace_dispatch_enabled`,
  `Base.TIMING_IMPORTS`, `Threads.LOCK_PROFILING`, `Threads.LOCK_CONFLICT_COUNT`. -/
  traceCompile : Int
  traceDispatch : Int
  timingImports : Int
  lockProfiling : Int
  lockConflicts : Int
  /-- `time_ns()`. -/
  clock : U64

/-- `gc_num()`, line 79. -/
def gcNumQ (rt : TimingRt) : GcNum := rt.gcNum

/-- `cumulative_compile_time_ns()`, lines 117-121. -/
def cumulativeCompileTimeNs (rt : TimingRt) : U64 × U64 := (rt.compileNs, rt.recompileNs)

/-- `cumulative_compile_timing(b)`, lines 123-130: one reentrant increment or decrement. -/
def cumulativeCompileTiming (b : Bool) (rt : TimingRt) : TimingRt :=
  if b then { rt with compileTiming := rt.compileTiming + 1 }
  else { rt with compileTiming := rt.compileTiming - 1 }

/-- `gc_time_ns()`, line 133. -/
def gcTimeNs (rt : TimingRt) : U64 := rt.gcHrtime

/-- `gc_live_bytes()`, lines 143-146: `Int(...)` of an `Int64` is the identity. -/
def gcLiveBytes (rt : TimingRt) : I64 :=
  let num := gcNumQ rt
  rt.liveBytes + num.allocd + num.deferred_alloc

/-- `JL_GC_N_MAX_POOLS`, line 149. -/
def nMaxPools : Nat := 51

/-- `gc_page_utilization_data()`, lines 150-153: a view of the first 51 doubles. -/
def gcPageUtilizationData (rt : TimingRt) : List F64 := rt.pageUtil.take nMaxPools

/-- `FULL_SWEEP_REASONS`, lines 158-159. -/
def fullSweepReasonNames : List String :=
  ["FULL_SWEEP_REASON_SWEEP_ALWAYS_FULL", "FULL_SWEEP_REASON_FORCED_FULL_SWEEP",
   "FULL_SWEEP_REASON_USER_MAX_EXCEEDED", "FULL_SWEEP_REASON_LARGE_PROMOTION_RATE",
   "FULL_SWEEP_REASON_LARGE_HEAP_GROWTH"]

/-- `d[r] = reasons_as_array[i]` converts a `UInt64` to the `Int64` value type. -/
def toI64 (x : U64) : R I64 :=
  if x.val ≤ IntTy.max .i64 then .ok (i64 x.val) else .error .inexactError

/-- `full_sweep_reasons()`, lines 175-187 (stock GC): the dictionary as its
key/value list in insertion order. -/
def fullSweepReasons (rt : TimingRt) : R (List (String × I64)) :=
  let arr := rt.sweepReasons.take fullSweepReasonNames.length
  (fullSweepReasonNames.zip arr).mapM fun (r, v) => do return (r, ← toI64 v)

/-- `jit_total_bytes()`, lines 195-197. -/
def jitTotalBytes (rt : TimingRt) : U64 := rt.jitBytes

/-! ## Unit selection and number formatting, lines 199-252 -/

/-- A number produced by `prettyprint_getunits`: the input itself (`Int64`) or a
`Float64` quotient. -/
inductive Num where
  | int (v : I64)
  | flt (x : F64)
  deriving DecidableEq, Repr

def Num.toF64 : Num → F64
  | .int v => F64.ofJInt v
  | .flt x => x

/-- `Float64` operations whose errors are Julia exceptions. -/
def liftJl {α : Type} : Jl α → R α
  | .ok a => .ok a
  | .error (.domainError _) => .error .domainError
  | .error (.inexactError _) => .error .inexactError
  | .error _ => .error .domainError

/-- `^(x::Int, p::Int)` (`power_by_squaring`, base/intfuncs.jl): a negative power
of an integer other than `±1` throws `DomainError`; products wrap. -/
def powInt (x p : I64) : R I64 :=
  if p.val < 0 then
    if x.val = 1 then .ok x
    else if x.val = -1 then .ok (if p.val % 2 = 0 then i64 1 else x)
    else .error .domainError
  else .ok (JInt.wrap .i64 (x.val ^ p.val.toNat))

/-- `prettyprint_getunits(value, numunits, factor)`, lines 202-210, for the
`Int64` values its callers pass. -/
def prettyprintGetunits (value : I64) (numunits : Nat) (factor : I64) : R (Num × I64) :=
  if value.val = 0 ∨ value.val = 1 then .ok (.int value, i64 1)
  else do
    let lv ← liftJl (MathFuncs.log (F64.ofJInt value))
    let lf ← liftJl (MathFuncs.log (F64.ofJInt factor))
    let unit ← liftJl (F64.ceilInt .i64 (F64.div lv lf))
    let unit := if (numunits : Int) < unit.val then i64 numunits else unit
    let p ← powInt factor (unit - i64 1)
    return (.flt (F64.div (F64.ofJInt value) (F64.ofJInt p)), unit)

/-- ASCII bytes as a string. -/
def bytesStr (bs : List Nat) : String := String.ofList (bs.map Char.ofNat)

/-- `Ryu.writefixed(x, prec)` with the default flags. -/
def writefixed (x : F64) (prec : Int) : R String :=
  match Printf.writefixed x prec false false false false with
  | .ok bs => .ok (bytesStr bs)
  | .error _ => .error (.argumentError "precision must be non-negative")

/-- `_mem_units` and `_cnt_units`, lines 200-201. -/
def memUnits : List String := ["byte", "KiB", "MiB", "GiB", "TiB", "PiB"]
def cntUnits : List String := ["", " k", " M", " G", " T", " P"]

/-- 1-based indexing of a unit table; `BoundsError` outside. -/
def unitAt (us : List String) (i : I64) : R String :=
  if 1 ≤ i.val ∧ i.val ≤ us.length then .ok (us.getD (i.val - 1).toNat "")
  else .error .boundsError

/-- `Int(x)` of a `prettyprint_getunits` number. -/
def numToInt : Num → R I64
  | .int v => .ok v
  | .flt x => liftJl (F64.int .i64 x)

/-- `bytes == 1` for an `Int64` or `Float64` number. -/
def numIsOne : Num → Bool
  | .int v => v.val = 1
  | .flt x => F64.eq x F64.one

/-- `format_bytes(bytes; binary)`, lines 243-252. -/
def formatBytes (bytes : I64) (binary : Bool := true) : R String := do
  let units := if binary then memUnits else cntUnits
  let factor := if binary then i64 1024 else i64 1000
  let (b, mb) ← prettyprintGetunits bytes units.length factor
  if mb.val = 1 then
    let n ← numToInt b
    let u ← unitAt memUnits mb
    return toString n.val ++ " " ++ u ++ (if numIsOne b then "" else "s")
  else
    let s ← writefixed b.toF64 3
    let u ← unitAt units mb
    return s ++ (if binary then " " ++ u else u ++ "B")

/-! ## Report printing, lines 212-324 -/

/-- A printed value tagged with its Julia type. -/
inductive PVal where
  | int (v : I64)
  | flt (x : F64)
  deriving DecidableEq, Repr

def PVal.nonzero : PVal → Bool
  | .int v => v.val ≠ 0
  | .flt x => !F64.iszero x

/-- `"                "[1:(19 - length(str))]`: 16 blanks, sliced. -/
def blanks (str : String) : R String :=
  let n : Int := 19 - str.length
  if n ≤ 0 then .ok ""
  else if n ≤ 16 then .ok (String.ofList (List.replicate n.toNat ' '))
  else .error .boundsError

/-- One line written by `padded_nonzero_print`. -/
structure Line where
  label : String
  pad : String
  value : PVal
  deriving DecidableEq, Repr

/-- `padded_nonzero_print(value, str, always_print = true)`, lines 212-217. -/
def paddedNonzeroPrint (value : PVal) (str : String) (alwaysPrint : Bool := true) :
    R (List Line) :=
  if alwaysPrint || value.nonzero then do
    let b ← blanks str
    return [⟨str, b, value⟩]
  else .ok []

/-- The arguments of `time_print` as `@time` passes them (line 405). -/
structure TimeArgs where
  elapsedtime : F64
  bytes : I64 := i64 0
  gctime : I64 := i64 0
  allocs : I64 := i64 0
  lock_conflicts : I64 := i64 0
  compile_time : F64 := F64.zero
  recompile_time : F64 := F64.zero
  newline : Bool := false
  msg : Option String := none

def fpos (x : F64) : Bool := F64.lt F64.zero x
def f100 : F64 := F64.ofInt 100
def f1e9 : F64 := F64.ofInt 1000000000

/-- The allocation-count part, lines 268-274. -/
def allocsPart (a : TimeArgs) : R String := do
  let (scaled, ma) ← prettyprintGetunits a.allocs cntUnits.length (i64 1000)
  let head ← if ma.val = 1 then do
      let n ← numToInt scaled
      let u ← unitAt cntUnits ma
      pure (toString n.val ++ u ++ (if numIsOne scaled then " allocation: " else " allocations: "))
    else do
      let s ← writefixed scaled.toF64 2
      let u ← unitAt cntUnits ma
      pure (s ++ u ++ " allocations: ")
  return head ++ (← formatBytes a.bytes)

/-- `time_print(io, elapsedtime, bytes, gctime, allocs, lock_conflicts,
compile_time, recompile_time, newline; msg)`, lines 254-305: the text written. -/
def timePrint (a : TimeArgs) : R String := do
  let timestr ← writefixed (F64.div a.elapsedtime f1e9) 6
  let lead := match a.msg with
    | some m => m ++ ": "
    | none => if timestr.length < 10 then String.ofList (List.replicate (10 - timestr.length) ' ') else ""
  let parens := a.bytes.val ≠ 0 || a.allocs.val ≠ 0 || 0 < a.gctime.val ||
    0 < a.lock_conflicts.val || fpos a.compile_time
  let had_allocs := a.bytes.val ≠ 0 || a.allocs.val ≠ 0
  let s1 ← if had_allocs then allocsPart a else pure ""
  let s2 ← if 0 < a.gctime.val then do
      let p ← writefixed (F64.div (F64.ofJInt (i64 100 * a.gctime)) a.elapsedtime) 2
      pure ((if had_allocs then ", " else "") ++ p ++ "% gc time")
    else pure ""
  let s3 := if 0 < a.lock_conflicts.val then
      (if had_allocs || 0 < a.gctime.val then ", " else "") ++ toString a.lock_conflicts.val ++
        " lock conflict" ++ (if a.lock_conflicts.val = 1 then "" else "s")
    else ""
  let s4 ← if fpos a.compile_time then do
      let p ← writefixed (F64.div (F64.mul f100 a.compile_time) a.elapsedtime) 2
      pure ((if had_allocs || 0 < a.gctime.val || 0 < a.lock_conflicts.val then ", " else "") ++
        p ++ "% compilation time")
    else pure ""
  let s5 ← if fpos a.recompile_time then do
      let perc := F64.div (F64.mul f100 a.recompile_time) a.compile_time
      let p ← if F64.lt perc F64.one then pure "<1" else writefixed perc 0
      pure (": " ++ p ++ "% of which was recompilation")
    else pure ""
  return lead ++ timestr ++ " seconds" ++ (if parens then " (" else "") ++ s1 ++ s2 ++ s3 ++ s4 ++
    s5 ++ (if parens then ")" else "") ++ (if a.newline then "\n" else "")

/-- What `timev_print` writes: the `time_print` text and the counter lines. -/
structure TimevOut where
  head : String
  lines : List Line
  deriving DecidableEq, Repr

/-- `timev_print(elapsedtime, diff, lock_conflicts, compile_times; msg)`,
lines 307-324, with `elapsedtime = ret.time*1e9` as `@timev` passes it (line 478). -/
def timevPrint (elapsedtime : F64) (diff : GcDiff) (lock_conflicts : I64)
    (compile_times : F64 × F64) (msg : Option String) : R TimevOut := do
  let allocs := gcAllocCount diff
  let head ← timePrint {
    elapsedtime := elapsedtime, bytes := diff.allocd, gctime := diff.total_time,
    allocs := allocs, lock_conflicts := lock_conflicts, compile_time := compile_times.1,
    recompile_time := compile_times.2, newline := true, msg := msg }
  let l1 ← paddedNonzeroPrint (.flt elapsedtime) "elapsed time (ns)"
  let l2 ← paddedNonzeroPrint (.int diff.total_time) "gc time (ns)"
  let l3 ← paddedNonzeroPrint (.int diff.allocd) "bytes allocated"
  let l4 ← paddedNonzeroPrint (.int diff.poolalloc) "pool allocs"
  let l5 ← paddedNonzeroPrint (.int diff.bigalloc) "non-pool GC allocs"
  let l6 ← paddedNonzeroPrint (.int diff.malloc) "malloc() calls" false
  let l7 ← paddedNonzeroPrint (.int diff.realloc) "realloc() calls" false
  let l8 ← paddedNonzeroPrint (.int diff.freecall) "free() calls" (0 < diff.malloc.val)
  let minor_collects := diff.pause - diff.full_sweep
  let l9 ← paddedNonzeroPrint (.int minor_collects) "minor collections"
  let l10 ← paddedNonzeroPrint (.int diff.full_sweep) "full collections"
  return ⟨head, l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6 ++ l7 ++ l8 ++ l9 ++ l10⟩

/-! ## Macros, lines 326-798

A macro's expansion is modelled by what the expanded code does: user code is an
`Outcome` (a value or an exception) together with the counter deltas it causes. -/

/-- The effect of evaluating the user expression: its outcome, and the time, GC
counters and compile time that pass while it runs. -/
structure Run where
  outcome : Outcome
  dt : U64
  gcAfter : GcNum
  compileAfter : U64 × U64
  conflicts : Int

/-- `@__tryfinally(ex, fin)`, lines 329-334: `fin` runs after `ex` on every exit;
the result is `ex`'s outcome. -/
def tryfinally {σ : Type} (ex : σ → Outcome × σ) (fin : σ → σ) (s : σ) : Outcome × σ :=
  let (o, s) := ex s
  (o, fin s)

/-- The `NamedTuple` built by `@timed`, lines 749-758. -/
structure Timed where
  value : Nat
  time : F64
  bytes : I64
  gctime : F64
  gcstats : GcDiff
  lock_conflicts : Int
  compile_time : F64
  recompile_time : F64
  deriving DecidableEq, Repr

/-- `-%` on `UInt64`. -/
def subw (a b : U64) : U64 := a - b

/-- `@timed ex`, lines 732-760. The counters are enabled before `ex`, the
`@__tryfinally` block disables them on every exit, and an exception from `ex`
propagates after that. -/
def timed (r : Run) (rt : TimingRt) : R Timed × TimingRt :=
  let rt := { rt with lockProfiling := rt.lockProfiling + 1 }
  let lc0 := rt.lockConflicts
  let stats := gcNumQ rt
  let t0 := rt.clock
  let rt := cumulativeCompileTiming true rt
  let c0 := cumulativeCompileTimeNs rt
  -- running `ex`
  let rt := { rt with
    clock := rt.clock + r.dt, gcNum := r.gcAfter, compileNs := r.compileAfter.1,
    recompileNs := r.compileAfter.2, lockConflicts := rt.lockConflicts + r.conflicts }
  -- the `finally` part
  let elapsed := subw rt.clock t0
  let rt := cumulativeCompileTiming false rt
  let c1 := cumulativeCompileTimeNs rt
  let cs := (subw c1.1 c0.1, subw c1.2 c0.2)
  let lc := rt.lockConflicts - lc0
  let rt := { rt with lockProfiling := rt.lockProfiling - 1 }
  match r.outcome with
  | .error e => (.error e, rt)
  | .ok v =>
    let diff := gcDiff (gcNumQ rt) stats
    (.ok {
      value := v, time := F64.div (F64.ofJInt elapsed) f1e9, bytes := diff.allocd,
      gctime := F64.div (F64.ofJInt diff.total_time) f1e9, gcstats := diff, lock_conflicts := lc,
      compile_time := F64.div (F64.ofJInt cs.1) f1e9,
      recompile_time := F64.div (F64.ofJInt cs.2) f1e9 }, rt)

/-- `string(_msg)` of the description, or `nothing`. -/
def msgStr (msg : Option String) : Option String := msg

/-- `@time msg ex`, lines 400-408 (`@time ex` is `@time nothing ex`, lines 395-399):
the printed report and the returned value. -/
def time (msg : Option String) (r : Run) (rt : TimingRt) : R (String × Nat) × TimingRt :=
  match timed r rt with
  | (.error e, rt) => (.error e, rt)
  | (.ok ret, rt) =>
    let report := timePrint {
      elapsedtime := F64.mul ret.time f1e9, bytes := ret.gcstats.allocd,
      gctime := ret.gcstats.total_time, allocs := gcAllocCount ret.gcstats,
      lock_conflicts := i64 ret.lock_conflicts, compile_time := F64.mul ret.compile_time f1e9,
      recompile_time := F64.mul ret.recompile_time f1e9, newline := true, msg := msgStr msg }
    (report.map (fun s => (s, ret.value)), rt)

/-- `@showtime ex`, lines 425-429: `@time` with the printed expression as message. -/
def showtime (exprText : String) (r : Run) (rt : TimingRt) : R (String × Nat) × TimingRt :=
  time (some exprText) r rt

/-- `@timev msg ex`, lines 473-481 (`@timev ex` is `@timev nothing ex`, lines 468-472). -/
def timev (msg : Option String) (r : Run) (rt : TimingRt) : R (TimevOut × Nat) × TimingRt :=
  match timed r rt with
  | (.error e, rt) => (.error e, rt)
  | (.ok ret, rt) =>
    let out := timevPrint (F64.mul ret.time f1e9) ret.gcstats (i64 ret.lock_conflicts)
      (F64.mul ret.compile_time f1e9, F64.mul ret.recompile_time f1e9) (msgStr msg)
    (out.map (fun o => (o, ret.value)), rt)

/-- `@elapsed ex`, lines 501-508: seconds as a `Float64`, the value discarded. -/
def elapsed (r : Run) (rt : TimingRt) : R F64 × TimingRt :=
  let t0 := rt.clock
  let rt := { rt with clock := rt.clock + r.dt, gcNum := r.gcAfter }
  match r.outcome with
  | .error e => (.error e, rt)
  | .ok _ => (.ok (F64.div (F64.ofJInt (subw rt.clock t0)) f1e9), rt)

/-- `gc_bytes(b::Ref{Int64})` and `gc_bytes()`, lines 511-517. -/
def gcBytes (rt : TimingRt) : I64 := rt.totalBytes

/-- The effect of a measured call on the total-bytes counter and GC counters. -/
structure Alloc where
  outcome : Outcome
  bytesAfter : I64
  gcAfter : GcNum

/-- `allocated(f, args...)`, lines 519-526 (and the v1.11 form of `@allocated`,
lines 568-576): the change of `jl_gc_get_total_bytes`. -/
def allocated (a : Alloc) (rt : TimingRt) : R I64 × TimingRt :=
  let b0 := gcBytes rt
  let rt := { rt with totalBytes := a.bytesAfter, gcNum := a.gcAfter }
  match a.outcome with
  | .error e => (.error e, rt)
  | .ok _ => (.ok (gcBytes rt - b0), rt)

/-- `allocations(f, args...)`, lines 529-534 (and lines 579-590): the change of
the allocation counters. -/
def allocations (a : Alloc) (rt : TimingRt) : R I64 × TimingRt :=
  let stats := gcNumQ rt
  let rt := { rt with totalBytes := a.bytesAfter, gcNum := a.gcAfter }
  match a.outcome with
  | .error e => (.error e, rt)
  | .ok _ => (.ok (gcAllocCount (gcDiff (gcNumQ rt) stats)), rt)

/-! ### Call-shape analysis of `@allocated`/`@allocations`, lines 537-592 -/

/-- The expression forms `is_simply_call` distinguishes. -/
inductive Ast where
  | sym (name : String)
  | quoteNode
  /-- A non-AST literal value (number, string, ...). -/
  | lit
  | call (args : List Ast)
  | splat (args : List Ast)
  /-- Any other expression head. -/
  | other (head : String) (args : List Ast)

/-- `isoperator`, restricted to the operator names that can follow a leading dot. -/
def isOperatorName (s : String) : Bool :=
  s ∈ ["+", "-", "*", "/", "\\", "^", "==", "!=", "<", "<=", ">", ">=", "&", "|", "⊻", "%",
    "÷", "=>", "<<", ">>", ">>>", "//", "∘", "≈", "≠", "≤", "≥", "∈", "∉", "~", "!", "√"]

/-- `is_simple_atom(a)`, line 538. -/
def isSimpleAtom : Ast → Bool
  | .quoteNode | .sym _ | .lit => true
  | _ => false

/-- The loop test of `is_simply_call`, lines 541-542: an atom, or `x...` of an atom. -/
def isSimpleArg (a : Ast) : Bool :=
  isSimpleAtom a || (match a with | .splat [b] => isSimpleAtom b | _ => false)

/-- `is_simply_call(ex)`, lines 537-554. -/
def isSimplyCall : Ast → R Bool
  | .call args =>
    if !args.all isSimpleArg then .ok false
    else match args with
      | [] => .error .boundsError
      | .sym sa :: _ =>
        if sa.startsWith "." && !sa.endsWith "." && isOperatorName (sa.drop 1).toString then .ok false
        else .ok true
      | _ :: _ => .ok true
  | _ => .ok false

/-- What `_gen_allocation_measurer(ex, fname)` generates, lines 556-592. -/
inductive Measurer where
  /-- `Base.allocated(f, args...)` / `Base.allocations(f, args...)` on the call itself. -/
  | direct (fname : String) (call : List Ast)
  /-- The same on the zero-argument closure `(() -> ex)`. -/
  | wrapped (fname : String) (ex : Ast)
  /-- Counting around `ex` in place. -/
  | inPlace (fname : String) (ex : Ast)

def genAllocationMeasurer (ex : Ast) (fname : String) : R Measurer :=
  match ex with
  | .call args => do
    let simple ← isSimplyCall ex
    if simple then return .direct fname args else return .wrapped fname ex
  | _ =>
    if fname = "allocated" then .ok (.inPlace fname ex)
    else if fname = "allocations" then .ok (.inPlace fname ex)
    else .error (.assertionError "unexpected fname")

/-- `@allocated ex` and `@allocations ex`, lines 622-624 and 643-645. -/
def allocatedMacro (ex : Ast) : R Measurer := genAllocationMeasurer ex "allocated"
def allocationsMacro (ex : Ast) : R Measurer := genAllocationMeasurer ex "allocations"

/-- `@lock_conflicts ex`, lines 672-683. -/
def lockConflictsMacro (r : Run) (rt : TimingRt) : R Int × TimingRt :=
  let rt := { rt with lockProfiling := rt.lockProfiling + 1 }
  let c0 := rt.lockConflicts
  let rt := { rt with lockConflicts := rt.lockConflicts + r.conflicts }
  let rt := { rt with lockProfiling := rt.lockProfiling - 1 }
  match r.outcome with
  | .error e => (.error e, rt)
  | .ok _ => (.ok (rt.lockConflicts - c0), rt)

/-- The three counter-bracketing macros `@time_imports`, `@trace_compile` and
`@trace_dispatch`, lines 764-798: increment, run, decrement in the `finally`. -/
inductive Bracket where | timeImports | traceCompile | traceDispatch
  deriving DecidableEq, Repr

def Bracket.get (b : Bracket) (rt : TimingRt) : Int :=
  match b with
  | .timeImports => rt.timingImports
  | .traceCompile => rt.traceCompile
  | .traceDispatch => rt.traceDispatch

def Bracket.add (b : Bracket) (d : Int) (rt : TimingRt) : TimingRt :=
  match b with
  | .timeImports => { rt with timingImports := rt.timingImports + d }
  | .traceCompile => { rt with traceCompile := rt.traceCompile + d }
  | .traceDispatch => { rt with traceDispatch := rt.traceDispatch + d }

/-- The body of the bracketing macros. `inside` is the counter value user code observes. -/
def bracket (b : Bracket) (o : Outcome) (rt : TimingRt) : (Outcome × Int) × TimingRt :=
  let rt := b.add 1 rt
  let inside := b.get rt
  let (res, rt) := tryfinally (fun s => (o, s)) (b.add (-1)) rt
  ((res, inside), rt)

end JuliaLean.ConcurrencyCov.Timing
