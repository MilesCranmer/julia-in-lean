import JuliaLean.Proofs.base.locks_mt.common
import JuliaLean.base.special.log
import JuliaLean.stdlib.Printf.src.Printf
import JuliaLean.base.rounding
import JuliaLean.Core
import JuliaLean.base.int
import JuliaLean.base.channels
import JuliaLean.base.expr

/-!
# Model of `base/timing.jl`

Typed models of Julia's garbage-collection counters, compile-time counters,
allocation measurements, and timing output. C calls, pointers, IO writes,
numeric dispatch, function calls, and syntax operations are typed interfaces. Macro
expansions remain visible as untranslated source blocks; compiler method metadata
is represented by byte-sized model constants.
-/

namespace JuliaLean.base.timing

open JuliaLean

abbrev I64 := JInt .i64
abbrev U64 := JInt .u64
abbrev I32 := JInt .i32
abbrev M (E Task W A : Type) := JuliaLean.base.channels.M E Task W A

def int (value : Int) : I64 := JInt.lit .i64 value

/- Julia structs mirrored from the source. -/
/--
Julia source: base/timing.jl:3-77 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# This type must be kept in sync with the C struct in src/gc-interface.h
struct GC_Num
    # (GC Internal) Number of allocated bytes since the last collection. This field is reset
    # after the end of every garbage collection cycle, so it will always be zero if observed
    # during execution of Julia user code
    allocd::Int64
    # (GC Internal) Number of allocated bytes within a `gc_disable/gc_enable` block. This field is
    # reset after every garbage collection cycle and will always be zero in case of no use
    # of `gc_disable/gc_enable` blocks
    deferred_alloc::Int64
    # (GC Internal) Number of bytes freed in the current collection cycle. This field is
    # reset after every garbage collection cycle and will always be zero when observed
    # during execution of Julia user code. It's incremented as memory is reclaimed during a collection,
    # used to gather some statistics within the collection itself and reset at the end of a GC cycle.
    freed::Int64
    # Number of `malloc/calloc` calls (never reset by the runtime)
    malloc::Int64
    # Number of `realloc` calls (never reset by the runtime)
    realloc::Int64
    # Number of pool allocation calls (never reset by the runtime)
    # NOTE: Julia's stock GC uses an internal (pool) allocator for objects up to 2032 bytes.
    # Larger objects are allocated through `malloc/calloc`.
    poolalloc::Int64
    # Number of allocations for "big objects" (non-array objects larger than 2032 bytes)
    # (never reset by the runtime)
    bigalloc::Int64
    # Number of `free` calls (never reset by the runtime)
    freecall::Int64
    # Total time spent in garbage collection (never reset by the runtime)
    total_time::Int64
    # (GC internal) Total number of bytes allocated since the program started
    total_allocd::Int64
    # (GC internal) Per-thread allocation quota before triggering a GC
    # NOTE: This field is no longer used by the heuristics in the stock GC
    interval::Csize_t
    # Number of GC pauses completed so far (never reset by the runtime)
    pause::Cint
    # Number of full GC sweeps completed so far (never reset by the runtime)
    full_sweep::Cint
    # Maximum pause duration observed so far in nanoseconds
    max_pause::Int64
    # Maximum number of bytes allocated at any point in time.
    # NOTE: This is aggregated over objects, not pages
    max_memory::Int64
    # Time taken to reach a safepoint in the last GC cycle in nanoseconds
    time_to_safepoint::Int64
    # Maximum time taken to reach a safepoint across all GCs in nanoseconds
    max_time_to_safepoint::Int64
    # Total time taken to reach safepoints across all GCs in nanoseconds
    total_time_to_safepoint::Int64
    # Time spent in the last GC sweeping phase in nanoseconds
    sweep_time::Int64
    # Time spent in the last GC marking phase in nanoseconds
    mark_time::Int64
    # Time spent sweeping stack pools in the last GC in nanoseconds
    stack_pool_sweep_time::Int64
    # Total time spent in sweeping phase across all GCs in nanoseconds
    total_sweep_time::Int64
    # Total time spent walking pool allocated pages during sweeping phase across all GCs in nanoseconds
    total_sweep_page_walk_time::Int64
    # Total time spent in madvise calls during sweeping phase across all GCs in nanoseconds
    total_sweep_madvise_time::Int64
    # Total time spent in freeing malloc'd memory during sweeping phase across all GCs in nanoseconds
    total_sweep_free_mallocd_memory_time::Int64
    # Total time spent in marking phase across all GCs in nanoseconds
    total_mark_time::Int64
    # Total time spent sweeping stack pools across all GCs in nanoseconds
    total_stack_pool_sweep_time::Int64
    # Timestamp of the last full GC sweep in nanoseconds
    last_full_sweep::Int64
    # Timestamp of the last incremental GC sweep in nanoseconds
    last_incremental_sweep::Int64
    # Number of tracked image objects referencing non-image objects
    image_remset_size::Int64
end
```
-/
structure GC_Num where
  allocd : I64
  deferredAlloc : I64
  freed : I64
  malloc : I64
  realloc : I64
  poolalloc : I64
  bigalloc : I64
  freecall : I64
  totalTime : I64
  totalAllocd : I64
  interval : U64
  pause : I32
  fullSweep : I32
  maxPause : I64
  maxMemory : I64
  timeToSafepoint : I64
  maxTimeToSafepoint : I64
  totalTimeToSafepoint : I64
  sweepTime : I64
  markTime : I64
  stackPoolSweepTime : I64
  totalSweepTime : I64
  totalSweepPageWalkTime : I64
  totalSweepMadviseTime : I64
  totalSweepFreeMallocdMemoryTime : I64
  totalMarkTime : I64
  totalStackPoolSweepTime : I64
  lastFullSweep : I64
  lastIncrementalSweep : I64
  imageRemsetSize : I64

/--
Julia source: base/timing.jl:81-92 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# This type is to represent differences in the counters, so fields may be negative
struct GC_Diff
    allocd      ::Int64 # Bytes allocated
    malloc      ::Int64 # Number of GC aware malloc()
    realloc     ::Int64 # Number of GC aware realloc()
    poolalloc   ::Int64 # Number of pool allocation
    bigalloc    ::Int64 # Number of big (non-pool) allocation
    freecall    ::Int64 # Number of GC aware free()
    total_time  ::Int64 # Time spent in garbage collection
    pause       ::Int64 # Number of GC pauses
    full_sweep  ::Int64 # Number of GC full collection
end
```
-/
structure GC_Diff where
  allocd : I64
  malloc : I64
  realloc : I64
  poolalloc : I64
  bigalloc : I64
  freecall : I64
  totalTime : I64
  pause : I64
  fullSweep : I64

structure TimingC (E Task W Pointer PageArray : Type) where
  gcNum : M E Task W GC_Num
  cumulativeCompileTimeNs : M E Task W U64
  cumulativeRecompileTimeNs : M E Task W U64
  enableCompileTiming : M E Task W Unit
  disableCompileTiming : M E Task W Unit
  gcTotalHrtime : M E Task W U64
  gcLiveBytes : M E Task W I64
  gcPageUtilizationPointer : M E Task W Pointer
  unsafeWrapPageUtilization : Pointer → I64 → Bool → M E Task W PageArray
  jitTotalBytes : M E Task W U64

structure FullSweepOps (E Task W Symbol Dict Pointer : Type) where
  stockGC : Bool
  newDict : M E Task W Dict
  symbol : String → Symbol
  pointer : M E Task W Pointer
  unsafeWrapReasons : Pointer → I64 → Bool → M E Task W (Array U64)
  getReason : Array U64 → I64 → M E Task W U64
  setDict : Dict → Symbol → I64 → M E Task W Unit
  reasonToInt : U64 → M E Task W I64

structure RefOps (E Task W Ref : Type) where
  newUninitialized : M E Task W Ref
  newRef : I64 → M E Task W Ref
  read : Ref → M E Task W I64
  gcBytesRef : Ref → M E Task W Unit

structure PrettyOps (E Task W Number Float : Type) where
  zero : Number
  isZero : Number → M E Task W Bool
  isOne : Number → M E Task W Bool
  greaterZero : Number → M E Task W Bool
  lessThanOne : Float → M E Task W Bool
  logValue : Number → M E Task W Float
  logFactor : I64 → M E Task W Float
  divideFloat : Float → Float → M E Task W Float
  ceilInt : Float → M E Task W I64
  divideByPower : Number → I64 → I64 → M E Task W Number
  fromInt : I64 → M E Task W Number
  toInt : Number → M E Task W I64
  toFloat64 : Number → M E Task W Float
  numberString : Number → M E Task W String
  writeFixed : Float → Nat → M E Task W String
  unitAt : List String → I64 → M E Task W String

structure TimePrintOps (E Task W IO Buffer Elapsed Bytes GcTime Allocations Locks CompileTime RecompileTime Float : Type) where
  elapsed : PrettyOps E Task W Elapsed Float
  bytes : PrettyOps E Task W Bytes Float
  allocations : PrettyOps E Task W Allocations Float
  gcTime : PrettyOps E Task W GcTime Float
  locks : PrettyOps E Task W Locks Float
  compileTime : PrettyOps E Task W CompileTime Float
  recompileTime : PrettyOps E Task W RecompileTime Float
  elapsedSeconds : Elapsed → M E Task W Float
  gcPercent : GcTime → Elapsed → M E Task W Float
  compilePercent : CompileTime → Elapsed → M E Task W Float
  recompilePercent : RecompileTime → CompileTime → M E Task W Float
  sprint : (Buffer → M E Task W Unit) → M E Task W String
  writeBuffer : Buffer → String → M E Task W Unit
  writeIO : IO → String → M E Task W Unit
  stdout : M E Task W IO

structure PaddedPrintOps (E Task W IO Number : Type) where
  isZero : Number → M E Task W Bool
  numberString : Number → M E Task W String
  stdout : M E Task W IO
  println : IO → List String → M E Task W Unit

structure TimeVPrintOps
    (E Task W IO Buffer Elapsed Locks CompileTime RecompileTime Float : Type) where
  time : TimePrintOps E Task W IO Buffer Elapsed I64 I64 I64 Locks CompileTime RecompileTime Float
  elapsed : PaddedPrintOps E Task W IO Elapsed
  gcTime : PaddedPrintOps E Task W IO I64
  bytes : PaddedPrintOps E Task W IO I64
  allocations : PaddedPrintOps E Task W IO I64

structure FunctionCallOps (E Task W F Args Result : Type) where
  call : F → Args → M E Task W Result

open JuliaLean.base.expr

structure AllocationSyntaxOps (L : Type) where
  leaves : LeafOps L
  isOperator : Sym → Bool

inductive AllocationError where
  | expression (error : ExprError)
  | assertionError (message : String)

private def timingLineNode {L : Type} (line : Nat) : Value L :=
  .lineNumberNode (JInt.wrap .i64 (Int.ofNat line)) (.symbol "timing.jl")

private def timingBlock {L : Type} (lines : List (Nat × Value L)) : Value L :=
  .expr "block" (lines.flatMap fun (line, expression) =>
    [timingLineNode line, expression])

private def timingCall {L : Type} (function : Value L) (arguments : List (Value L)) : Value L :=
  .expr "call" (function :: arguments)

private def timingBaseCall {L : Type} (function : Sym) (arguments : List (Value L)) : Value L :=
  timingCall (.expr "." [.symbol "Base", .quoteNode (.symbol function)]) arguments

private def timingForceCompile {L : Type} (line : Nat) : Value L :=
  .expr "macrocall" [
    .expr "." [.symbol "Experimental", .quoteNode (.symbol "@force_compile")],
    timingLineNode line]

private def timingRefZero {L : Type} (ops : AllocationSyntaxOps L) : Value L :=
  timingCall (.expr "curly" [.symbol "Ref", .symbol "Int64"])
    [.leaf (ops.leaves.ofInt (JInt.lit .i64 0))]

private def timingLocal {L : Type} (name : Sym) (value : Value L) : Value L :=
  .expr "local" [.expr "=" [.symbol name, value]]

private def timingAssign {L : Type} (name : Sym) (value : Value L) : Value L :=
  .expr "=" [.symbol name, value]

private def allocatedQuote {L : Type} (ops : AllocationSyntaxOps L) (expression : Value L) :
    Value L :=
  timingBlock [
    (569, timingForceCompile 569),
    (570, timingLocal "b0" (timingRefZero ops)),
    (571, timingLocal "b1" (timingRefZero ops)),
    (572, timingCall (.symbol "gc_bytes") [.symbol "b0"]),
    (573, .expr "escape" [expression]),
    (574, timingCall (.symbol "gc_bytes") [.symbol "b1"]),
    (575, timingCall (.symbol "-") [
      .expr "ref" [.symbol "b1"], .expr "ref" [.symbol "b0"]])]

private def allocationsQuote {L : Type} (ops : AllocationSyntaxOps L) (expression : Value L) :
    Value L :=
  timingBlock [
    (580, timingForceCompile 580),
    (584, timingLocal "b1" (timingRefZero ops)),
    (585, timingAssign "stats" (timingBaseCall "gc_num" [])),
    (586, .expr "escape" [expression]),
    (587, timingLocal "diff" (timingBaseCall "GC_Diff" [
      timingBaseCall "gc_num" [], .symbol "stats"])),
    (588, timingCall (.symbol "gc_bytes") [.symbol "b1"]),
    (589, timingBaseCall "gc_alloc_count" [.symbol "diff"])]

private def simpleCallAtom {L : Type} : Value L → Bool
  | .quoteNode _ | .symbol _ => true
  | value => !isa_ast_node value

/--
Julia source: base/timing.jl:94-95 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
gc_total_bytes(gc_num::GC_Num) =
    gc_num.allocd + gc_num.deferred_alloc + gc_num.total_allocd
```
-/
def gcTotalBytes (value : GC_Num) : I64 :=
  (value.allocd + value.deferredAlloc) + value.totalAllocd

/--
Julia source: base/timing.jl:97-110 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function GC_Diff(new::GC_Num, old::GC_Num)
    # logic from `jl_gc_total_bytes`
    old_allocd = gc_total_bytes(old)
    new_allocd = gc_total_bytes(new)
    return GC_Diff(new_allocd       - old_allocd,
                   new.malloc       - old.malloc,
                   new.realloc      - old.realloc,
                   new.poolalloc    - old.poolalloc,
                   new.bigalloc     - old.bigalloc,
                   new.freecall     - old.freecall,
                   new.total_time   - old.total_time,
                   new.pause        - old.pause,
                   new.full_sweep   - old.full_sweep)
end
```
-/
def gcDiff (newValue oldValue : GC_Num) : GC_Diff :=
  let oldAllocd := gcTotalBytes oldValue
  let newAllocd := gcTotalBytes newValue
  {
    allocd := newAllocd - oldAllocd
    malloc := newValue.malloc - oldValue.malloc
    realloc := newValue.realloc - oldValue.realloc
    poolalloc := newValue.poolalloc - oldValue.poolalloc
    bigalloc := newValue.bigalloc - oldValue.bigalloc
    freecall := newValue.freecall - oldValue.freecall
    totalTime := newValue.totalTime - oldValue.totalTime
    pause := JInt.wrap .i64 (newValue.pause - oldValue.pause).val
    fullSweep := JInt.wrap .i64 (newValue.fullSweep - oldValue.fullSweep).val
  }

/--
Julia source: base/timing.jl:112-114 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function gc_alloc_count(diff::GC_Diff)
    diff.malloc + diff.realloc + diff.poolalloc + diff.bigalloc
end
```
-/
def gcAllocCount (value : GC_Diff) : I64 :=
  ((value.malloc + value.realloc) + value.poolalloc) + value.bigalloc

/--
Julia source: base/timing.jl:117-121 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function cumulative_compile_time_ns()
    comp = ccall(:jl_cumulative_compile_time_ns, UInt64, ())
    recomp = ccall(:jl_cumulative_recompile_time_ns, UInt64, ())
    return comp, recomp
end
```
-/
def cumulativeCompileTimeNs {E Task W Pointer PageArray : Type} (ops : TimingC E Task W Pointer PageArray) :
    M E Task W (U64 × U64) := do
  let compileTime ← ops.cumulativeCompileTimeNs
  let recompileTime ← ops.cumulativeRecompileTimeNs
  pure (compileTime, recompileTime)

/--
Julia source: base/timing.jl:123-130 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function cumulative_compile_timing(b::Bool)
    if b
        ccall(:jl_cumulative_compile_timing_enable, Cvoid, ())
    else
        ccall(:jl_cumulative_compile_timing_disable, Cvoid, ())
    end
    return
end
```
-/
def cumulativeCompileTiming {E Task W Pointer PageArray : Type}
    (ops : TimingC E Task W Pointer PageArray) (enabled : Bool) : M E Task W Unit := do
  if enabled then ops.enableCompileTiming else ops.disableCompileTiming

/--
Julia source: base/timing.jl:135-146 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Base.gc_live_bytes()

Return the total size (in bytes) of objects currently in memory.
This is computed as the total size of live objects after
the last garbage collection, plus the number of bytes allocated
since then.
"""
function gc_live_bytes()
    num = gc_num()
    Int(ccall(:jl_gc_live_bytes, Int64, ())) + num.allocd + num.deferred_alloc
end
```
-/
def gcLiveBytes {E Task W Pointer PageArray : Type}
    (ops : TimingC E Task W Pointer PageArray) : M E Task W I64 := do
  let counters ← ops.gcNum
  let live ← ops.gcLiveBytes
  pure ((live + counters.allocd) + counters.deferredAlloc)

/--
Julia source: base/timing.jl:150-153 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function gc_page_utilization_data()
    page_utilization_raw = cglobal(:jl_gc_page_utilization_stats, Float64)
    return Base.unsafe_wrap(Array, page_utilization_raw, JL_GC_N_MAX_POOLS, own=false)
end
```
-/
def gcPageUtilizationData {E Task W Pointer PageArray : Type}
    (ops : TimingC E Task W Pointer PageArray) : M E Task W PageArray := do
  let pointer ← ops.gcPageUtilizationPointer
  ops.unsafeWrapPageUtilization pointer (int 51) false

/--
Julia source: base/timing.jl:155-160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Full sweep reasons are currently only available for the stock GC
@static if Base.USING_STOCK_GC
# must be kept in sync with `src/gc-stock.h``
const FULL_SWEEP_REASONS = [:FULL_SWEEP_REASON_SWEEP_ALWAYS_FULL, :FULL_SWEEP_REASON_FORCED_FULL_SWEEP,
                            :FULL_SWEEP_REASON_USER_MAX_EXCEEDED, :FULL_SWEEP_REASON_LARGE_PROMOTION_RATE, :FULL_SWEEP_REASON_LARGE_HEAP_GROWTH]
end
```
-/
def fullSweepReasonNames {Symbol : Type} (toSymbol : String → Symbol) (stockGC : Bool) : Option (List Symbol) :=
  if stockGC then
    some [
      toSymbol "FULL_SWEEP_REASON_SWEEP_ALWAYS_FULL",
      toSymbol "FULL_SWEEP_REASON_FORCED_FULL_SWEEP",
      toSymbol "FULL_SWEEP_REASON_USER_MAX_EXCEEDED",
      toSymbol "FULL_SWEEP_REASON_LARGE_PROMOTION_RATE",
      toSymbol "FULL_SWEEP_REASON_LARGE_HEAP_GROWTH"]
  else
    none

/--
Julia source: base/timing.jl:175-187 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function full_sweep_reasons()
    d = Dict{Symbol, Int64}()
    # populate the dictionary according to the reasons above for the stock GC
    # otherwise return an empty dictionary for now
    @static if Base.USING_STOCK_GC
        reason = cglobal(:jl_full_sweep_reasons, UInt64)
        reasons_as_array = Base.unsafe_wrap(Vector{UInt64}, reason, length(FULL_SWEEP_REASONS), own=false)
        for (i, r) in enumerate(FULL_SWEEP_REASONS)
            d[r] = reasons_as_array[i]
        end
    end
    return d
end
```
-/
def fullSweepReasons {E Task W Symbol Dict Pointer : Type}
    (ops : FullSweepOps E Task W Symbol Dict Pointer) : M E Task W Dict := do
  let result ← ops.newDict
  match fullSweepReasonNames ops.symbol ops.stockGC with
  | none => pure result
  | some names => do
      let pointer ← ops.pointer
      let reasons ← ops.unsafeWrapReasons pointer (int (Int.ofNat names.length)) false
      let _ ← JuliaLean.base.channels.loop (fun (index, remaining) => do
        match remaining with
        | [] => pure (.inl ())
        | name :: rest => do
            let count ← ops.getReason reasons index
            let count ← ops.reasonToInt count
            ops.setDict result name count
            pure (.inr (index + int 1, rest))) (int 1, names)
      pure result

/--
Julia source: base/timing.jl:202-210 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function prettyprint_getunits(value, numunits, factor)
    if value == 0 || value == 1
        return (value, 1)
    end
    unit = ceil(Int, log(value) / log(factor))
    unit = min(numunits, unit)
    number = value/factor^(unit-1)
    return number, unit
end
```
-/
def prettyprintGetUnits {E Task W Number Float : Type}
    (ops : PrettyOps E Task W Number Float) (value : Number) (numUnits factor : I64) :
    M E Task W (Number × I64) := do
  if ← ops.isZero value then
    pure (value, int 1)
  else if ← ops.isOne value then
    pure (value, int 1)
  else
    let logValue ← ops.logValue value
    let logFactor ← ops.logFactor factor
    let ratio ← ops.divideFloat logValue logFactor
    let unit ← ops.ceilInt ratio
    let unit := if numUnits.val < unit.val then numUnits else unit
    let number ← ops.divideByPower value factor (unit - int 1)
    pure (number, unit)

/--
Julia source: base/timing.jl:200-200 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const _mem_units = ["byte", "KiB", "MiB", "GiB", "TiB", "PiB"]
```
-/
def memUnits : List String := ["byte", "KiB", "MiB", "GiB", "TiB", "PiB"]
/--
Julia source: base/timing.jl:201-201 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const _cnt_units = ["", " k", " M", " G", " T", " P"]
```
-/
def countUnits : List String := ["", " k", " M", " G", " T", " P"]

/--
Julia source: base/timing.jl:212-217 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function padded_nonzero_print(value, str, always_print = true)
    if always_print || value != 0
        blanks = "                "[1:(19 - length(str))]
        println(str, ":", blanks, value)
    end
end
```
-/
def paddedNonzeroPrint {E Task W IO Number : Type}
    (ops : PaddedPrintOps E Task W IO Number) (value : Number) (label : String)
    (alwaysPrint : Bool := true) : M E Task W Unit := do
  let shouldPrint ← if alwaysPrint then pure true else do
    pure (!(← ops.isZero value))
  if shouldPrint then
    let padLength := 19 - Int.ofNat label.length
    let blanks ← if padLength <= 0 then
        pure ""
      else if padLength <= 16 then
        pure (String.ofList (List.replicate padLength.toNat ' '))
      else
        throw (.julia .boundsError)
    let valueString ← ops.numberString value
    let io ← ops.stdout
    ops.println io [label, ":", blanks, valueString]
  else
    pure ()

/--
Julia source: base/timing.jl:219-252 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    format_bytes(bytes; binary=true)

Format a given number of bytes into a human-readable string.

# Arguments
- `bytes`: The number of bytes to format.
- `binary=true`: If `true`, formats the bytes in binary units (powers of 1024). If `false`, uses decimal units (powers of 1000).

# Returns
`String`: A human-readable string representation of the bytes, formatted in either binary or decimal units based on the `binary` argument.

# Examples
```jldoctest
julia> Base.format_bytes(1024)
"1024 bytes"

julia> Base.format_bytes(10000)
"9.766 KiB"

julia> Base.format_bytes(10000, binary=false)
"10.000 kB"
```
"""
function format_bytes(bytes; binary=true) # also used by InteractiveUtils
    units = binary ? _mem_units : _cnt_units
    factor = binary ? 1024 : 1000
    bytes, mb = prettyprint_getunits(bytes, length(units), Int64(factor))
    if mb == 1
        return string(Int(bytes), " ", _mem_units[mb], bytes==1 ? "" : "s")
    else
        return string(Ryu.writefixed(Float64(bytes), 3), binary ? " $(units[mb])" : "$(units[mb])B")
    end
end
````
-/
def formatBytes {E Task W Number Float : Type}
    (ops : PrettyOps E Task W Number Float) (bytes : Number) (binary : Bool := true) :
    M E Task W String := do
  let units := if binary then memUnits else countUnits
  let factor := int (if binary then 1024 else 1000)
  let (scaledBytes, unit) ← prettyprintGetUnits ops bytes (int (Int.ofNat units.length)) factor
  if unit.val == 1 then
    let integer ← ops.toInt scaledBytes
    let unitName ← ops.unitAt memUnits unit
    let singular ← ops.isOne scaledBytes
    pure (toString integer.val ++ " " ++ unitName ++ if singular then "" else "s")
  else
    let value ← ops.toFloat64 scaledBytes
    let formatted ← ops.writeFixed value 3
    let unitName ← ops.unitAt units unit
    pure (formatted ++ if binary then " " ++ unitName else unitName ++ "B")

/--
Julia source: base/timing.jl:254-305 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function time_print(io::IO, elapsedtime, bytes=0, gctime=0, allocs=0, lock_conflicts=0, compile_time=0, recompile_time=0, newline=false;
                    msg::Union{String,Nothing}=nothing)
    timestr = Ryu.writefixed(Float64(elapsedtime/1e9), 6)
    str = sprint() do io
        if msg isa String
            print(io, msg, ": ")
        else
            print(io, length(timestr) < 10 ? (" "^(10 - length(timestr))) : "")
        end
        print(io, timestr, " seconds")
        parens = bytes != 0 || allocs != 0 || gctime > 0 || lock_conflicts > 0 || compile_time > 0
        parens && print(io, " (")
        had_allocs = bytes != 0 || allocs != 0
        if had_allocs
            allocs_scaled, ma = prettyprint_getunits(allocs, length(_cnt_units), Int64(1000))
            if ma == 1
                print(io, Int(allocs_scaled), _cnt_units[ma], allocs_scaled==1 ? " allocation: " : " allocations: ")
            else
                print(io, Ryu.writefixed(Float64(allocs_scaled), 2), _cnt_units[ma], " allocations: ")
            end
            print(io, format_bytes(bytes))
        end
        if gctime > 0
            if had_allocs
                print(io, ", ")
            end
            print(io, Ryu.writefixed(Float64(100*gctime/elapsedtime), 2), "% gc time")
        end
        if lock_conflicts > 0
            if had_allocs || gctime > 0
                print(io, ", ")
            end
            plural = lock_conflicts == 1 ? "" : "s"
            print(io, lock_conflicts, " lock conflict$plural")
        end
        if compile_time > 0
            if had_allocs || gctime > 0 || lock_conflicts > 0
                print(io, ", ")
            end
            print(io, Ryu.writefixed(Float64(100*compile_time/elapsedtime), 2), "% compilation time")
        end
        if recompile_time > 0
            perc = Float64(100 * recompile_time / compile_time)
            # use "<1" to avoid the confusing UX of reporting 0% when it's >0%
            print(io, ": ", perc < 1 ? "<1" : Ryu.writefixed(perc, 0), "% of which was recompilation")
        end
        parens && print(io, ")")
        newline && print(io, "\n")
    end
    print(io, str)
    nothing
end
```
-/
def timePrint
    {E Task W IO Buffer Elapsed Bytes GcTime Allocations Locks CompileTime RecompileTime Float : Type}
    (ops : TimePrintOps E Task W IO Buffer Elapsed Bytes GcTime Allocations Locks CompileTime RecompileTime Float)
    (elapsed : Elapsed) (bytes : Bytes := ops.bytes.zero)
    (gcTime : GcTime := ops.gcTime.zero) (allocations : Allocations := ops.allocations.zero)
    (lockConflicts : Locks := ops.locks.zero) (compileTime : CompileTime := ops.compileTime.zero)
    (recompileTime : RecompileTime := ops.recompileTime.zero)
    (newline : Bool := false) (msg : Option String := none) : M E Task W Unit := do
  let timestr ← ops.elapsed.writeFixed (← ops.elapsedSeconds elapsed) 6
  let rendered ← ops.sprint (fun io => do
    match msg with
    | some message => ops.writeBuffer io (message ++ ": ")
    | none =>
      if timestr.length < 10 then
        ops.writeBuffer io (String.ofList (List.replicate (10 - timestr.length) ' '))
      else
        pure ()
    ops.writeBuffer io timestr
    ops.writeBuffer io " seconds"
    let bytesZeroForParens ← ops.bytes.isZero bytes
    let bytesNonzeroForParens := !bytesZeroForParens
    let allocationsNonzeroForParens ← if bytesNonzeroForParens then
        pure false
      else do
        let allocationsZeroForParens ← ops.allocations.isZero allocations
        pure (!allocationsZeroForParens)
    let gcPositiveForParens ← if bytesNonzeroForParens || allocationsNonzeroForParens then
        pure false
      else
        ops.gcTime.greaterZero gcTime
    let locksPositiveForParens ← if bytesNonzeroForParens || allocationsNonzeroForParens || gcPositiveForParens then
        pure false
      else
        ops.locks.greaterZero lockConflicts
    let compilePositiveForParens ← if bytesNonzeroForParens || allocationsNonzeroForParens ||
        gcPositiveForParens || locksPositiveForParens then
        pure false
      else
        ops.compileTime.greaterZero compileTime
    let parens := bytesNonzeroForParens || allocationsNonzeroForParens ||
      gcPositiveForParens || locksPositiveForParens || compilePositiveForParens
    if parens then ops.writeBuffer io " (" else pure ()
    let bytesZero ← ops.bytes.isZero bytes
    let hadAllocations ← if bytesZero then do
        let allocationsZero ← ops.allocations.isZero allocations
        pure (!allocationsZero)
      else
        pure true
    if hadAllocations then do
      let (scaled, unit) ← prettyprintGetUnits ops.allocations allocations (int (Int.ofNat countUnits.length)) (int 1000)
      if unit.val == 1 then do
        let count ← ops.allocations.toInt scaled
        let unitName ← ops.allocations.unitAt countUnits unit
        let singular ← ops.allocations.isOne scaled
        ops.writeBuffer io (toString count.val ++ unitName ++ if singular then " allocation: " else " allocations: ")
      else do
        let value ← ops.allocations.toFloat64 scaled
        let formatted ← ops.allocations.writeFixed value 2
        let unitName ← ops.allocations.unitAt countUnits unit
        ops.writeBuffer io (formatted ++ unitName ++ " allocations: ")
      let formattedBytes ← formatBytes ops.bytes bytes
      ops.writeBuffer io formattedBytes
    else
      pure ()
    let gcPositive ← ops.gcTime.greaterZero gcTime
    if gcPositive then do
      if hadAllocations then ops.writeBuffer io ", " else pure ()
      let percentage ← ops.gcPercent gcTime elapsed
      let formatted ← ops.elapsed.writeFixed percentage 2
      ops.writeBuffer io (formatted ++ "% gc time")
    else
      pure ()
    let locksPositive ← ops.locks.greaterZero lockConflicts
    if locksPositive then do
      let separatorNeeded ← if hadAllocations then pure true else ops.gcTime.greaterZero gcTime
      if separatorNeeded then ops.writeBuffer io ", " else pure ()
      let singular ← ops.locks.isOne lockConflicts
      let count ← ops.locks.numberString lockConflicts
      ops.writeBuffer io (count ++ " lock conflict" ++ if singular then "" else "s")
    else
      pure ()
    let compilePositive ← ops.compileTime.greaterZero compileTime
    if compilePositive then do
      let separatorNeeded ← if hadAllocations then pure true else do
        let gcPositive ← ops.gcTime.greaterZero gcTime
        if gcPositive then pure true else ops.locks.greaterZero lockConflicts
      if separatorNeeded then ops.writeBuffer io ", " else pure ()
      let percentage ← ops.compilePercent compileTime elapsed
      let formatted ← ops.elapsed.writeFixed percentage 2
      ops.writeBuffer io (formatted ++ "% compilation time")
    else
      pure ()
    let recompilePositive ← ops.recompileTime.greaterZero recompileTime
    if recompilePositive then do
      let percentage ← ops.recompilePercent recompileTime compileTime
      let percentageString ← if ← ops.elapsed.lessThanOne percentage then
          pure "<1"
        else
          ops.elapsed.writeFixed percentage 0
      ops.writeBuffer io (": " ++ percentageString ++ "% of which was recompilation")
    else
      pure ()
    if parens then ops.writeBuffer io ")" else pure ()
    if newline then ops.writeBuffer io "\n" else pure ())
  let io ← ops.stdout
  ops.writeIO io rendered
  pure ()

/--
Julia source: base/timing.jl:307-324 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function timev_print(elapsedtime, diff::GC_Diff, lock_conflicts, compile_times; msg::Union{String,Nothing}=nothing)
    allocs = gc_alloc_count(diff)
    compile_time = first(compile_times)
    recompile_time = last(compile_times)
    time_print(stdout, elapsedtime, diff.allocd, diff.total_time, allocs, lock_conflicts, compile_time, recompile_time, true; msg)
    padded_nonzero_print(elapsedtime,       "elapsed time (ns)")
    padded_nonzero_print(diff.total_time,   "gc time (ns)")
    padded_nonzero_print(diff.allocd,       "bytes allocated")
    padded_nonzero_print(diff.poolalloc,    "pool allocs")
    padded_nonzero_print(diff.bigalloc,     "non-pool GC allocs")
    padded_nonzero_print(diff.malloc,       "malloc() calls", false)
    padded_nonzero_print(diff.realloc,      "realloc() calls", false)
    # always print number of frees if there are mallocs
    padded_nonzero_print(diff.freecall,     "free() calls", diff.malloc > 0)
    minor_collects = diff.pause - diff.full_sweep
    padded_nonzero_print(minor_collects,    "minor collections")
    padded_nonzero_print(diff.full_sweep,   "full collections")
end
```
-/
def timeVPrint
    {E Task W IO Buffer Elapsed Locks CompileTime RecompileTime Float : Type}
    (ops : TimeVPrintOps E Task W IO Buffer Elapsed Locks CompileTime RecompileTime Float)
    (elapsed : Elapsed) (diff : GC_Diff) (lockConflicts : Locks)
    (compileTimes : CompileTime × RecompileTime) (msg : Option String := none) : M E Task W Unit := do
  let allocations := gcAllocCount diff
  timePrint ops.time elapsed diff.allocd diff.totalTime allocations lockConflicts
    compileTimes.1 compileTimes.2 true msg
  paddedNonzeroPrint ops.elapsed elapsed "elapsed time (ns)"
  paddedNonzeroPrint ops.gcTime diff.totalTime "gc time (ns)"
  paddedNonzeroPrint ops.bytes diff.allocd "bytes allocated"
  paddedNonzeroPrint ops.allocations diff.poolalloc "pool allocs"
  paddedNonzeroPrint ops.allocations diff.bigalloc "non-pool GC allocs"
  paddedNonzeroPrint ops.allocations diff.malloc "malloc() calls" false
  paddedNonzeroPrint ops.allocations diff.realloc "realloc() calls" false
  let alwaysPrintFree := decide (0 < diff.malloc.val)
  paddedNonzeroPrint ops.allocations diff.freecall "free() calls" alwaysPrintFree
  let minorCollects := diff.pause - diff.fullSweep
  paddedNonzeroPrint ops.allocations minorCollects "minor collections"
  paddedNonzeroPrint ops.allocations diff.fullSweep "full collections"

/--
Julia source: base/timing.jl:79-79 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
gc_num() = ccall(:jl_gc_num, GC_Num, ())
```
-/
def gcNum {E Task W Pointer PageArray : Type}
    (ops : TimingC E Task W Pointer PageArray) : M E Task W GC_Num :=
  ops.gcNum

/--
Julia source: base/timing.jl:132-133 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# total time spent in garbage collection, in nanoseconds
gc_time_ns() = ccall(:jl_gc_total_hrtime, UInt64, ())
```
-/
def gcTimeNs {E Task W Pointer PageArray : Type}
    (ops : TimingC E Task W Pointer PageArray) : M E Task W U64 :=
  ops.gcTotalHrtime

/--
Julia source: base/timing.jl:148-149 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# must be kept in sync with the value from `src/julia_threads.h``
const JL_GC_N_MAX_POOLS = 51
```
-/
def gcNMaxPools : I64 := int 51

/--
Julia source: base/timing.jl:189-197 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Base.jit_total_bytes()

Return the total amount (in bytes) allocated by the just-in-time compiler
for e.g. native code and data.
"""
function jit_total_bytes()
    return ccall(:jl_jit_total_bytes, Csize_t, ())
end
```
-/
def jitTotalBytes {E Task W Pointer PageArray : Type}
    (ops : TimingC E Task W Pointer PageArray) : M E Task W U64 :=
  ops.jitTotalBytes

/--
Julia source: base/timing.jl:510-511 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# total number of bytes allocated so far
gc_bytes(b::Ref{Int64}) = ccall(:jl_gc_get_total_bytes, Cvoid, (Ptr{Int64},), b)
```
-/
def gcBytesRef {E Task W Ref : Type} (ops : RefOps E Task W Ref) (reference : Ref) : M E Task W Unit :=
  ops.gcBytesRef reference

/--
Julia source: base/timing.jl:512-517 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# NOTE: gc_bytes() is deprecated
function gc_bytes()
    b = Ref{Int64}()
    gc_bytes(b)
    b[]
end
```
-/
def gcBytes {E Task W Ref : Type} (ops : RefOps E Task W Ref) : M E Task W I64 := do
  let reference ← ops.newUninitialized
  gcBytesRef ops reference
  ops.read reference

/--
Julia source: base/timing.jl:519-526 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@constprop :none function allocated(f, args::Vararg{Any,N}) where {N}
    b0 = Ref{Int64}(0)
    b1 = Ref{Int64}(0)
    Base.gc_bytes(b0)
    @noinline f(args...)
    Base.gc_bytes(b1)
    return b1[] - b0[]
end
```
-/
def allocated
    {E Task W F Args Result Ref : Type}
    (refs : RefOps E Task W Ref) (call : FunctionCallOps E Task W F Args Result)
    (f : F) (args : Args) : M E Task W I64 := do
  let before ← refs.newRef (int 0)
  let after ← refs.newRef (int 0)
  gcBytesRef refs before
  let _ ← call.call f args
  gcBytesRef refs after
  let newValue ← refs.read after
  let oldValue ← refs.read before
  pure (newValue - oldValue)

/--
Julia source: base/timing.jl:529-534 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@constprop :none function allocations(f, args::Vararg{Any,N}) where {N}
    stats = Base.gc_num()
    @noinline f(args...)
    diff = Base.GC_Diff(Base.gc_num(), stats)
    return Base.gc_alloc_count(diff)
end
```
-/
def allocations
    {E Task W F Args Result Pointer PageArray : Type}
    (cOps : TimingC E Task W Pointer PageArray)
    (call : FunctionCallOps E Task W F Args Result)
    (f : F) (args : Args) : M E Task W I64 := do
  let before ← cOps.gcNum
  let _ ← call.call f args
  let after ← cOps.gcNum
  pure (gcAllocCount (gcDiff after before))


-- Reason: Macro hygiene and syntax generation have no typed runtime method equivalent.
-- UNTRANSLATED
-- Source: base/timing.jl:326-334 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # Like a try-finally block, except without introducing the try scope
-- # NOTE: This is deprecated and should not be used from user logic. A proper solution to
-- # this problem will be introduced in https://github.com/JuliaLang/julia/pull/39217
-- macro __tryfinally(ex, fin)
--     Expr(:tryfinally,
--        :($(esc(ex))),
--        :($(esc(fin)))
--        )
-- end
-- /Source

-- Reason: The `@time` macro rewrites user syntax and emits compiler instrumentation.
-- UNTRANSLATED
-- Source: base/timing.jl:395-399 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro time(ex)
--     quote
--         @time nothing $(esc(ex))
--     end
-- end
-- /Source

-- Reason: The message-taking `@time` macro rewrites user syntax and emits compiler instrumentation.
-- UNTRANSLATED
-- Source: base/timing.jl:400-408 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro time(msg, ex)
--     quote
--         local ret = @timed $(esc(ex))
--         local _msg = $(esc(msg))
--         local _msg_str = _msg === nothing ? _msg : string(_msg)
--         time_print(stdout, ret.time*1e9, ret.gcstats.allocd, ret.gcstats.total_time, gc_alloc_count(ret.gcstats), ret.lock_conflicts, ret.compile_time*1e9, ret.recompile_time*1e9, true; msg=_msg_str)
--         ret.value
--     end
-- end
-- /Source

-- Reason: `@showtime` constructs an expression that prints the escaped source expression.
-- UNTRANSLATED
-- Source: base/timing.jl:425-429 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro showtime(ex)
--     quote
--         @time $(sprint(show_unquoted,ex)) $(esc(ex))
--     end
-- end
-- /Source

-- Reason: `@timev` rewrites user syntax and emits compiler instrumentation.
-- UNTRANSLATED
-- Source: base/timing.jl:468-472 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro timev(ex)
--     quote
--         @timev nothing $(esc(ex))
--     end
-- end
-- /Source

-- Reason: The message-taking `@timev` macro rewrites user syntax and emits compiler instrumentation.
-- UNTRANSLATED
-- Source: base/timing.jl:473-481 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro timev(msg, ex)
--     quote
--         local ret = @timed $(esc(ex))
--         local _msg = $(esc(msg))
--         local _msg_str = _msg === nothing ? _msg : string(_msg)
--         timev_print(ret.time*1e9, ret.gcstats, ret.lock_conflicts, (ret.compile_time*1e9, ret.recompile_time*1e9); msg=_msg_str)
--         ret.value
--     end
-- end
-- /Source

-- Reason: `@elapsed` rewrites user syntax and emits compiler instrumentation.
-- UNTRANSLATED
-- Source: base/timing.jl:501-508 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro elapsed(ex)
--     quote
--         Experimental.@force_compile
--         local t0 = time_ns()
--         $(esc(ex))
--         (time_ns() -% t0) / 1e9
--     end
-- end
-- /Source

/--
Julia source: base/timing.jl:527-527 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
only(methods(allocated)).called = 0xff
```
-/
def allocatedMethodCalled : JInt .u8 := JInt.lit .u8 255

/--
Julia source: base/timing.jl:535-535 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
only(methods(allocations)).called = 0xff
```
-/
def allocationsMethodCalled : JInt .u8 := JInt.lit .u8 255

/--
Julia source: base/timing.jl:537-554 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function is_simply_call(@nospecialize ex)
    is_simple_atom(a) = a isa QuoteNode || a isa Symbol || !isa_ast_node(a)
    Meta.isexpr(ex, :call) || return false
    for a in ex.args
        is_simple_atom(a) && continue
        Meta.isexpr(a, :..., 1) && is_simple_atom(a.args[1]) && continue
        return false
    end
    # Ensure Expr(:call, .+, ...) get wrapped
    if ex.args[1] isa Symbol
        sa = String(ex.args[1]::Symbol)
        startswith(sa, ".") &&
            !endswith(sa, ".") &&
            isoperator(Symbol(sa[2:end])) &&
            return false
    end
    return true
end
```
-/
def isSimplyCall {L : Type} (isOperator : Sym → Bool) (expression : Value L) : ExprResult Bool := do
  if !isexpr expression "call" then
    return false
  let arguments ← match expression with
    | .expr _ arguments => pure arguments
    | _ => return false
  for argument in arguments do
    if simpleCallAtom argument then
      pure ()
    else if isexpr_n argument "..." (i64 1) then
      let splatArgument ← match argument with
        | .expr _ arguments => argAt arguments 1
        | _ => throw (.jl .boundsError)
      if !simpleCallAtom splatArgument then
        return false
    else
      return false
  let firstArgument ← argAt arguments 1
  match firstArgument with
  | .symbol name =>
    let characters := name.toList
    if characters.head? == some '.' && characters.reverse.head? != some '.' &&
        isOperator (String.ofList (characters.drop 1)) then
      return false
  | _ => pure ()
  return true

/--
Julia source: base/timing.jl:556-592 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _gen_allocation_measurer(ex, fname::Symbol)
    if isexpr(ex, :call)
        if !is_simply_call(ex)
            ex = :((() -> $ex)())
        end
        pushfirst!(ex.args, GlobalRef(Base, fname))
        return quote
            Experimental.@force_compile
            $(esc(ex))
        end
    elseif fname === :allocated
        # v1.11-compatible implementation
        return quote
            Experimental.@force_compile
            local b0 = Ref{Int64}(0)
            local b1 = Ref{Int64}(0)
            gc_bytes(b0)
            $(esc(ex))
            gc_bytes(b1)
            b1[] - b0[]
        end
    else
        @assert fname === :allocations "unexpected fname"
        return quote
            Experimental.@force_compile
            # Note this value is unused, but without it `allocated` and `allocations`
            # are sufficiently different that the compiler can remove allocations here
            # that it cannot remove there, giving inconsistent numbers.
            local b1 = Ref{Int64}(0)
            local stats = Base.gc_num()
            $(esc(ex))
            local diff = Base.GC_Diff(Base.gc_num(), stats)
            gc_bytes(b1)
            Base.gc_alloc_count(diff)
        end
    end
end
```
-/
def genAllocationMeasurer {L : Type} (ops : AllocationSyntaxOps L)
    (expression : Value L) (functionName : Sym) :
    Except AllocationError (Value L) := do
  if isexpr expression "call" then
    let isSimple ← (isSimplyCall ops.isOperator expression).mapError .expression
    let callExpression := if isSimple then expression else
      .expr "call" [.expr "->" [.expr "tuple" [], expression]]
    let callExpression := match callExpression with
      | .expr "call" arguments =>
        .expr "call" (.globalRef ops.leaves.base functionName :: arguments)
      | other => other
    pure (timingBlock [
      (563, timingForceCompile 563),
      (564, .expr "escape" [callExpression])])
  else if functionName == "allocated" then
    pure (allocatedQuote ops expression)
  else if functionName == "allocations" then
    pure (allocationsQuote ops expression)
  else
    throw (.assertionError "unexpected fname")

-- Reason: `@allocated` rewrites Julia syntax and inserts compiler allocation instrumentation.
-- UNTRANSLATED
-- Source: base/timing.jl:622-624 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro allocated(ex)
--     _gen_allocation_measurer(ex, :allocated)
-- end
-- /Source

-- Reason: `@allocations` rewrites Julia syntax and inserts compiler allocation instrumentation.
-- UNTRANSLATED
-- Source: base/timing.jl:643-645 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro allocations(ex)
--     _gen_allocation_measurer(ex, :allocations)
-- end
-- /Source

-- Reason: `@lock_conflicts` emits compiler instrumentation for lock-wait counts.
-- UNTRANSLATED
-- Source: base/timing.jl:672-683 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro lock_conflicts(ex)
--     quote
--         Threads.lock_profiling(true)
--         local lock_conflicts = Threads.LOCK_CONFLICT_COUNT[]
--         try
--             $(esc(ex))
--         finally
--             Threads.lock_profiling(false)
--         end
--         Threads.LOCK_CONFLICT_COUNT[] - lock_conflicts
--     end
-- end
-- /Source

-- Reason: `@timed` rewrites Julia syntax and emits compiler instrumentation.
-- UNTRANSLATED
-- Source: base/timing.jl:732-760 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro timed(ex)
--     quote
--         Experimental.@force_compile
--         Threads.lock_profiling(true)
--         local lock_conflicts = Threads.LOCK_CONFLICT_COUNT[]
--         local stats = gc_num()
--         local elapsedtime = time_ns()
--         cumulative_compile_timing(true)
--         local compile_elapsedtimes = cumulative_compile_time_ns()
--         local val = @__tryfinally($(esc(ex)),
--             (elapsedtime = time_ns() -% elapsedtime;
--             cumulative_compile_timing(false);
--             compile_elapsedtimes = map(-%, cumulative_compile_time_ns(), compile_elapsedtimes);
--             lock_conflicts = Threads.LOCK_CONFLICT_COUNT[] - lock_conflicts;
--             Threads.lock_profiling(false))
--         )
--         local diff = GC_Diff(gc_num(), stats)
--         (
--             value=val,
--             time=elapsedtime/1e9,
--             bytes=diff.allocd,
--             gctime=diff.total_time/1e9,
--             gcstats=diff,
--             lock_conflicts=lock_conflicts,
--             compile_time=compile_elapsedtimes[1]/1e9,
--             recompile_time=compile_elapsedtimes[2]/1e9
--         )
--     end
-- end
-- /Source

-- Reason: `@time_imports` rewrites module imports and measures their load-time effects.
-- UNTRANSLATED
-- Source: base/timing.jl:764-774 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro time_imports(ex)
--     quote
--         Base.Threads.atomic_add!(Base.TIMING_IMPORTS, 1)
--         @__tryfinally(
--             # try
--             $(esc(ex)),
--             # finally
--             Base.Threads.atomic_sub!(Base.TIMING_IMPORTS, 1)
--         )
--     end
-- end
-- /Source

-- Reason: `@trace_compile` emits compiler trace hooks during macro expansion.
-- UNTRANSLATED
-- Source: base/timing.jl:776-786 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro trace_compile(ex)
--     quote
--         ccall(:jl_force_trace_compile_timing_enable, Cvoid, ())
--         @__tryfinally(
--             # try
--             $(esc(ex)),
--             # finally
--             ccall(:jl_force_trace_compile_timing_disable, Cvoid, ())
--         )
--     end
-- end
-- /Source

-- Reason: `@trace_dispatch` emits compiler dispatch trace hooks during macro expansion.
-- UNTRANSLATED
-- Source: base/timing.jl:788-798 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro trace_dispatch(ex)
--     quote
--         ccall(:jl_force_trace_dispatch_enable, Cvoid, ())
--         @__tryfinally(
--             # try
--             $(esc(ex)),
--             # finally
--             ccall(:jl_force_trace_dispatch_disable, Cvoid, ())
--         )
--     end
-- end
-- /Source

end JuliaLean.base.timing

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

namespace JuliaLean.ConcurrencyCov.FaithfulTiming

open JuliaLean JuliaLean.ConcurrencyCov

def gcNumM := Timing.gcNumQ
def gcTotalBytesM := Timing.gcTotalBytes
def gcDiffM := Timing.gcDiff
def gcAllocCountM := Timing.gcAllocCount
def cumulativeCompileTimeNsM := Timing.cumulativeCompileTimeNs
def cumulativeCompileTimingM := Timing.cumulativeCompileTiming
def gcTimeNsM := Timing.gcTimeNs
def gcLiveBytesM := Timing.gcLiveBytes
def gcPageUtilizationDataM := Timing.gcPageUtilizationData
def fullSweepReasonsM := Timing.fullSweepReasons
def jitTotalBytesM := Timing.jitTotalBytes
def prettyprintGetunitsM := Timing.prettyprintGetunits
def paddedNonzeroPrintM (v : Timing.PVal) (s : String) (always : Bool) :=
  Timing.paddedNonzeroPrint v s always
def formatBytesM (bytes : I64) (binary : Bool) := Timing.formatBytes bytes binary
def timePrintM := Timing.timePrint
def timevPrintM (elapsed : JuliaLean.Float.F64) (diff : Timing.GcDiff) (conflicts : I64)
    (compile : JuliaLean.Float.F64 × JuliaLean.Float.F64) (msg : Option String) :=
  Timing.timevPrint elapsed diff conflicts compile msg
def tryfinallyM {σ : Type} (ex : σ → Outcome × σ) (fin : σ → σ) (s : σ) :=
  Timing.tryfinally ex fin s
def timeNoMsgM := Timing.time none
def timeMsgM (msg : String) := Timing.time (some msg)
def showtimeM := Timing.showtime
def timevNoMsgM := Timing.timev none
def timevMsgM (msg : String) := Timing.timev (some msg)
def elapsedM := Timing.elapsed
def gcBytesRefM := Timing.gcBytes
def gcBytesM := Timing.gcBytes
def allocatedM := Timing.allocated
def allocationsM := Timing.allocations
def isSimplyCallM := Timing.isSimplyCall
def isSimpleAtomM := Timing.isSimpleAtom
def genAllocationMeasurerM := Timing.genAllocationMeasurer
def allocatedMacroM := Timing.allocatedMacro
def allocationsMacroM := Timing.allocationsMacro
def lockConflictsM := Timing.lockConflictsMacro
def timedM := Timing.timed
def timeImportsM := Timing.bracket Timing.Bracket.timeImports
def traceCompileM := Timing.bracket Timing.Bracket.traceCompile
def traceDispatchM := Timing.bracket Timing.Bracket.traceDispatch

end JuliaLean.ConcurrencyCov.FaithfulTiming
