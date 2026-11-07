import JuliaLean.base.runtime_internals
import JuliaLean.Core

/-!
# Model of `base/options.jl`

Typed model of `Base.JLOptions` and its helpers at Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`
on a 64-bit platform. Each modelled method is a Lean definition whose docstring carries the
method's verbatim source; its body follows the Julia body call by call.

* Integer fields are `JInt` of their declared width. `Ptr{UInt8}` fields have type `P` and
  `Ptr{Ptr{UInt8}}` fields type `PP`, with `C_NULL` tests and loads through `PtrOps`.
* The runtime (`jl_options`, `jl_is_file_tracked`, `ENV`) and the printers of later files
  (`print`, `repr`) are interface parameters.
-/

namespace JuliaLean.base.options
open JuliaLean

abbrev Bytes := List UInt8
def lit (s : String) : Bytes := s.toUTF8.toList

-- UNTRANSLATED
-- license header: no method
-- Source: base/options.jl:1-2 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- /Source

/--
Julia source: base/options.jl:3-78 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# NOTE: This type needs to be kept in sync with jl_options in src/jloptions.h
struct JLOptions
    quiet::Int8
    banner::Int8
    julia_bindir::Ptr{UInt8}
    julia_bin::Ptr{UInt8}
    commands::Ptr{Ptr{UInt8}} # (e)eval, (E)print, (L)load
    image_file::Ptr{UInt8}
    cpu_target::Ptr{UInt8}
    nthreadpools::Int8
    nthreads::Int16
    nmarkthreads::Int16
    nsweepthreads::Int8
    nthreads_per_pool::Ptr{Int16}
    nprocs::Int32
    machine_file::Ptr{UInt8}
    project::Ptr{UInt8}
    program_file::Ptr{UInt8}
    isinteractive::Int8
    color::Int8
    historyfile::Int8
    startupfile::Int8
    compile_enabled::Int8
    code_coverage::Int8
    code_coverage_mode::Int8
    malloc_log::Int8
    tracked_path::Ptr{UInt8}
    opt_level::Int8
    opt_level_min::Int8
    debug_level::Int8
    check_bounds::Int8
    depwarn::Int8
    warn_overwrite::Int8
    can_inline::Int8
    polly::Int8
    trace_compile::Ptr{UInt8}
    trace_dispatch::Ptr{UInt8}
    fast_math::Int8
    worker::Int8
    cookie::Ptr{UInt8}
    handle_signals::Int8
    use_experimental_features::Int8
    use_sysimage_native_code::Int8
    use_compiled_modules::Int8
    use_pkgimages::Int8
    bindto::Ptr{UInt8}
    outputbc::Ptr{UInt8}
    outputunoptbc::Ptr{UInt8}
    outputo::Ptr{UInt8}
    outputasm::Ptr{UInt8}
    outputji::Ptr{UInt8}
    output_code_coverage::Ptr{UInt8}
    incremental::Int8
    image_file_specified::Int8
    warn_scope::Int8
    image_codegen::Int8
    rr_detach::Int8
    strip_metadata::Int8
    strip_ir::Int8
    permalloc_pkgimg::Int8
    heap_size_hint::UInt64
    hard_heap_limit::UInt64
    heap_target_increment::UInt64
    trace_compile_timing::Int8
    trim::Int8
    trace_eval::Int8
    task_metrics::Int8
    timeout_for_safepoint_straggler_s::Int16
    gc_sweep_always_full::Int8
    compress_sysimage::Int8
    alert_on_critical_error::Int8
    target_sanitize_memory::Int8
    target_sanitize_thread::Int8
    target_sanitize_address::Int8
end

```
-/
structure JLOptions (P PP : Type) where
  quiet : JInt .i8
  banner : JInt .i8
  julia_bindir : P
  julia_bin : P
  commands : PP
  image_file : P
  cpu_target : P
  nthreadpools : JInt .i8
  nthreads : JInt .i16
  nmarkthreads : JInt .i16
  nsweepthreads : JInt .i8
  /-- `nthreads_per_pool::Ptr{Int16}`, represented by its address. -/
  nthreads_per_pool : JInt .u64
  nprocs : JInt .i32
  machine_file : P
  project : P
  program_file : P
  isinteractive : JInt .i8
  color : JInt .i8
  historyfile : JInt .i8
  startupfile : JInt .i8
  compile_enabled : JInt .i8
  code_coverage : JInt .i8
  code_coverage_mode : JInt .i8
  malloc_log : JInt .i8
  tracked_path : P
  opt_level : JInt .i8
  opt_level_min : JInt .i8
  debug_level : JInt .i8
  check_bounds : JInt .i8
  depwarn : JInt .i8
  warn_overwrite : JInt .i8
  can_inline : JInt .i8
  polly : JInt .i8
  trace_compile : P
  trace_dispatch : P
  fast_math : JInt .i8
  worker : JInt .i8
  cookie : P
  handle_signals : JInt .i8
  use_experimental_features : JInt .i8
  use_sysimage_native_code : JInt .i8
  use_compiled_modules : JInt .i8
  use_pkgimages : JInt .i8
  bindto : P
  outputbc : P
  outputunoptbc : P
  outputo : P
  outputasm : P
  outputji : P
  output_code_coverage : P
  incremental : JInt .i8
  image_file_specified : JInt .i8
  warn_scope : JInt .i8
  image_codegen : JInt .i8
  rr_detach : JInt .i8
  strip_metadata : JInt .i8
  strip_ir : JInt .i8
  permalloc_pkgimg : JInt .i8
  heap_size_hint : JInt .u64
  hard_heap_limit : JInt .u64
  heap_target_increment : JInt .u64
  trace_compile_timing : JInt .i8
  trim : JInt .i8
  trace_eval : JInt .i8
  task_metrics : JInt .i8
  timeout_for_safepoint_straggler_s : JInt .i16
  gc_sweep_always_full : JInt .i8
  compress_sysimage : JInt .i8
  alert_on_critical_error : JInt .i8
  target_sanitize_memory : JInt .i8
  target_sanitize_thread : JInt .i8
  target_sanitize_address : JInt .i8

/-- A field value of a `JLOptions`, by its declared type. -/
inductive FieldValue (P PP : Type) where
  | int (t : IntTy) (v : JInt t)
  | ptrUInt8 (p : P)
  | ptrPtrUInt8 (p : PP)
  /-- The `Ptr{Int16}` field. -/
  | ptrInt16 (address : JInt .u64)

/-- `fieldnames(JLOptions)` paired with `getfield(opt, i)`, in declaration order. -/
def fields {P PP : Type} (o : JLOptions P PP) : List (String × FieldValue P PP) :=
  let i8 (v : JInt .i8) : FieldValue P PP := .int .i8 v
  [("quiet", i8 o.quiet), ("banner", i8 o.banner), ("julia_bindir", .ptrUInt8 o.julia_bindir),
   ("julia_bin", .ptrUInt8 o.julia_bin), ("commands", .ptrPtrUInt8 o.commands),
   ("image_file", .ptrUInt8 o.image_file), ("cpu_target", .ptrUInt8 o.cpu_target),
   ("nthreadpools", i8 o.nthreadpools), ("nthreads", .int .i16 o.nthreads),
   ("nmarkthreads", .int .i16 o.nmarkthreads), ("nsweepthreads", i8 o.nsweepthreads),
   ("nthreads_per_pool", .ptrInt16 o.nthreads_per_pool), ("nprocs", .int .i32 o.nprocs),
   ("machine_file", .ptrUInt8 o.machine_file), ("project", .ptrUInt8 o.project),
   ("program_file", .ptrUInt8 o.program_file), ("isinteractive", i8 o.isinteractive),
   ("color", i8 o.color), ("historyfile", i8 o.historyfile), ("startupfile", i8 o.startupfile),
   ("compile_enabled", i8 o.compile_enabled), ("code_coverage", i8 o.code_coverage),
   ("code_coverage_mode", i8 o.code_coverage_mode), ("malloc_log", i8 o.malloc_log),
   ("tracked_path", .ptrUInt8 o.tracked_path), ("opt_level", i8 o.opt_level),
   ("opt_level_min", i8 o.opt_level_min), ("debug_level", i8 o.debug_level),
   ("check_bounds", i8 o.check_bounds), ("depwarn", i8 o.depwarn),
   ("warn_overwrite", i8 o.warn_overwrite), ("can_inline", i8 o.can_inline), ("polly", i8 o.polly),
   ("trace_compile", .ptrUInt8 o.trace_compile), ("trace_dispatch", .ptrUInt8 o.trace_dispatch),
   ("fast_math", i8 o.fast_math), ("worker", i8 o.worker), ("cookie", .ptrUInt8 o.cookie),
   ("handle_signals", i8 o.handle_signals), ("use_experimental_features", i8 o.use_experimental_features),
   ("use_sysimage_native_code", i8 o.use_sysimage_native_code),
   ("use_compiled_modules", i8 o.use_compiled_modules), ("use_pkgimages", i8 o.use_pkgimages),
   ("bindto", .ptrUInt8 o.bindto), ("outputbc", .ptrUInt8 o.outputbc),
   ("outputunoptbc", .ptrUInt8 o.outputunoptbc), ("outputo", .ptrUInt8 o.outputo),
   ("outputasm", .ptrUInt8 o.outputasm), ("outputji", .ptrUInt8 o.outputji),
   ("output_code_coverage", .ptrUInt8 o.output_code_coverage), ("incremental", i8 o.incremental),
   ("image_file_specified", i8 o.image_file_specified), ("warn_scope", i8 o.warn_scope),
   ("image_codegen", i8 o.image_codegen), ("rr_detach", i8 o.rr_detach),
   ("strip_metadata", i8 o.strip_metadata), ("strip_ir", i8 o.strip_ir),
   ("permalloc_pkgimg", i8 o.permalloc_pkgimg), ("heap_size_hint", .int .u64 o.heap_size_hint),
   ("hard_heap_limit", .int .u64 o.hard_heap_limit),
   ("heap_target_increment", .int .u64 o.heap_target_increment),
   ("trace_compile_timing", i8 o.trace_compile_timing), ("trim", i8 o.trim),
   ("trace_eval", i8 o.trace_eval), ("task_metrics", i8 o.task_metrics),
   ("timeout_for_safepoint_straggler_s", .int .i16 o.timeout_for_safepoint_straggler_s),
   ("gc_sweep_always_full", i8 o.gc_sweep_always_full), ("compress_sysimage", i8 o.compress_sysimage),
   ("alert_on_critical_error", i8 o.alert_on_critical_error),
   ("target_sanitize_memory", i8 o.target_sanitize_memory),
   ("target_sanitize_thread", i8 o.target_sanitize_thread),
   ("target_sanitize_address", i8 o.target_sanitize_address)]

-- UNTRANSLATED
-- load-time check of the structure size against `jl_sizeof_jl_options`: not a method
-- Source: base/options.jl:79-84 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This runs early in the sysimage when `!=` is not defined yet
-- if sizeof(JLOptions) === ccall(:jl_sizeof_jl_options, Int, ())
-- else
--     ccall(:jl_throw, Cvoid, (Any,), "Option structure mismatch")
-- end
-- 
-- /Source

/-- Pointer primitives: `p == C_NULL`, `unsafe_load(v, i)` of a `Ptr{Ptr{UInt8}}`, `unsafe_load(s)`
of a `Ptr{UInt8}`, `s + 1`, and `unsafe_string(p)`. -/
structure PtrOps (m : Type → Type) (P PP : Type) where
  isNullP : P → Bool
  isNullPP : PP → Bool
  loadPP : PP → JInt .i64 → m P
  loadByte : P → m UInt8
  succ : P → P
  unsafe_string : P → m Bytes

section
variable {m : Type → Type} [Monad m] {P PP : Type}

/--
Julia source: base/options.jl:85-86 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
JLOptions() = unsafe_load(cglobal(:jl_options, JLOptions))

```
-/
def JLOptions_new (load_jl_options : m (JLOptions P PP)) : m (JLOptions P PP) := load_jl_options

/--
Julia source: base/options.jl:87-92 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# NOTE: Keep in sync with the JL_OPTIONS_COMPILE_* defines in src/julia.h
const JL_OPTIONS_COMPILE_OFF = 0
const JL_OPTIONS_COMPILE_ON  = 1
const JL_OPTIONS_COMPILE_ALL = 2
const JL_OPTIONS_COMPILE_MIN = 3

```
-/
def JL_OPTIONS_COMPILE_OFF : JInt .i64 := JInt.wrap .i64 0
def JL_OPTIONS_COMPILE_ON : JInt .i64 := JInt.wrap .i64 1
def JL_OPTIONS_COMPILE_ALL : JInt .i64 := JInt.wrap .i64 2
def JL_OPTIONS_COMPILE_MIN : JInt .i64 := JInt.wrap .i64 3

/--
Julia source: base/options.jl:93-104 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function colored_text(opts::JLOptions)
    return if opts.color != 0
        opts.color == 1
    elseif !isempty(get(ENV, "FORCE_COLOR", ""))
        true
    elseif !isempty(get(ENV, "NO_COLOR", ""))
        false
    else
        nothing
    end
end

```
-/
/- `colored_text(opts)`; `getENV k` is `get(ENV, k, "")`. `none` is `nothing`. -/
def colored_text (getENV : Bytes → m Bytes) (opts : JLOptions P PP) : m (Option Bool) := do
  if opts.color.val != 0 then
    return some (opts.color.val == 1)
  else if !(← getENV (lit "FORCE_COLOR")).isEmpty then
    return some true
  else if !(← getENV (lit "NO_COLOR")).isEmpty then
    return some false
  else
    return none

/--
Julia source: base/options.jl:121-134 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_load_commands(v::Ptr{Ptr{UInt8}})
    cmds = Pair{Char, String}[]
    v == C_NULL && return cmds
    i = 1
    while true
        s = unsafe_load(v, i)
        s == C_NULL && break
        e = Char(unsafe_load(s))
        push!(cmds, e => unsafe_string(s + 1))
        i += 1
    end
    return cmds
end

```
-/
/- The `while true` loop of `unsafe_load_commands`. -/
def unsafe_load_commands_loop [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : PtrOps m P PP)
    (v : PP) (i : JInt .i64) (cmds : List (Char × Bytes)) : m (List (Char × Bytes)) := do
  let s ← o.loadPP v i
  if o.isNullP s then return cmds
  -- `Char(::UInt8)` is the character with that code point
  let e := Char.ofNat (← o.loadByte s).toNat
  let cmds := cmds ++ [(e, ← o.unsafe_string (o.succ s))]
  unsafe_load_commands_loop o v (JInt.wrap .i64 (i.val + 1)) cmds
partial_fixpoint

/-- `unsafe_load_commands(v)`. -/
def unsafe_load_commands [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : PtrOps m P PP)
    (v : PP) : m (List (Char × Bytes)) := do
  if o.isNullPP v then return []
  unsafe_load_commands_loop o v (JInt.wrap .i64 1) []

/--
Julia source: base/options.jl:105-120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, opt::JLOptions)
    print(io, "JLOptions(")
    fields = fieldnames(JLOptions)
    nfields = length(fields)
    for (i, f) in enumerate(fields)
        v = getfield(opt, i)
        if isa(v, Ptr{UInt8})
            v = (v != C_NULL) ? unsafe_string(v) : ""
        elseif isa(v, Ptr{Ptr{UInt8}})
            v = unsafe_load_commands(v)
        end
        print(io, f, " = ", repr(v), i < nfields ? ", " : "")
    end
    print(io, ")")
end

```
-/
/- A value printed by `repr` in `show(io, ::JLOptions)`. -/
inductive ReprArg where
  | int (t : IntTy) (v : JInt t)
  | string (s : Bytes)
  | ptrInt16 (address : JInt .u64)
  | commands (cmds : List (Char × Bytes))

/-- `show(io, opt::JLOptions)`; `print io s` prints bytes and `repr` is Julia's `repr` of the
value's type. -/
def show_JLOptions [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] {Io : Type} (o : PtrOps m P PP)
    (print : Io → Bytes → m Unit) (repr : ReprArg → m Bytes) (io : Io) (opt : JLOptions P PP) : m Unit := do
  print io (lit "JLOptions(")
  let fs := fields opt
  let nfields := fs.length
  for ((f, v), idx) in fs.zipIdx do
    let i := idx + 1
    let v : ReprArg ← match v with
      | .ptrUInt8 p => if !o.isNullP p then ReprArg.string <$> o.unsafe_string p else pure (.string [])
      | .ptrPtrUInt8 p => ReprArg.commands <$> unsafe_load_commands o p
      | .int t x => pure (.int t x)
      | .ptrInt16 a => pure (.ptrInt16 a)
    print io (lit f ++ lit " = " ++ (← repr v) ++ (if i < nfields then lit ", " else []))
  print io (lit ")")

/--
Julia source: base/options.jl:135-137 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function is_file_tracked(file::Symbol)
    return ccall(:jl_is_file_tracked, Cint, (Any,), file) == 1
end
```
-/
def is_file_tracked (jl_is_file_tracked : String → m (JInt .i32)) (file : String) : m Bool := do
  return (← jl_is_file_tracked file).val == 1

end

end JuliaLean.base.options

section
namespace JuliaLean.RuntimeCov.Options

open JuliaLean.RuntimeCov

/-- `JLOptions()`, base/options.jl:85: one `unsafe_load` of the runtime's
`jl_options` global, modelled as returning the runtime record unchanged. -/
def jlOptions {α : Type} (runtimeRecord : α) : α := runtimeRecord

/-- `colored_text(opts)`, base/options.jl:93-103, with the `color` field and
the environment lookup as inputs. `none` is Julia's `nothing`. -/
def coloredText (color : Int) (env : String → Option String) : Option Bool :=
  if color != 0 then some (color == 1)
  else if !((env "FORCE_COLOR").getD "").isEmpty then some true
  else if !((env "NO_COLOR").getD "").isEmpty then some false
  else none

/-- A field value as `show(::IO, ::JLOptions)` sees it. -/
inductive FieldValue where
  /-- A `Ptr{UInt8}`: `none` is `C_NULL`. -/
  | cstr (s : Option String)
  /-- A `Ptr{Ptr{UInt8}}` command table: printed via `unsafe_load_commands`. -/
  | cmds (reprOfCommands : String)
  /-- Any other field: printed with `repr`. -/
  | other (reprText : String)

/-- The printed value of one field, base/options.jl:110-115. -/
def fieldText : FieldValue → String
  | .cstr none => "\"\""
  | .cstr (some s) => "\"" ++ s ++ "\""
  | .cmds r => r
  | .other r => r

/-- The body of the loop at base/options.jl:109-117: field `i` (1-based) prints
`name = value`, then the separator `", "` when `i < nfields` (the flag). -/
def showFields (nfields : Nat) : Nat → List (String × FieldValue) → List (String × Bool)
  | _, [] => []
  | i, (f, v) :: rest =>
    (f ++ " = " ++ fieldText v, decide (i < nfields)) :: showFields nfields (i + 1) rest

/-- `show(io, opt::JLOptions)`, base/options.jl:105-119, as the printed text. -/
def showOptions (fields : List (String × FieldValue)) : String :=
  "JLOptions(" ++ String.join ((showFields fields.length 1 fields).map
    (fun p => p.1 ++ (if p.2 then ", " else ""))) ++ ")"

/-- The command table read by `unsafe_load_commands`: successive
`Ptr{UInt8}` slots, `none` for `C_NULL`; a present slot holds its first byte as
a `Char` and the rest of the C string. -/
def loadCommandsFrom : List (Option (Char × String)) → List (Char × String)
  | [] => []
  | none :: _ => []
  | some e :: rest => e :: loadCommandsFrom rest

/-- `unsafe_load_commands(v)`, base/options.jl:121-133: `none` is a null table
pointer. -/
def unsafeLoadCommands (v : Option (List (Option (Char × String)))) : List (Char × String) :=
  match v with
  | none => []
  | some table => loadCommandsFrom table

/-- `is_file_tracked(file)`, base/options.jl:135-137. -/
def isFileTracked (runtime : Sym → Int) (file : Sym) : Bool := runtime file == 1
end JuliaLean.RuntimeCov.Options
end
