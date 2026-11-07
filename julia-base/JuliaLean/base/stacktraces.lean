import JuliaLean.base.error
import JuliaLean.Core

/-!
# Model of `base/stacktraces.jl`

Typed model of the module `Base.StackTraces` at Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`
on a 64-bit platform. Each modelled method is a Lean definition whose docstring carries the
method's verbatim source; its body follows the Julia body call by call.

* `StackFrame` is a Lean structure with the Julia fields. Its `linfo` field is the union
  `Linfo` of the abstract types `MI` (`Core.MethodInstance`), `CI` (`Core.CodeInstance`), `Meth`
  (`Method`) and `CInfo` (`Core.CodeInfo`); `DI` is `Core.DebugInfo`, `Mod` `Module`, `Ty` a Julia
  type. Pointers are `UInt64` values.
* `lookup` is modelled over typed primitives (`Reflect`): the runtime's
  `jl_lookup_code_address` (its result as raw frames `RF` with typed field reads),
  `jl_cdi_firstxy`, the compiler's `DebugInfo` traversal (`prev_debuginfo`, `edge_debuginfo`,
  `has_prev_debuginfo`, `source_location`, IRShow's `method_name`, `debuginfo_file`,
  `debuginfo_firstline`) and the fields of the runtime objects.
* Printing and the calls into files loaded after stacktraces.jl (`print` and `IOContext` of
  `base/show.jl`, `print_within_stacktrace`, `demangle_function_name`, `show_mi`,
  `show_tuple_as_call`, `method_argnames` of `base/methodshow.jl`, `basename`, `backtrace`,
  `hash`) are the fields of `Callees`, over an abstract stream type `Io`.
* Loops over the debug-info tree are `partial_fixpoint` definitions; they require the monad to
  carry a `Lean.Order.CCPO` and `Lean.Order.MonoBind` structure.
-/

namespace JuliaLean.base.stacktraces

open JuliaLean

/-- A Julia `Symbol`, by its name. -/
abbrev Sym := String

/-- Exceptions thrown by the modelled methods. -/
inductive StError where
  /-- A failed type assertion `x::T` or `convert` to a field type. -/
  | typeError
  | boundsError
  | assertionError (msg : String)
  /-- `InexactError` of a failed integer conversion. -/
  | inexactError (fn : String)
  | methodError (fn : String)
  | stringIndexError
  deriving Repr, DecidableEq

/-- The `linfo` field: `Union{Core.MethodInstance, Core.CodeInstance, Method, CodeInfo, Nothing}`. -/
inductive Linfo (MI CI Meth CInfo : Type) where
  | methodInstance (x : MI)
  | codeInstance (x : CI)
  | method (x : Meth)
  | codeInfo (x : CInfo)
  | nothing

/-- `code.def` of a `CodeInstance`: a `MethodInstance`, a `Core.ABIOverride` (by its `def`), or another value. -/
inductive CIDef (MI : Type) where
  | mi (x : MI)
  | abiOverride (inner : Option MI)
  | other

/-- `mi.def` of a `MethodInstance`: a `Method` or a `Module`. -/
inductive MIDef (Meth Mod : Type) where
  | method (x : Meth)
  | module (x : Mod)

/-- `ip.code` of a `Base.InterpreterIP`. -/
inductive IPCode (MI CI CInfo : Type) where
  | codeInfo (x : CInfo)
  | methodInstance (x : MI)
  | codeInstance (x : CI)
  | nothing

/-- `Base.InterpreterIP` (`base/error.jl`): `code` and `stmt` (`mod` is not read here). -/
structure InterpreterIP (MI CI CInfo : Type) where
  code : IPCode MI CI CInfo
  stmt : JInt .u64

/-- An element of a backtrace: `Ptr{Cvoid}` or `Base.InterpreterIP`. -/
inductive IP (MI CI CInfo : Type) where
  | ptr (p : JInt .u64)
  | interp (ip : InterpreterIP MI CI CInfo)

/-- `Base.Compiler.SourceLocation`. -/
structure SourceLocation where
  byte : JInt64
  byte_end : JInt64
  col : JInt64
  col_end : JInt64
  line : JInt64
  line_end : JInt64

/-- Runtime and compiler primitives and the fields of runtime objects. `RF` is one raw frame of
`jl_lookup_code_address` (a `SimpleVector`). -/
structure Reflect (m : Type → Type) (MI CI Meth CInfo DI Mod Ty RF : Type) where
  /-- `@ccall jl_lookup_code_address(pointer::Ptr{Cvoid}, false::Cint)::Core.SimpleVector`. -/
  lookup_code_address : JInt .u64 → m (List RF)
  /-- `length(f)`, and `f[i]` read as a `Symbol`, `Int` or `Bool` (`none` for another type). -/
  rfLength : RF → Nat
  rfSym : RF → Nat → Option Sym
  rfInt : RF → Nat → Option JInt64
  rfBool : RF → Nat → Option Bool
  /-- `f[4]` converted to the `linfo` field type (`none`: no conversion). -/
  rfLinfo : RF → Option (Linfo MI CI Meth CInfo)
  /-- `f[4]` when it is a `CodeInstance`. -/
  rfCodeInstance : RF → Option CI
  /-- `x.debuginfo` of a `CodeInstance` when it is a `Core.DebugInfo`. -/
  ciDebuginfo : CI → Option DI
  /-- `Base.Compiler.prev_debuginfo(di, pc)`: the linetable when it is a `DebugInfo`, and its pc. -/
  prev_debuginfo : DI → JInt64 → m (Option DI × JInt64)
  /-- `Base.Compiler.edge_debuginfo(di, pc)`: `nothing` or an edge and its pc. -/
  edge_debuginfo : DI → JInt64 → m (Option (DI × JInt64))
  has_prev_debuginfo : DI → JInt64 → m Bool
  source_location : DI → JInt64 → m SourceLocation
  /-- `di.def isa Symbol`, and `di.def` when it is a `MethodInstance`. -/
  diDefIsSymbol : DI → Bool
  diDefMI : DI → Option MI
  /-- `IRShow.method_name(di.def)`, `IRShow.debuginfo_file(di)`, `IRShow.debuginfo_firstline(di)[2]`. -/
  method_name : DI → m Sym
  debuginfo_file : DI → m Sym
  debuginfo_firstline : DI → m JInt64
  /-- `@ccall(jl_cdi_firstxy(di::Any, pc::Int32)::NTuple{2, Int32})[1]`. -/
  cdi_firstxy : DI → JInt .i32 → m (JInt .i32)
  /-- `mi.def`, `meth.name`, `meth.module`, `meth.sig`, `meth.nkw`, `meth.source`, `mi.specTypes`. -/
  miDef : MI → MIDef Meth Mod
  methName : Meth → Sym
  methModule : Meth → Mod
  methSig : Meth → Ty
  nkw : Meth → JInt64
  /-- `meth.source` as a `CodeInfo` (reading its `debuginfo` throws otherwise). -/
  methSource : Meth → m CInfo
  specTypes : MI → Ty
  /-- `code.inferred` when it is a `CodeInfo`, `code.def`, `code.owner !== nothing`. -/
  ciInferred : CI → Option CInfo
  ciDef : CI → CIDef MI
  /-- Printed `typeof(def)` after unwrapping a `Core.ABIOverride`. -/
  ciUnwrappedDefTypeName : CI → String
  ciHasOwner : CI → Bool
  /-- `Base.get_ci_mi(ci)`. -/
  get_ci_mi : CI → m MI
  cinfoDebuginfo : CInfo → DI
  /-- `fieldtype(T, i)`, `unwrap_unionall`, `.parameters` of a `DataType` (throws otherwise),
  `rewrap_unionall`, `Tuple{ts...}`. -/
  fieldtype : Ty → JInt64 → m Ty
  unwrap_unionall : Ty → Ty
  parameters : Ty → m (List Ty)
  rewrap_unionall : Ty → Ty → Ty
  tupleOf : List Ty → Ty
  /-- `===` on modules. -/
  egalMod : Mod → Mod → Bool

/-- `StackFrame`. -/
structure StackFrame (MI CI Meth CInfo DI : Type) where
  func : Sym
  file : Sym
  line : JInt64
  linfo : Linfo MI CI Meth CInfo
  from_c : Bool
  inlined : Bool
  pointer : JInt .u64
  pc : JInt64
  debuginfo : Option DI

/-- Calls into files loaded after stacktraces.jl, over a stream type `Io`. -/
structure Callees (m : Type → Type) (Io MI CI Meth CInfo DI Mod Ty : Type) where
  /-- `print(io, s)` of a `String`, `print(io, xs...)` of strings (by their bytes: a `String` may
  hold invalid UTF-8), `print(io, n)` of an `Int`. -/
  print : Io → String → m Unit
  printMany : Io → List (List UInt8) → m Unit
  printInt : Io → JInt64 → m Unit
  /-- `get(io, :limit, false)::Bool`, `haskey(io, :displaysize)`,
  `IOContext(io, :displaysize => displaysize(io))`. -/
  getLimit : Io → m Bool
  haskeyDisplaysize : Io → Bool
  withDisplaysize : Io → m Io
  /-- `Base.print_within_stacktrace(io, s, bold=b)`, `Base.demangle_function_name`. -/
  print_within_stacktrace : Io → String → Bool → m Unit
  demangle_function_name : String → String
  /-- `Base.show_mi(io, mi, from_stackframe)`. -/
  show_mi : Io → MI → Bool → m Unit
  /-- `Base.method_argnames(m)` (`base/methodshow.jl`). -/
  method_argnames : Meth → m (List Sym)
  /-- `Base.show_tuple_as_call(io, name, sig; demangle, kwargs, argnames)`. -/
  show_tuple_as_call : Io → Sym → Ty → Bool → Option (List (Sym × Ty)) → Option (List Sym) → m Unit
  /-- `show_custom_spec_sig(io, linfo.owner, linfo, frame)`: dispatch on the owner, which compiler
  packages may extend; the last argument runs the default method, `show_custom_spec_sig_default`
  below, for owners without a method of their own. -/
  show_custom_spec_sig : Io → CI → StackFrame MI CI Meth CInfo DI → m Unit → m Unit
  /-- `basename(path)` of `base/path.jl`: the bytes of a `String`. -/
  basename : String → List UInt8
  /-- `backtrace()`. -/
  backtrace : m (List (IP MI CI CInfo))
  /-- `isequal` on backtrace entries (the keys of `lookups`). -/
  ipEq : IP MI CI CInfo → IP MI CI CInfo → Bool
  /-- `hash(x, h)` of an `Int`, a `Symbol` and a `Bool`. -/
  hashInt : JInt64 → JInt .u64 → JInt .u64
  hashSym : Sym → JInt .u64 → JInt .u64
  hashBool : Bool → JInt .u64 → JInt .u64

section
variable {m : Type → Type} [Monad m] [MonadExceptOf StError m] {MI CI Meth CInfo DI Mod Ty RF Io : Type}

def throwSt {α : Type} (e : StError) : m α := throwThe StError e

def ofOpt {α : Type} : Option α → m α
  | some a => pure a
  | none => throwSt .typeError

def i64 (z : Int) : JInt64 := JInt.wrap .i64 z

/-- `Int32(x)` of an `Int`. -/
def toInt32 (x : JInt64) : m (JInt .i32) :=
  if IntTy.min .i32 ≤ x.val ∧ x.val ≤ IntTy.max .i32 then pure (JInt.wrap .i32 x.val)
  else throwSt (.inexactError "Int32")

-- UNTRANSLATED
-- license header, module docstring, `module StackTraces`, imports and exports; no method
-- Source: base/stacktraces.jl:1-15 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- """
-- Tools for collecting and manipulating stack traces. Mainly used for building errors.
-- """
-- module StackTraces
-- 
-- 
-- import Base: hash, ==, show
-- 
-- using Core: CodeInfo, MethodInstance, CodeInstance
-- using Base.IRShow
-- 
-- export StackTrace, StackFrame, stacktrace
-- 
-- /Source

/--
Julia source: base/stacktraces.jl:16-81 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    StackFrame

Stack information representing execution context, with the following fields:

- `func::Symbol`

  The name of the function containing the execution context.

- `linfo::Union{Method, Core.MethodInstance, Core.CodeInstance, Core.CodeInfo, Nothing}`

  The Method, MethodInstance, CodeInstance, or CodeInfo containing the execution context (if it could be found),
     or nothing (for example, if the inlining was a result of macro expansion).

- `file::Symbol`

  The path to the file containing the execution context.

- `line::Int`

  The line number in the file containing the execution context.

- `from_c::Bool`

  True if the code is from C.

- `inlined::Bool`

  True if the code is from an inlined frame.

- `pointer::UInt64`

  Representation of the pointer to the execution context as returned by `backtrace`.

- `pc::Int`

  If `from_c`, this is a column number.  Otherwise, it is a 1-based statement
  index within the frame's `linfo.debuginfo`, recovered from the DWARF column
  emitted by codegen, or `0` when debuginfo is unavailable. Used internally by
  `StackTraces.lookup` to resolve the `MethodInstance` for inlined frames; also
  surfaced in low-level safe backtrace output (e.g. on segfault) but not in
  Julia's default `show` for `StackFrame`.
"""
struct StackFrame # this type should be kept platform-agnostic so that profiles can be dumped on one machine and read on another
    "the name of the function containing the execution context"
    func::Symbol
    "the path to the file containing the execution context"
    file::Symbol
    "the line number in the file containing the execution context"
    line::Int
    "the CodeInstance or CodeInfo containing the execution context (if it could be found), \
     or nothing (for example, if the inlining was a result of macro expansion)."
    linfo::Union{Core.MethodInstance, Core.CodeInstance, Method, CodeInfo, Nothing}
    "true if the code is from C"
    from_c::Bool
    "true if the code is from an inlined frame"
    inlined::Bool
    "representation of the pointer to the execution context as returned by `backtrace`"
    pointer::UInt64  # Large enough to be read losslessly on 32- and 64-bit machines.
    "if !from_c, 1-based statement index (PC) within the frame's CodeInfo, or 0 if unavailable"
    pc::Int
    # TODO: can be redundant given `linfo`, but needed for inlined frames with
    # `linfo isa MethodInstance`
    debuginfo::Union{Core.DebugInfo, Nothing}
end

```
-/
-- `StackFrame` is the structure above.
def StackFrame_9 (func file : Sym) (line : JInt64) (linfo : Linfo MI CI Meth CInfo) (from_c inlined : Bool)
    (pointer : JInt .u64) (pc : JInt64) (debuginfo : Option DI) : StackFrame MI CI Meth CInfo DI :=
  ⟨func, file, line, linfo, from_c, inlined, pointer, pc, debuginfo⟩

/--
Julia source: base/stacktraces.jl:82-83 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
StackFrame(func, file, line, linfo, from_c, inlined, pointer) =
    StackFrame(func, file, line, linfo, from_c, inlined, pointer, 0, nothing)
```
-/
def StackFrame_7 (func file : Sym) (line : JInt64) (linfo : Linfo MI CI Meth CInfo) (from_c inlined : Bool)
    (pointer : JInt .u64) : StackFrame MI CI Meth CInfo DI :=
  StackFrame_9 func file line linfo from_c inlined pointer (i64 0) none

/--
Julia source: base/stacktraces.jl:84-86 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
StackFrame(func, file, line) = StackFrame(Symbol(func), Symbol(file), line,
                                          nothing, false, false, 0, 0, nothing)

```
-/
-- `Symbol(func)`, `Symbol(file)` and the `Int` conversion of `line` are given by `toSym` and `toInt`.
def StackFrame_3 {A B C : Type} (toSym : A → m Sym) (toSymB : B → m Sym) (toInt : C → m JInt64)
    (func : A) (file : B) (line : C) : m (StackFrame MI CI Meth CInfo DI) := do
  return StackFrame_9 (← toSym func) (← toSymB file) (← toInt line) .nothing false false (JInt.wrap .u64 0) (i64 0) none

/--
Julia source: base/stacktraces.jl:87-94 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    StackTrace

An alias for `Vector{StackFrame}` provided for convenience; returned by calls to
`stacktrace`.
"""
const StackTrace = Vector{StackFrame}

```
-/
-- `StackTrace` is `List (StackFrame …)`.
abbrev StackTrace (MI CI Meth CInfo DI : Type) := List (StackFrame MI CI Meth CInfo DI)

/--
Julia source: base/stacktraces.jl:95-95 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const empty_sym = Symbol("")
```
-/
def empty_sym : Sym := ""

/--
Julia source: base/stacktraces.jl:96-98 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const UNKNOWN = StackFrame(empty_sym, empty_sym, -1, nothing, true, false, 0) # === lookup(C_NULL)


```
-/
def UNKNOWN : StackFrame MI CI Meth CInfo DI :=
  StackFrame_7 empty_sym empty_sym (i64 (-1)) .nothing true false (JInt.wrap .u64 0) -- === lookup(C_NULL)

/--
Julia source: base/stacktraces.jl:99-106 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
#=
If the StackFrame has function and line information, we consider two of them the same if
they share the same function/line information.
=#
function ==(a::StackFrame, b::StackFrame)
    return a.line == b.line && a.from_c == b.from_c && a.func == b.func && a.file == b.file && a.inlined == b.inlined # excluding linfo and pointer
end

```
-/
def eq_StackFrame (a b : StackFrame MI CI Meth CInfo DI) : Bool :=
  a.line == b.line && a.from_c == b.from_c && a.func == b.func && a.file == b.file && a.inlined == b.inlined -- excluding linfo and pointer

/--
Julia source: base/stacktraces.jl:107-116 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function hash(frame::StackFrame, h::UInt)
    h ⊻= 0xf4fbda67fe20ce88 % UInt
    h = hash(frame.line, h)
    h = hash(frame.file, h)
    h = hash(frame.func, h)
    h = hash(frame.from_c, h)
    h = hash(frame.inlined, h)
    return h
end

```
-/
def hash_StackFrame (c : Callees m Io MI CI Meth CInfo DI Mod Ty) (frame : StackFrame MI CI Meth CInfo DI)
    (h : JInt .u64) : JInt .u64 :=
  let h := JInt.wrap .u64 (Int.ofNat (h.val.toNat ^^^ (0xf4fbda67fe20ce88 : Nat)))
  let h := c.hashInt frame.line h
  let h := c.hashSym frame.file h
  let h := c.hashSym frame.func h
  let h := c.hashBool frame.from_c h
  let h := c.hashBool frame.inlined h
  h

abbrev Frame (MI CI Meth CInfo DI : Type) := StackFrame MI CI Meth CInfo DI

mutual

/--
Julia source: base/stacktraces.jl:117-126 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _add_linetable_frames!(frames, pointer, di::Core.DebugInfo, pc::Int)
    lt, ltpc = Base.Compiler.prev_debuginfo(di, pc)
    if lt isa Core.DebugInfo
        _add_linetable_frames!(frames, pointer, lt, ltpc)
        edi, epc = Base.Compiler.edge_debuginfo(lt, ltpc)
        edi !== nothing && _add_di_frames!(frames, pointer, edi, epc)
    end
    nothing
end

```
-/
def _add_linetable_frames [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (r : Reflect m MI CI Meth CInfo DI Mod Ty RF) (frames : List (Frame MI CI Meth CInfo DI))
    (pointer : JInt .u64) (di : DI) (pc : JInt64) : m (List (Frame MI CI Meth CInfo DI)) := do
  let ltp ← r.prev_debuginfo di pc
  let ltpc ← pure ltp.2
  match ltp.1 with
  | some lt =>
    let frames ← _add_linetable_frames r frames pointer lt ltpc
    let e ← r.edge_debuginfo lt ltpc
    match e with
    | some ep => _add_di_frames r frames pointer ep.1 ep.2
    | none => pure frames
  | none => pure frames
partial_fixpoint

/--
Julia source: base/stacktraces.jl:127-147 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# 1. Push our own frame
# 2. If there is a linetable, recurse on edges there (and not the linetable)
# 3. Recurse on any of our own edges
function _add_di_frames!(frames, pointer, di::Core.DebugInfo, pc::Int)
    @assert pc > 0 "invalid pc"
    push!(frames, StackFrame(
        di.def isa Symbol ? Symbol("macro expansion") : IRShow.method_name(di.def),
        IRShow.debuginfo_file(di),
        @ccall(jl_cdi_firstxy(di::Any, pc::Int32)::NTuple{2, Int32})[1],
        di.def isa Core.MethodInstance ? di.def : nothing,
        false, # we can assume C frames aren't inlined into julia
        !isempty(frames),
        pointer,
        pc,
        di))
    _add_linetable_frames!(frames, pointer, di, pc)
    edi, epc = Base.Compiler.edge_debuginfo(di, pc)
    edi !== nothing && _add_di_frames!(frames, pointer, edi, epc)
    nothing
end

```
-/
def _add_di_frames [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (r : Reflect m MI CI Meth CInfo DI Mod Ty RF) (frames : List (Frame MI CI Meth CInfo DI))
    (pointer : JInt .u64) (di : DI) (pc : JInt64) : m (List (Frame MI CI Meth CInfo DI)) := do
  if !(pc.val > 0) then throwSt (.assertionError "invalid pc")
  let func ← if r.diDefIsSymbol di then pure "macro expansion" else r.method_name di
  let file ← r.debuginfo_file di
  let line ← r.cdi_firstxy di (← toInt32 pc)
  let linfo : Linfo MI CI Meth CInfo := match r.diDefMI di with
    | some mi => .methodInstance mi
    | none => .nothing
  let frames := frames ++ [StackFrame_9 func file (i64 line.val) linfo
    false -- we can assume C frames aren't inlined into julia
    (!frames.isEmpty) pointer pc (some di)]
  let frames ← _add_linetable_frames r frames pointer di pc
  let e ← r.edge_debuginfo di pc
  match e with
  | some ep => _add_di_frames r frames pointer ep.1 ep.2
  | none => pure frames
partial_fixpoint

end

/-- The `for i in 1:length(frames)` loop of `lookup(pointer)`. -/
def lookup_frames_loop (r : Reflect m MI CI Meth CInfo DI Mod Ty RF) (pointer : JInt .u64) :
    List RF → m (List (Frame MI CI Meth CInfo DI))
  | [] => pure []
  | f :: fs => do
    if !(r.rfLength f == 7) then throwSt (.assertionError "corrupt return from jl_lookup_code_address")
    let func ← ofOpt (r.rfSym f 1)
    let file ← ofOpt (r.rfSym f 2)
    let linenum ← ofOpt (r.rfInt f 3)
    let linfo := r.rfLinfo f
    let from_c ← ofOpt (r.rfBool f 5)
    let inlined ← ofOpt (r.rfBool f 6)
    let sv_pc ← if from_c then ofOpt (r.rfInt f 7) else pure (i64 0)
    -- `StackFrame(...)` converts `linfo` to the field type
    let linfo ← ofOpt linfo
    let rest ← lookup_frames_loop r pointer fs
    return StackFrame_9 func file linenum linfo from_c inlined pointer sv_pc none :: rest

/--
Julia source: base/stacktraces.jl:148-196 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    lookup(pointer::Ptr{Cvoid})::Vector{StackFrame}

Given a pointer to an execution context (usually generated by a call to `backtrace`), looks
up stack frame context information. Returns an array of frame information for all functions
inlined at that point, innermost function first.
"""
Base.@constprop :none function lookup(pointer::Ptr{Cvoid})
    frames = @ccall jl_lookup_code_address(pointer::Ptr{Cvoid}, false::Cint)::Core.SimpleVector
    pointer = convert(UInt64, pointer)

    # this is equal to UNKNOWN
    isempty(frames) && return [StackFrame(
        empty_sym, empty_sym, -1, nothing, true, false, pointer)]

    # If we aren't given a PC and CodeInstance for the last (non-inlined) frame,
    # we can't recover any more information than `frames`, so use those.
    # Otherwise, DebugInfo lets us recover `linfo` for inlined frames too, so
    # ignore `frames` and construct them by traversing the DebugInfo tree
    # instead.  This is a separate code path since attempting to enhance
    # existing `frames` would require matching them to our tree traversal.
    pc = frames[end][5]::Bool ? 0 : frames[end][7]::Int
    di = let x = frames[end][4]
        x isa Core.CodeInstance ? x.debuginfo : nothing
    end
    if pc <= 0 || !(di isa Core.DebugInfo)
        out = Vector{StackFrame}(undef, length(frames))
        for i in 1:length(frames)
            f = frames[i]
            @assert length(f) == 7 "corrupt return from jl_lookup_code_address"
            func = f[1]::Symbol
            file = f[2]::Symbol
            linenum = f[3]::Int
            linfo = f[4]
            from_c = f[5]::Bool
            inlined = f[6]::Bool
            sv_pc = from_c ? f[7]::Int : 0
            out[i] = StackFrame(
                func, file, linenum, linfo, from_c, inlined, pointer, sv_pc,
                nothing)
        end
    else
        out = Vector{StackFrame}()
        _add_di_frames!(out, pointer, di, pc)
        reverse!(out)
    end
    return out
end

```
-/
def lookup_Ptr [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (r : Reflect m MI CI Meth CInfo DI Mod Ty RF)
    (pointer : JInt .u64) : m (List (Frame MI CI Meth CInfo DI)) := do
  let frames ← r.lookup_code_address pointer
  -- `convert(UInt64, pointer)`
  -- this is equal to UNKNOWN
  match frames.getLast? with
  | none => return [StackFrame_7 empty_sym empty_sym (i64 (-1)) .nothing true false pointer]
  | some last =>
    -- If we aren't given a PC and CodeInstance for the last (non-inlined) frame,
    -- we can't recover any more information than `frames`, so use those.
    -- Otherwise, DebugInfo lets us recover `linfo` for inlined frames too, so
    -- ignore `frames` and construct them by traversing the DebugInfo tree
    -- instead.  This is a separate code path since attempting to enhance
    -- existing `frames` would require matching them to our tree traversal.
    let pc ← if (← ofOpt (r.rfBool last 5)) then pure (i64 0) else ofOpt (r.rfInt last 7)
    let di := match r.rfCodeInstance last with
      | some x => r.ciDebuginfo x
      | none => none
    match di with
    | some di =>
      if pc.val ≤ 0 then
        lookup_frames_loop r pointer frames
      else
        let out ← _add_di_frames r [] pointer di pc
        return out.reverse
    | none => lookup_frames_loop r pointer frames

/--
Julia source: base/stacktraces.jl:197-198 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const top_level_scope_sym = Symbol("top-level scope")

```
-/
def top_level_scope_sym : Sym := "top-level scope"

/--
Julia source: base/stacktraces.jl:199-232 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Interpreted => unoptimized => no inlined frames, so >1 frames are returned
# only with code from macro expansions.
function lookup(ip::Base.InterpreterIP)
    code = ip.code
    pc::Int = max(ip.stmt + 1, 0) # n.b. ip.stmt is 0-indexed
    if code === nothing
        return [StackFrame(
            top_level_scope_sym, empty_sym, 0, nothing, false, false, 0)]
    elseif code isa MethodInstance && (meth = code.def; meth isa Method)
        func = meth.name
        linfo = code
        codeinfo = meth.source
    elseif code isa Core.CodeInstance
        # uninferred CodeInstances have no `debuginfo`
        codeinfo = code.inferred::CodeInfo
        def = code.def isa Core.ABIOverride ? code.def.def : code.def
        @assert def isa MethodInstance lazy"unexpected $(typeof(def))"
        meth = def.def
        func = meth isa Method ? meth.name : top_level_scope_sym
        linfo = def
    else
        codeinfo = code::CodeInfo
        linfo = codeinfo
        func = top_level_scope_sym
    end
    di = codeinfo.debuginfo
    line = pc > 0 ? @ccall(jl_cdi_firstxy(di::Any, pc::Int32)::NTuple{2, Int32})[1] :
        IRShow.debuginfo_firstline(di)[2]
    frames = [StackFrame(func, IRShow.debuginfo_file(di), line, linfo, false, false, 0, pc, di)]
    edi, epc = Base.Compiler.edge_debuginfo(di, pc)
    edi !== nothing && _add_di_frames!(frames, 0, edi, epc)
    return reverse!(frames)
end

```
-/
def lookup_InterpreterIP [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (r : Reflect m MI CI Meth CInfo DI Mod Ty RF)
    (ip : InterpreterIP MI CI CInfo) : m (List (Frame MI CI Meth CInfo DI)) := do
  let code := ip.code
  -- `max(ip.stmt + 1, 0)` wraps in `UInt` (n.b. ip.stmt is 0-indexed); `pc::Int` converts it
  let s1 := JInt.wrap .u64 (ip.stmt.val + 1)
  if s1.val > IntTy.max .i64 then throwSt (.inexactError "Int64")
  let pc := i64 s1.val
  if let .nothing := code then
    return [StackFrame_7 top_level_scope_sym empty_sym (i64 0) .nothing false false (JInt.wrap .u64 0)]
  let (func, linfo, codeinfo) ← match code with
    | .methodInstance mi =>
      match r.miDef mi with
      | .method meth => do pure (r.methName meth, Linfo.methodInstance mi, ← r.methSource meth)
      -- otherwise the `else` branch: `code::CodeInfo` fails for a `MethodInstance`
      | .module _ => throwSt .typeError
    | .codeInstance ci => do
      -- uninferred CodeInstances have no `debuginfo`
      let codeinfo ← ofOpt (r.ciInferred ci)
      let dfn ← match r.ciDef ci with
        | .abiOverride (some d) => pure d
        | .mi d => pure d
        | _ => throwSt (.assertionError ("unexpected " ++ r.ciUnwrappedDefTypeName ci))
      let func := match r.miDef dfn with
        | .method meth => r.methName meth
        | .module _ => top_level_scope_sym
      pure (func, Linfo.methodInstance dfn, codeinfo)
    | .codeInfo ci => pure (top_level_scope_sym, Linfo.codeInfo ci, ci)
    | .nothing => throwSt .typeError
  let di := r.cinfoDebuginfo codeinfo
  let line ← if pc.val > 0 then do pure (i64 (← r.cdi_firstxy di (← toInt32 pc)).val) else r.debuginfo_firstline di
  let frames := [StackFrame_9 func (← r.debuginfo_file di) line linfo false false (JInt.wrap .u64 0) pc (some di)]
  let e ← r.edge_debuginfo di pc
  let frames ← match e with
    | some ep => _add_di_frames r frames (JInt.wrap .u64 0) ep.1 ep.2
    | none => pure frames
  return frames.reverse

/-- *dispatch*: `lookup(ip)`. -/
def lookup [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (r : Reflect m MI CI Meth CInfo DI Mod Ty RF) :
    IP MI CI CInfo → m (List (Frame MI CI Meth CInfo DI))
  | .ptr p => lookup_Ptr r p
  | .interp ip => lookup_InterpreterIP r ip

/-- `get(lookups, ip, nothing)` on the association list of `lookups`. -/
def lookupsGet (c : Callees m Io MI CI Meth CInfo DI Mod Ty) (lookups : List (IP MI CI CInfo × List (Frame MI CI Meth CInfo DI)))
    (ip : IP MI CI CInfo) : Option (List (Frame MI CI Meth CInfo DI)) :=
  (lookups.find? fun e => c.ipEq e.1 ip).map Prod.snd

/-- The `for ip in trace` loop of `stacktrace(trace, c_funcs)`. -/
def stacktrace_loop [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (r : Reflect m MI CI Meth CInfo DI Mod Ty RF)
    (c : Callees m Io MI CI Meth CInfo DI Mod Ty) (c_funcs : Bool)
    (stack : List (Frame MI CI Meth CInfo DI)) (lookups : List (IP MI CI CInfo × List (Frame MI CI Meth CInfo DI))) :
    List (IP MI CI CInfo) → m (List (Frame MI CI Meth CInfo DI))
  | [] => pure stack
  | ip :: ips => do
    let (frames, lookups) ← match lookupsGet c lookups ip with
      | some frames => pure (frames, lookups)
      | none => do
        let frames ← lookup r ip
        pure (frames, lookups ++ [(ip, frames)])
    -- Skip frames that come from C calls.
    let stack := stack ++ frames.filter fun frame => c_funcs || !frame.from_c
    stacktrace_loop r c c_funcs stack lookups ips

/--
Julia source: base/stacktraces.jl:233-255 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    stacktrace([trace::Vector{Ptr{Cvoid}},] [c_funcs::Bool=false])::StackTrace

Return a stack trace in the form of a vector of `StackFrame`s. (By default stacktrace
doesn't return C functions, but this can be enabled.) When called without specifying a
trace, `stacktrace` first calls `backtrace`.
"""
Base.@constprop :none function stacktrace(trace::Vector{<:Union{Base.InterpreterIP,Ptr{Cvoid}}}, c_funcs::Bool=false)
    stack = StackTrace()
    lookups = Dict{eltype(trace),StackTrace}()
    for ip in trace
        frames = get(lookups, ip, nothing)
        frames === nothing && (frames = lookups[ip] = lookup(ip))
        for frame in frames
            # Skip frames that come from C calls.
            if c_funcs || !frame.from_c
                push!(stack, frame)
            end
        end
    end
    return stack
end

```
-/
def stacktrace_trace [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (r : Reflect m MI CI Meth CInfo DI Mod Ty RF)
    (c : Callees m Io MI CI Meth CInfo DI Mod Ty) (trace : List (IP MI CI CInfo)) (c_funcs : Bool := false) :
    m (List (Frame MI CI Meth CInfo DI)) :=
  stacktrace_loop r c c_funcs [] [] trace

/--
Julia source: base/stacktraces.jl:265-277 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    remove_frames!(stack::StackTrace, name::Symbol)

Takes a `StackTrace` (a vector of `StackFrames`) and a function name (a `Symbol`) and
removes the `StackFrame` specified by the function name from the `StackTrace` (also removing
all frames above the specified function). Primarily used to remove `StackTraces` functions
from the `StackTrace` prior to returning it.
"""
function remove_frames!(stack::StackTrace, name::Symbol)
    deleteat!(stack, 1:something(findlast(frame -> frame.func == name, stack), 0))
    return stack
end

```
-/
def remove_frames_Symbol (stack : List (Frame MI CI Meth CInfo DI)) (name : Sym) : List (Frame MI CI Meth CInfo DI) :=
  -- `1:something(findlast(frame -> frame.func == name, stack), 0)`
  let k := match (stack.reverse.findIdx? fun frame => frame.func == name) with
    | some j => stack.length - j
    | none => 0
  stack.drop k

/--
Julia source: base/stacktraces.jl:278-282 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function remove_frames!(stack::StackTrace, names::Vector{Symbol})
    deleteat!(stack, 1:something(findlast(frame -> frame.func in names, stack), 0))
    return stack
end

```
-/
def remove_frames_Vector (stack : List (Frame MI CI Meth CInfo DI)) (names : List Sym) : List (Frame MI CI Meth CInfo DI) :=
  let k := match (stack.reverse.findIdx? fun frame => names.contains frame.func) with
    | some j => stack.length - j
    | none => 0
  stack.drop k

/--
Julia source: base/stacktraces.jl:256-264 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@constprop :none function stacktrace(c_funcs::Bool=false)
    stack = stacktrace(backtrace(), c_funcs)
    # Remove frame for this function (and any functions called by this function).
    remove_frames!(stack, :stacktrace)
    # also remove all of the non-Julia functions that led up to this point (if that list is non-empty)
    c_funcs && deleteat!(stack, 1:(something(findfirst(frame -> !frame.from_c, stack), 1) - 1))
    return stack
end

```
-/
def stacktrace_cfuncs [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (r : Reflect m MI CI Meth CInfo DI Mod Ty RF)
    (c : Callees m Io MI CI Meth CInfo DI Mod Ty) (c_funcs : Bool := false) : m (List (Frame MI CI Meth CInfo DI)) := do
  let stack ← stacktrace_trace r c (← c.backtrace) c_funcs
  -- Remove frame for this function (and any functions called by this function).
  let stack := remove_frames_Symbol stack "stacktrace"
  -- also remove all of the non-Julia functions that led up to this point (if that list is non-empty)
  let stack := if c_funcs then
      let k := match stack.findIdx? (fun frame => !frame.from_c) with
        | some j => j + 1
        | none => 1
      stack.drop (k - 1)
    else stack
  return stack

/--
Julia source: base/stacktraces.jl:425-450 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.parentmodule(frame::StackFrame)
    linfo = frame.linfo
    if linfo isa CodeInstance
        linfo = linfo.def
        if isa(linfo, Core.ABIOverride)
            linfo = linfo.def
        end
    end
    if linfo isa MethodInstance
        def = linfo.def
        if def isa Module
            return def
        else
            return (def::Method).module
        end
    elseif linfo isa Method
        return linfo.module
    elseif linfo isa Module
        return linfo
    else
        # The module is not always available (common reasons include
        # frames arising from the interpreter)
        nothing
    end
end

```
-/
def parentmodule_StackFrame (r : Reflect m MI CI Meth CInfo DI Mod Ty RF) (frame : Frame MI CI Meth CInfo DI) : Option Mod :=
  -- `linfo isa CodeInstance`: `linfo = linfo.def`, then the `def` of a `Core.ABIOverride`
  let mi : Option MI := match frame.linfo with
    | .codeInstance ci => match r.ciDef ci with
      | .mi x => some x
      | .abiOverride d => d
      | .other => none
    | .methodInstance x => some x
    | _ => none
  match mi with
  | some mi => match r.miDef mi with
    | .module dfn => some dfn
    | .method dfn => some (r.methModule dfn)
  | none => match frame.linfo with
    | .method meth => some (r.methModule meth)
    -- `linfo isa Module` never holds for the field type
    | _ =>
      -- The module is not always available (common reasons include
      -- frames arising from the interpreter)
      none

/--
Julia source: base/stacktraces.jl:451-459 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    from(frame::StackFrame, filter_mod::Module)::Bool

Return whether the `frame` is from the provided `Module`
"""
function from(frame::StackFrame, m::Module)
    return parentmodule(frame) === m
end

```
-/
def from_frame (r : Reflect m MI CI Meth CInfo DI Mod Ty RF) (frame : Frame MI CI Meth CInfo DI) (mod : Mod) : Bool :=
  match parentmodule_StackFrame r frame with
  | some p => r.egalMod p mod
  | none => false

/--
Julia source: base/stacktraces.jl:283-292 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    remove_frames!(stack::StackTrace, m::Module)

Return the `StackTrace` with all `StackFrame`s from the provided `Module` removed.
"""
function remove_frames!(stack::StackTrace, m::Module)
    filter!(f -> !from(f, m), stack)
    return stack
end

```
-/
def remove_frames_Module (r : Reflect m MI CI Meth CInfo DI Mod Ty RF) (stack : List (Frame MI CI Meth CInfo DI))
    (mod : Mod) : List (Frame MI CI Meth CInfo DI) :=
  stack.filter fun f => !from_frame r f mod

/--
Julia source: base/stacktraces.jl:293-294 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
is_top_level_frame(f::StackFrame) = f.linfo isa CodeInfo || (f.linfo === nothing && f.func === top_level_scope_sym)

```
-/
def is_top_level_frame (f : Frame MI CI Meth CInfo DI) : Bool :=
  (match f.linfo with | .codeInfo _ => true | _ => false) ||
    ((match f.linfo with | .nothing => true | _ => false) && f.func == top_level_scope_sym)

/--
Julia source: base/stacktraces.jl:304-311 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function frame_mi(lkup::StackFrame)
    code = lkup.linfo
    code isa Core.CodeInstance && (code = code.def)
    code isa Core.ABIOverride && (code = code.def)
    code isa MethodInstance || return nothing
    return code
end

```
-/
def frame_mi (r : Reflect m MI CI Meth CInfo DI Mod Ty RF) (lkup : Frame MI CI Meth CInfo DI) : Option MI :=
  match lkup.linfo with
  | .codeInstance ci => match r.ciDef ci with
    | .mi x => some x
    | .abiOverride d => d
    | .other => none
  | .methodInstance x => some x
  | _ => none

/--
Julia source: base/stacktraces.jl:295-303 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function frame_method_or_module(lkup::StackFrame)
    code = lkup.linfo
    code isa Method && return code
    code isa Module && return code
    mi = frame_mi(lkup)
    mi isa MethodInstance || return nothing
    return mi.def
end

```
-/
def frame_method_or_module (r : Reflect m MI CI Meth CInfo DI Mod Ty RF) (lkup : Frame MI CI Meth CInfo DI) :
    Option (MIDef Meth Mod) :=
  match lkup.linfo with
  | .method code => some (.method code)
  -- (`code isa Module` never holds for the field type)
  | _ => match frame_mi r lkup with
    | none => none
    | some mi => some (r.miDef mi)

/-- The `while Base.Compiler.has_prev_debuginfo(di, pc)` loop of `frame_location`. -/
def prev_debuginfo_loop [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (r : Reflect m MI CI Meth CInfo DI Mod Ty RF)
    (di : DI) (pc : JInt64) : m (DI × JInt64) := do
  let h ← r.has_prev_debuginfo di pc
  if h then
    let p ← r.prev_debuginfo di pc
    match p.1 with
    | some d => prev_debuginfo_loop r d p.2
    -- the next `has_prev_debuginfo` call has no method for a value that is not a `DebugInfo`
    | none => throwSt (.methodError "has_prev_debuginfo")
  else
    pure (di, pc)
partial_fixpoint

/--
Julia source: base/stacktraces.jl:312-332 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function frame_location(frame::StackFrame)
    if frame.from_c
        Base.Compiler.SourceLocation(0,0,frame.pc,0,frame.line,0)
    elseif isnothing(frame.debuginfo) || frame.pc <= 0
        Base.Compiler.SourceLocation(0,0,0,0,frame.line,0)
    else
        # Ideally this would just be a source_location call, but we need to
        # check for pc=0 recursively since source_location doesn't have a good
        # answer for pc=0 until we stop producing it from lowering.
        di, pc = frame.debuginfo, frame.pc
        while Base.Compiler.has_prev_debuginfo(di, pc)
            di, pc = Base.Compiler.prev_debuginfo(di, pc)
        end
        if pc <= 0
            Base.Compiler.SourceLocation(0,0,0,0,frame.line,0)
        else
            Base.Compiler.source_location(frame.debuginfo, frame.pc)
        end
    end
end

```
-/
def frame_location [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (r : Reflect m MI CI Meth CInfo DI Mod Ty RF)
    (frame : Frame MI CI Meth CInfo DI) : m SourceLocation := do
  if frame.from_c then
    return ⟨i64 0, i64 0, frame.pc, i64 0, frame.line, i64 0⟩
  match frame.debuginfo with
  | none => return ⟨i64 0, i64 0, i64 0, i64 0, frame.line, i64 0⟩
  | some fdi =>
    if frame.pc.val ≤ 0 then
      return ⟨i64 0, i64 0, i64 0, i64 0, frame.line, i64 0⟩
    -- Ideally this would just be a source_location call, but we need to
    -- check for pc=0 recursively since source_location doesn't have a good
    -- answer for pc=0 until we stop producing it from lowering.
    let (_, pc) ← prev_debuginfo_loop r fdi frame.pc
    if pc.val ≤ 0 then
      return ⟨i64 0, i64 0, i64 0, i64 0, frame.line, i64 0⟩
    else
      r.source_location fdi frame.pc

/-- `s[1:end-3]` of a `String` ending in `"..."`: a `StringIndexError` when the byte before the
dots is not the last byte of a character. -/
def dropDots (s : String) : m String := do
  let bs := s.toUTF8.toList
  let j := bs.length - 3
  let jValid := j == 0 || (match bs[j - 1]? with
    | some b => b &&& 0xC0 != 0x80
    | none => false)
  if !jValid then throwSt .stringIndexError
  return String.fromUTF8! ⟨(bs.take j).toArray⟩

/-- `kwarg_types = Any[fieldtype(sig, i) for i = 2:(1+m.nkw)]`. -/
def kwarg_types_loop (r : Reflect m MI CI Meth CInfo DI Mod Ty RF) (sig : Ty) : Nat → m (List Ty)
  | 0 => pure []
  | k + 1 => do
    let earlier ← kwarg_types_loop r sig k
    return earlier ++ [← r.fieldtype sig (i64 (k + 2))]

/--
Julia source: base/stacktraces.jl:374-402 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_spec_sig(io::IO, m::Method, @nospecialize(sig::Type))
    if get(io, :limit, :false)::Bool
        if !haskey(io, :displaysize)
            io = IOContext(io, :displaysize => displaysize(io))
        end
    end
    argnames = Base.method_argnames(m)
    argnames = replace(argnames, :var"#unused#" => :var"")
    if m.nkw > 0
        # rearrange call kw_impl(kw_args..., func, pos_args...) to func(pos_args...; kw_args)
        kwarg_types = Any[ fieldtype(sig, i) for i = 2:(1+m.nkw) ]
        uw = Base.unwrap_unionall(sig)::DataType
        pos_sig = Base.rewrap_unionall(Tuple{uw.parameters[(m.nkw+2):end]...}, sig)
        kwnames = argnames[2:(m.nkw+1)]
        for i = 1:length(kwnames)
            str = string(kwnames[i])::String
            if endswith(str, "...")
                kwnames[i] = Symbol(str[1:end-3])
            end
        end
        Base.show_tuple_as_call(io, m.name, pos_sig;
                                demangle=true,
                                kwargs=zip(kwnames, kwarg_types),
                                argnames=argnames[m.nkw+2:end])
    else
        Base.show_tuple_as_call(io, m.name, sig; demangle=true, argnames)
    end
end

```
-/
def show_spec_sig (r : Reflect m MI CI Meth CInfo DI Mod Ty RF) (c : Callees m Io MI CI Meth CInfo DI Mod Ty)
    (io : Io) (meth : Meth) (sig : Ty) : m Unit := do
  let mut io := io
  if ← c.getLimit io then
    if !c.haskeyDisplaysize io then
      io ← c.withDisplaysize io
  let argnames ← c.method_argnames meth
  let argnames := argnames.map fun a => if a == "#unused#" then "" else a
  let nkw := (r.nkw meth).val
  if nkw > 0 then
    -- rearrange call kw_impl(kw_args..., func, pos_args...) to func(pos_args...; kw_args)
    let kwarg_types ← kwarg_types_loop r sig nkw.toNat
    let uw ← r.parameters (r.unwrap_unionall sig)
    let pos_sig := r.rewrap_unionall (r.tupleOf (uw.drop (nkw + 1).toNat)) sig
    -- `argnames[2:(m.nkw+1)]`
    if nkw + 1 > argnames.length then throwSt .boundsError
    let kwnames := (argnames.drop 1).take nkw.toNat
    let kwnames ← kwnames.mapM fun str => do
      if str.endsWith "..." then dropDots str else pure str
    c.show_tuple_as_call io (r.methName meth) pos_sig true (some (kwnames.zip kwarg_types))
      (some (argnames.drop (nkw + 1).toNat))
  else
    c.show_tuple_as_call io (r.methName meth) sig true none (some argnames)

/--
Julia source: base/stacktraces.jl:367-373 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Can be extended by compiler packages to customize backtrace display of custom code instance frames
function show_custom_spec_sig(io::IO, @nospecialize(owner), linfo::CodeInstance, frame::StackFrame)
    mi = Base.get_ci_mi(linfo)
    m = mi.def::Method # the case ::Module is handled in show_spec_linfo
    return show_spec_sig(io, m, mi.specTypes)
end

```
-/
def show_custom_spec_sig_default (r : Reflect m MI CI Meth CInfo DI Mod Ty RF) (c : Callees m Io MI CI Meth CInfo DI Mod Ty)
    (io : Io) (linfo : CI) (_frame : Frame MI CI Meth CInfo DI) : m Unit := do
  let mi ← r.get_ci_mi linfo
  -- the case ::Module is handled in show_spec_linfo
  let meth ← match r.miDef mi with
    | .method x => pure x
    | .module _ => throwSt .typeError
  show_spec_sig r c io meth (r.specTypes mi)

/-- `string(x, base=16)` of a `UInt64`: lowercase hexadecimal digits without padding. -/
def hexStr (x : JInt .u64) : String := String.ofList (Nat.toDigits 16 x.val.toNat)

/--
Julia source: base/stacktraces.jl:333-366 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_spec_linfo(io::IO, frame::StackFrame)
    linfo = frame.linfo
    if linfo === nothing
        if frame.func === empty_sym
            print(io, "ip:0x", string(frame.pointer, base=16))
        elseif frame.func === top_level_scope_sym
            print(io, "top-level scope")
        else
            Base.print_within_stacktrace(io, Base.demangle_function_name(string(frame.func)), bold=true)
        end
    elseif linfo isa CodeInfo
        print(io, "top-level scope")
    elseif linfo isa Module
        Base.print_within_stacktrace(io, Base.demangle_function_name(string(frame.func)), bold=true)
    else
        if linfo isa Union{MethodInstance, CodeInstance}
            def = frame_method_or_module(frame)
            if def isa Module
                Base.show_mi(io, linfo::MethodInstance, #=from_stackframe=#true)
            elseif linfo isa CodeInstance && linfo.owner !== nothing
                show_custom_spec_sig(io, linfo.owner, linfo, frame)
            else
                # Equivalent to the default implementation of `show_custom_spec_sig`
                # for `linfo isa CodeInstance`, but saves an extra dynamic dispatch.
                mi = frame_mi(frame)::MethodInstance
                show_spec_sig(io, def::Method, mi.specTypes)
            end
        else
            m = linfo::Method
            show_spec_sig(io, m, m.sig)
        end
    end
end

```
-/
def show_spec_linfo (r : Reflect m MI CI Meth CInfo DI Mod Ty RF) (c : Callees m Io MI CI Meth CInfo DI Mod Ty)
    (io : Io) (frame : Frame MI CI Meth CInfo DI) : m Unit := do
  match frame.linfo with
  | .nothing =>
    if frame.func == empty_sym then
      c.printMany io ["ip:0x".toUTF8.toList, (hexStr frame.pointer).toUTF8.toList]
    else if frame.func == top_level_scope_sym then
      c.print io "top-level scope"
    else
      c.print_within_stacktrace io (c.demangle_function_name frame.func) true
  | .codeInfo _ => c.print io "top-level scope"
  -- (`linfo isa Module` never holds for the field type)
  | .method meth => show_spec_sig r c io meth (r.methSig meth)
  | linfo =>
    -- `linfo isa Union{MethodInstance, CodeInstance}`
    let dfn := frame_method_or_module r frame
    match dfn with
    | some (.module _) =>
      match linfo with
      | .methodInstance mi => c.show_mi io mi true
      | _ => throwSt .typeError
    | _ =>
      match linfo with
      | .codeInstance ci =>
        if r.ciHasOwner ci then
          c.show_custom_spec_sig io ci frame (show_custom_spec_sig_default r c io ci frame)
          return
      | _ => pure ()
      -- Equivalent to the default implementation of `show_custom_spec_sig`
      -- for `linfo isa CodeInstance`, but saves an extra dynamic dispatch.
      let mi ← ofOpt (frame_mi r frame)
      let meth ← match dfn with
        | some (.method x) => pure x
        | _ => throwSt .typeError
      show_spec_sig r c io meth (r.specTypes mi)

/--
Julia source: base/stacktraces.jl:403-424 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, frame::StackFrame)
    show_spec_linfo(io, frame)
    if frame.file !== empty_sym
        file_info = basename(string(frame.file))
        print(io, " at ")
        print(io, file_info, ":")
        fl = frame_location(frame)
        if fl.line >= 0
            print(io, fl.line)
        else
            print(io, "?")
        end
        if fl.col != 0
            print(io, ":")
            print(io, fl.col)
        end
    end
    if frame.inlined
        print(io, " [inlined]")
    end
end

```
-/
def show_StackFrame [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (r : Reflect m MI CI Meth CInfo DI Mod Ty RF)
    (c : Callees m Io MI CI Meth CInfo DI Mod Ty) (io : Io) (frame : Frame MI CI Meth CInfo DI) : m Unit := do
  show_spec_linfo r c io frame
  if frame.file != empty_sym then
    let file_info := c.basename frame.file
    c.print io " at "
    c.printMany io [file_info, ":".toUTF8.toList]
    let fl ← frame_location r frame
    if fl.line.val ≥ 0 then
      c.printInt io fl.line
    else
      c.print io "?"
    if fl.col.val != 0 then
      c.print io ":"
      c.printInt io fl.col
  if frame.inlined then
    c.print io " [inlined]"

-- UNTRANSLATED
-- end of `module StackTraces`; no method
-- Source: base/stacktraces.jl:460-460 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- end  # module StackTraces
-- /Source

end

end JuliaLean.base.stacktraces


namespace JuliaLean.ErrorShow


/-! ### Stack traces and active exceptions -/

structure Frame where
  functionName : String
  file : String := ""
  line : Int := 0
  fromC : Bool := false
  deriving Repr, DecidableEq

inductive LookupInput where
  | unknown
  | raw (frames : List Frame)
  | debugTraversal (outermostFirst : List Frame)
  deriving Repr, DecidableEq

/-- The three result paths of `StackTraces.lookup`,
`base/stacktraces.jl:155-195,201-230`. DebugInfo traversal builds the outer
frame first and reverses before returning the documented innermost-first list. -/
def lookupFrames : LookupInput → List Frame
  | .unknown => [{ functionName := "", file := "", line := -1, fromC := true }]
  | .raw frames => frames
  | .debugTraversal frames => frames.reverse

/-- `remove_frames!`, `base/stacktraces.jl:270-277`: retain exactly the frames
after the last matching frame. -/
def removeFrames (stack : List Frame) (names : List String) : List Frame :=
  (stack.reverse.takeWhile fun frame => !names.contains frame.functionName).reverse

end JuliaLean.ErrorShow

namespace JuliaLean.ErrorShow.Coverage

open JuliaLean.ErrorShow

/-! ### `base/stacktraces.jl` -/

structure FullFrame where
  functionName : String
  file : String
  line : Int
  linfo : Option Nat := none
  fromC : Bool := false
  inlined : Bool := false
  pointer : Nat := 0
  pc : Int := 0
  moduleId : Option Nat := none
  deriving Repr, DecidableEq

/-- StackFrame constructors, lines 82-85. -/
def shortFrame (functionName file : String) (line : Int) : FullFrame :=
  { functionName, file, line }

/-- `==(StackFrame,StackFrame)`, lines 103-105. -/
def frameEqual (left right : FullFrame) : Bool :=
  left.line == right.line && left.fromC == right.fromC &&
    left.functionName == right.functionName && left.file == right.file &&
    left.inlined == right.inlined

/-- `hash(StackFrame)`, lines 107-115, using an abstract component hash. -/
def frameHash (hashPart : Nat → Nat → Nat) (frame : FullFrame) (seed : Nat) : Nat :=
  let seed := seed ^^^ 0xf4fbda67fe20ce88
  let seed := hashPart frame.line.natAbs seed
  let seed := hashPart frame.file.length seed
  let seed := hashPart frame.functionName.length seed
  let seed := hashPart (if frame.fromC then 1 else 0) seed
  hashPart (if frame.inlined then 1 else 0) seed

def flattenLookups (lookups : List (List FullFrame)) (includeC : Bool) : List FullFrame :=
  (lookups.flatten).filter fun frame => includeC || !frame.fromC

def removeModuleFrames (stack : List FullFrame) (moduleId : Nat) : List FullFrame :=
  stack.filter fun frame => frame.moduleId != some moduleId

def isTopLevelFrame (frame : FullFrame) (isCodeInfo : Bool) : Bool :=
  isCodeInfo || (frame.linfo.isNone && frame.functionName == "top-level scope")

inductive FrameOwner where
  | method (id : Nat)
  | moduleId (id : Nat)
  | none
  deriving Repr, DecidableEq

def frameMethodOrModule (linfoOwner : Option FrameOwner) : FrameOwner :=
  linfoOwner.getD .none

def frameMethodInstance (linfo : Option Nat) : Option Nat := linfo

def frameLocation (source : Option (String × Int × Int))
    (fallbackFile : String) (fallbackLine pc : Int) : String × Int × Int :=
  source.getD (fallbackFile, fallbackLine, pc)

def addDebugFrames (own : FullFrame) (lineTableEdges ownEdges : List (List FullFrame)) :
    List FullFrame :=
  own :: (lineTableEdges.flatten ++ ownEdges.flatten)

def showFrame (signature location : String) (inlined : Bool) : String :=
  signature ++ (if location.isEmpty then "" else " at " ++ location) ++
    (if inlined then " [inlined]" else "")

def parentModuleOfFrame (methodModule codeModule : Option Nat) : Option Nat :=
  methodModule.orElse fun _ => codeModule

def fromModule (frameModule target : Option Nat) : Bool := frameModule == target

end JuliaLean.ErrorShow.Coverage


namespace JuliaLean.ErrorShow.StacktracesFaithful

open JuliaLean.ErrorShow.Coverage

structure StackFrameM where
  functionName : String
  file : String
  line : Int
  linfo : Option String := none
  fromC : Bool := false
  inlined : Bool := false
  pointer : Nat := 0
  pc : Int := 0
  debugId : Option Nat := none
  moduleName : Option String := none
  column : Int := 0
  deriving Repr, DecidableEq, BEq, Inhabited

def stackFrameSeven (functionName file : String) (line : Int) (linfo : Option String)
    (fromC inlined : Bool) (pointer : Nat) : StackFrameM :=
  { functionName, file, line, linfo, fromC, inlined, pointer }

def stackFrameThree (functionName file : String) (line : Int) : StackFrameM :=
  { functionName, file, line }

def frameEqual (a b : StackFrameM) : Bool :=
  a.line == b.line && a.fromC == b.fromC && a.functionName == b.functionName &&
    a.file == b.file && a.inlined == b.inlined

def frameHash (hashPart : String → Nat → Nat) (frame : StackFrameM) (seed : Nat) : Nat :=
  let seed := seed ^^^ 0xf4fbda67fe20ce88
  let seed := hashPart (toString frame.line) seed
  let seed := hashPart frame.file seed
  let seed := hashPart frame.functionName seed
  let seed := hashPart (toString frame.fromC) seed
  hashPart (toString frame.inlined) seed

structure DebugNode where
  frame : StackFrameM
  lineTable : List StackFrameM
  edgeFrames : List StackFrameM
  deriving Repr, DecidableEq

def addLineTableFrames (frames : List StackFrameM) (lineTable edgeFrames : List StackFrameM) :
    List StackFrameM :=
  frames ++ lineTable ++ edgeFrames

def addDebugFrames (frames : List StackFrameM) (node : DebugNode) : List StackFrameM :=
  addLineTableFrames (frames ++ [node.frame]) node.lineTable node.edgeFrames

structure RawLookupFrame where
  frame : StackFrameM
  pc : Int
  deriving Repr, DecidableEq, Inhabited

def lookupPointer (pointer : Nat) (raw : List RawLookupFrame)
    (debugTree : Option (List StackFrameM)) : List StackFrameM :=
  match raw with
  | [] => [{ functionName := "", file := "", line := -1, fromC := true, pointer }]
  | _ =>
      let last := raw.getLast!
      if last.frame.fromC || last.pc ≤ 0 || debugTree.isNone then
        raw.map fun item => { item.frame with pointer, pc := if item.frame.fromC then item.pc else 0 }
      else debugTree.get!.reverse

inductive InterpreterCode where
  | none
  | method (functionName file : String) (line : Int) (edges : List StackFrameM)
  | codeInfo (file : String) (line : Int) (edges : List StackFrameM)
  deriving Repr, DecidableEq

def lookupInterpreter (code : InterpreterCode) (statement : Int) : List StackFrameM :=
  match code with
  | .none => [{ functionName := "top-level scope", file := "", line := 0 }]
  | .method functionName file line edges =>
      ({ functionName, file, line, pc := max (statement + 1) 0 } :: edges).reverse
  | .codeInfo file line edges =>
      ({ functionName := "top-level scope", file, line, pc := max (statement + 1) 0 } :: edges).reverse

def stacktraceFromLookups (lookups : List (List StackFrameM)) (includeC : Bool) : List StackFrameM :=
  lookups.flatten.filter fun frame => includeC || !frame.fromC

def removeThroughLastName (stack : List StackFrameM) (names : List String) : List StackFrameM :=
  (stack.reverse.takeWhile fun frame => !names.contains frame.functionName).reverse

def stacktraceHere (captured : List StackFrameM) (includeC : Bool) : List StackFrameM :=
  let withoutSelf := removeThroughLastName captured ["stacktrace"]
  if includeC then withoutSelf.dropWhile (·.fromC) else withoutSelf

def removeFramesName (stack : List StackFrameM) (name : String) : List StackFrameM :=
  removeThroughLastName stack [name]

def removeFramesNames (stack : List StackFrameM) (names : List String) : List StackFrameM :=
  removeThroughLastName stack names

def removeFramesModule (stack : List StackFrameM) (moduleName : String) : List StackFrameM :=
  stack.filter fun frame => frame.moduleName != some moduleName

def isTopLevelFrame (frame : StackFrameM) (linfoIsCodeInfo : Bool) : Bool :=
  linfoIsCodeInfo || (frame.linfo.isNone && frame.functionName == "top-level scope")

inductive MethodOrModule where | method (name : String) | moduleName (name : String) | none deriving Repr, DecidableEq

def frameMethodOrModule (owner : Option MethodOrModule) : MethodOrModule := owner.getD .none

def frameMethodInstance (linfo : Option String) : Option String := linfo

def frameLocation (debugLocation : Option (String × Int × Int)) (frame : StackFrameM) : String × Int × Int :=
  debugLocation.getD (frame.file, frame.line, if frame.fromC then frame.pc else 0)

inductive SpecLinfoCase where
  | noInfoPointer (hexPointer : String)
  | noInfoTopLevel
  | noInfoFunction (demangled : String)
  | codeInfo
  | moduleFrame (demangled : String)
  | moduleMethodInstance (shown : String)
  | customCodeInstance (shown : String)
  | specializedMethod (shown : String)
  | method (shown : String)
  deriving Repr, DecidableEq

def showSpecLinfo : SpecLinfoCase → String
  | .noInfoPointer pointer => "ip:0x" ++ pointer
  | .noInfoTopLevel | .codeInfo => "top-level scope"
  | .noInfoFunction shown | .moduleFrame shown | .moduleMethodInstance shown |
      .customCodeInstance shown | .specializedMethod shown | .method shown => shown

def showCustomSpecSig (methodName specializedTypes : String) : String :=
  methodName ++ specializedTypes

structure KeywordName where
  raw : String
  withoutDots : String
  isVararg : Bool
  deriving Repr, DecidableEq

structure SpecSignatureInput where
  methodName : String
  positionalSignature : String
  positionalNames : List String
  keywordNames : List KeywordName
  keywordTypes : List String
  limit : Bool
  hasDisplaySize : Bool
  deriving Repr, DecidableEq

def showSpecSig (input : SpecSignatureInput) : String :=
  let names := input.positionalNames.map fun name => if name == "#unused#" then "" else name
  if input.keywordNames.isEmpty then
    input.methodName ++ "(" ++ String.intercalate "," names ++ ")::" ++ input.positionalSignature
  else
    let keywords := (input.keywordNames.zip input.keywordTypes).map fun (name, type) =>
      (if name.isVararg then name.withoutDots else name.raw) ++ "::" ++ type
    input.methodName ++ "(" ++ String.intercalate "," names ++ ";" ++
      String.intercalate "," keywords ++ ")::" ++ input.positionalSignature

def showFrame (signature : String) (location : Option String) (inlined : Bool) : String :=
  signature ++ (match location with | none => "" | some text => " at " ++ text) ++
    (if inlined then " [inlined]" else "")

inductive ParentModuleCase where
  | codeInstanceMethodInstance (moduleName : String)
  | codeInstanceModule (moduleName : String)
  | method (moduleName : String)
  | moduleValue (moduleName : String)
  | unavailable
  deriving Repr, DecidableEq

def parentModule : ParentModuleCase → Option String
  | .codeInstanceMethodInstance name | .codeInstanceModule name |
      .method name | .moduleValue name => some name
  | .unavailable => none

def fromModule (frameModule target : Option String) : Bool := frameModule == target

end JuliaLean.ErrorShow.StacktracesFaithful
