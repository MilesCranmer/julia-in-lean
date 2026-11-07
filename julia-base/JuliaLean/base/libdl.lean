import JuliaLean.base.path
import JuliaLean.Registry.Types
import JuliaLean.base.io

/-!
# Model of `base/libdl.jl`

Typed source-mirrored model at Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`.
Dynamic-loader calls are typed primitives over `base.io.M`, with their ABI
arguments, null pointers, mutable output references and errors explicit. Loader
searching and symbol lookup themselves remain runtime operations. Julia's source
checks and cleanup are mirrored here. Lazy-library references keep identity in the
world; acquire/release atomics and reentrant locks remain distinct typed calls.
Dependencies and callbacks are read when the source reads them, including the
empty-lock synchronization after an already-published handle. Path strings,
callbacks and abstract integer flags retain their own type parameters.
-/

namespace JuliaLean.base.libdl
open JuliaLean
open JuliaLean.base.io (M Error finallyDo)
abbrev I := JInt64
abbrev Cint := JInt .i32
abbrev Flags := JInt .u32
def i (z : Int) : I := JInt.wrap .i64 z

structure LoaderOps (World Handle Path Name PointerRef : Type) where
  null : Handle
  isNull : Handle → Bool
  newNullRef : M World PointerRef
  readRef : PointerRef → M World Handle
  jlDlsym : Handle → Name → PointerRef → I → I → M World Cint
  jlLoadDynamic : Path → Flags → Cint → M World Handle
  jlDlclose : Handle → M World Cint
  jlPathname : Handle → M World Handle
  unsafeString : Handle → M World Path
  free : Handle → M World Unit
  iswindows : Bool

structure LazyOps (World Library Path Callback Lock Dependencies Keywords : Type) (Handle : Type) where
  null : Handle
  isNull : Handle → Bool
  acquireHandle : Library → M World Handle
  plainHandle : Library → M World Handle
  releaseHandle : Library → Handle → M World Unit
  getLock : Library → M World Lock
  lock : Lock → M World Unit
  unlock : Lock → M World Unit
  getDependencies : Library → M World Dependencies
  dependencyValues : Dependencies → M World (List Library)
  pushDependency : Dependencies → Library → M World Unit
  getPath : Library → M World Path
  pathString : Path → M World Path
  getCallback : Library → M World (Option Callback)
  invokeCallback : Callback → M World Unit
  openDependency : Library → Keywords → M World (Option Handle)

def withLazyLock {World Library Path Callback Lock Dependencies Keywords Handle A : Type}
    (ops : LazyOps World Library Path Callback Lock Dependencies Keywords Handle)
    (ll : Library) (body : M World A) : M World A := do
  let lock ← ops.getLock ll
  ops.lock lock
  finallyDo body (ops.unlock lock)

structure IteratorOps (World Collection Element State : Type) where
  iterate : Collection → Option State → M World (Option (Element × State))

/--
Julia source: base/libdl.jl:24-24 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const RTLD_LOCAL     = 0x00000001
```
-/
def rtldLocal : Flags := JInt.wrap .u32 1

/--
Julia source: base/libdl.jl:25-25 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const RTLD_GLOBAL    = 0x00000002
```
-/
def rtldGlobal : Flags := JInt.wrap .u32 2

/--
Julia source: base/libdl.jl:26-26 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const RTLD_LAZY      = 0x00000004
```
-/
def rtldLazy : Flags := JInt.wrap .u32 4

/--
Julia source: base/libdl.jl:27-27 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const RTLD_NOW       = 0x00000008
```
-/
def rtldNow : Flags := JInt.wrap .u32 8

/--
Julia source: base/libdl.jl:28-28 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const RTLD_NODELETE  = 0x00000010
```
-/
def rtldNodelete : Flags := JInt.wrap .u32 16

/--
Julia source: base/libdl.jl:29-29 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const RTLD_NOLOAD    = 0x00000020
```
-/
def rtldNoload : Flags := JInt.wrap .u32 32

/--
Julia source: base/libdl.jl:30-30 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const RTLD_DEEPBIND  = 0x00000040
```
-/
def rtldDeepbind : Flags := JInt.wrap .u32 64

/--
Julia source: base/libdl.jl:31-31 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const RTLD_FIRST     = 0x00000080
```
-/
def rtldFirst : Flags := JInt.wrap .u32 128

/--
Julia source: base/libdl.jl:49-49 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const default_rtld_flags = RTLD_LAZY | RTLD_DEEPBIND
```
-/
def defaultRtldFlags : Flags := JInt.wrap .u32 68

/--
Julia source: base/libdl.jl:59-72 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@constprop :aggressive function dlsym(hnd::Ptr, s::Union{Symbol,AbstractString}; throw_error::Bool = true)
    # Propagate `throw_error=true` to exclude `nothing` from the inferred return type,
    # even when string conversion makes the keyword body too costly to inline.
    hnd == C_NULL && throw(ArgumentError("NULL library handle"))
    val = Ref(Ptr{Cvoid}(0))
    symbol_found = ccall(:jl_dlsym, Cint,
        (Ptr{Cvoid}, Cstring, Ref{Ptr{Cvoid}}, Cint, Cint),
        hnd, s, val, Int64(throw_error), Int64(1)
    )
    if symbol_found == 0 && !throw_error
        return nothing
    end
    return val[]
end
```
-/
def dlsym {World Handle Path Name PointerRef : Type}
    (ops : LoaderOps World Handle Path Name PointerRef) (hnd : Handle) (symbol : Name)
    (throwErr : Bool := true) : M World (Option Handle) := do
  if ops.isNull hnd then throw (.jl (.argumentError "NULL library handle"))
  let val ← ops.newNullRef
  let symbolFound ← ops.jlDlsym hnd symbol val (i (if throwErr then 1 else 0)) (i 1)
  if symbolFound.val == 0 && !throwErr then return none
  pure (some (← ops.readRef val))

/--
Julia source: base/libdl.jl:80-82 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function dlsym_e(args...)
    return something(dlsym(args...; throw_error=false), C_NULL)
end
```
-/
def dlsymE {World Args Handle : Type} (dlsym : Args → Bool → M World (Option Handle))
    (null : Handle) (args : Args) : M World Handle := do
  pure ((← dlsym args false).getD null)

/--
Julia source: base/libdl.jl:118-119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
dlopen(s::Symbol, flags::Integer = default_rtld_flags; kwargs...) =
    dlopen(string(s), flags; kwargs...)
```
-/
def dlopenSymbol {World Symbol Path Integer Keywords Handle : Type}
    (string : Symbol → M World Path)
    (dlopen : Path → Integer → Keywords → M World (Option Handle))
    (defaultFlags : Integer) (symbol : Symbol) (kwargs : Keywords)
    (flags : Integer := defaultFlags) : M World (Option Handle) := do
  dlopen (← string symbol) flags kwargs

/--
Julia source: base/libdl.jl:121-127 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function dlopen(s::AbstractString, flags::Integer = default_rtld_flags; throw_error::Bool = true)
    ret = ccall(:jl_load_dynamic_library, Ptr{Cvoid}, (Cstring,UInt32,Cint), s, flags, Cint(throw_error))
    if !throw_error && ret == C_NULL
        return nothing
    end
    return ret
end
```
-/
def dlopenString {World Handle Path Name PointerRef Integer : Type}
    (ops : LoaderOps World Handle Path Name PointerRef) (convertFlags : Integer → M World Flags)
    (defaultFlags : Integer) (path : Path) (flags : Integer := defaultFlags)
    (throwErr : Bool := true) : M World (Option Handle) := do
  let ret ← ops.jlLoadDynamic path (← convertFlags flags) (JInt.wrap .i32 (if throwErr then 1 else 0))
  if !throwErr && ops.isNull ret then return none
  pure (some ret)

/--
Julia source: base/libdl.jl:146-154 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function dlopen(f::Function, name, args...; kwargs...)
    hdl = nothing
    try
        hdl = dlopen(name, args...; kwargs...)
        f(hdl)
    finally
        dlclose(hdl)
    end
end
```
-/
def dlopenDo {World Name Args Keywords Handle A CloseResult : Type}
    (dlopen : Name → Args → Keywords → M World (Option Handle))
    (dlclose : Option Handle → M World CloseResult) (f : Option Handle → M World A)
    (name : Name) (args : Args) (kwargs : Keywords) : M World A := do
  let mut hdl := none
  let result ← try
      hdl := ← dlopen name args kwargs
      pure (Except.ok (← f hdl))
    catch error => pure (Except.error error)
  let _ ← dlclose hdl
  match result with
  | .ok value => pure value
  | .error error => throw error

/--
Julia source: base/libdl.jl:162-162 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
dlopen_e(args...) = something(dlopen(args...; throw_error=false), C_NULL)
```
-/
def dlopenE {World Args Handle : Type} (dlopen : Args → Bool → M World (Option Handle))
    (null : Handle) (args : Args) : M World Handle := do
  pure ((← dlopen args false).getD null)

/--
Julia source: base/libdl.jl:169-171 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function dlclose(p::Ptr)
    0 == ccall(:jl_dlclose, Cint, (Ptr{Cvoid},), p)
end
```
-/
def dlclose {World Handle : Type} (jlDlclose : Handle → M World Cint)
    (p : Handle) : M World Bool := do pure ((← jlDlclose p).val == 0)

/--
Julia source: base/libdl.jl:189-190 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function dlclose(p::Nothing)
end
```
-/
def dlcloseNothing {World : Type} : M World Unit := pure ()

/--
Julia source: base/libdl.jl:201-218 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function find_library(libnames, extrapaths=String[])
    for lib in libnames
        for path in extrapaths
            l = joinpath(path, lib)
            p = dlopen(l, RTLD_LAZY; throw_error=false)
            if p !== nothing
                dlclose(p)
                return l
            end
        end
        p = dlopen(lib, RTLD_LAZY; throw_error=false)
        if p !== nothing
            dlclose(p)
            return lib
        end
    end
    return ""
end
```
-/
def findLibrary {World Names Paths Path Handle CloseResult NameState PathState : Type}
    (names : IteratorOps World Names Path NameState) (paths : IteratorOps World Paths Path PathState)
    (literal : String → Path) (joinpath : Path → Path → M World Path)
    (dlopen : Path → Flags → Bool → M World (Option Handle))
    (dlclose : Handle → M World CloseResult) (emptyPaths : Paths) (libnames : Names)
    (extrapaths : Paths := emptyPaths) : M World Path :=
  JuliaLean.base.io.whileLoop (fun state => do
    match ← names.iterate libnames state with
    | none => pure (.inl (literal ""))
    | some (lib, next) =>
      let found ← JuliaLean.base.io.whileLoop (fun pathState => do
        match ← paths.iterate extrapaths pathState with
        | none => pure (.inl none)
        | some (path, nextPath) =>
          let l ← joinpath path lib
          if let some p ← dlopen l rtldLazy false then
            let _ ← dlclose p
            pure (.inl (some l))
          else pure (.inr (some nextPath))) none
      match found with
      | some path => pure (.inl path)
      | none =>
        if let some p ← dlopen lib rtldLazy false then
          let _ ← dlclose p
          pure (.inl lib)
        else pure (.inr (some next))) none

/--
Julia source: base/libdl.jl:219-220 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
find_library(libname::Union{Symbol,AbstractString}, extrapaths=String[]) =
    find_library([string(libname)], extrapaths)
```
-/
def findLibrarySingle {World Name Path : Type} (string : Name → M World Path)
    (findLibrary : List Path → List Path → M World Path) (libname : Name)
    (extrapaths : List Path := []) : M World Path := do
  findLibrary [← string libname] extrapaths

/--
Julia source: base/libdl.jl:227-233 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function dlpath(handle::Ptr{Cvoid})
    handle == C_NULL && throw(ArgumentError("NULL library handle"))
    p = ccall(:jl_pathname_for_handle, Cstring, (Ptr{Cvoid},), handle)
    s = unsafe_string(p)
    Sys.iswindows() && Libc.free(p)
    return s
end
```
-/
def dlpathHandle {World Handle Path Name PointerRef : Type}
    (ops : LoaderOps World Handle Path Name PointerRef) (handle : Handle) : M World Path := do
  if ops.isNull handle then throw (.jl (.argumentError "NULL library handle"))
  let p ← ops.jlPathname handle
  let s ← ops.unsafeString p
  if ops.iswindows then ops.free p
  pure s

/--
Julia source: base/libdl.jl:245-250 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function dlpath(libname::Union{AbstractString, Symbol})
    handle = dlopen(libname)
    path = dlpath(handle)
    dlclose(handle)
    return path
end
```
-/
def dlpathName {World Name Handle Path CloseResult : Type}
    (dlopen : Name → M World Handle) (dlpath : Handle → M World Path)
    (dlclose : Handle → M World CloseResult) (libname : Name) : M World Path := do
  let handle ← dlopen libname
  let path ← dlpath handle
  let _ ← dlclose handle
  pure path

/--
Julia source: base/libdl.jl:252-259 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
if Sys.isapple()
    const dlext = "dylib"
elseif Sys.iswindows()
    const dlext = "dll"
else
    #assume Sys.islinux, or similar
    const dlext = "so"
end
```
-/
def dlext (isapple iswindows : Bool) : String :=
  if isapple then "dylib" else if iswindows then "dll" else "so"

/--
Julia source: base/libdl.jl:273-294 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function dllist()
    dynamic_libraries = Vector{String}()

    @static if Sys.isapple()
        numImages = ccall(:_dyld_image_count, Cint, ())

        # start at 1 instead of 0 to skip self
        for i in 1:numImages-1
            name = unsafe_string(ccall(:_dyld_get_image_name, Cstring, (UInt32,), i))
            push!(dynamic_libraries, name)
        end
    elseif Sys.iswindows() || Sys.islinux() || Sys.isbsd()
        # `dl_iterate_phdr` must be handled by C, since otherwise arbitrary Julia
        # code (in finalizers / ccall symbol resolution) may compete for the dynamic
        # linker lock held during its callback
        ccall(:jl_dllist, Cint, (Any,), dynamic_libraries)
    else
        # unimplemented
    end

    return dynamic_libraries
end
```
-/
def dllist {World Handle Path Vector : Type} (newVector : M World Vector)
    (push : Vector → Path → M World Unit) (isapple iswindows islinux isbsd : Bool)
    (dyldImageCount : M World Cint) (dyldGetImageName : Flags → M World Handle)
    (unsafeString : Handle → M World Path) (jlDllist : Vector → M World Cint) : M World Vector := do
  let libraries ← newVector
  if isapple then
    let numImages ← dyldImageCount
    for offset in List.range (max 0 (numImages - JInt.wrap .i32 1).val).toNat do
      let index := JInt.wrap .i32 offset + JInt.wrap .i32 1
      let cindex ← JuliaLean.base.io.liftJl (JInt.convert "convert" .u32 index.val)
      push libraries (← unsafeString (← dyldGetImageName cindex))
  else if iswindows || islinux || isbsd then
    let _ ← jlDllist libraries
  pure libraries

/--
Julia source: base/libdl.jl:315-318 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct LazyLibraryPath
    pieces::Tuple{Vararg{Any}}
    LazyLibraryPath(pieces...) = new(pieces)
end
```
-/
structure LazyLibraryPath (Piece : Type) where
  pieces : List Piece

/--
Julia source: base/libdl.jl:317-317 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    LazyLibraryPath(pieces...) = new(pieces)
```
-/
def lazyLibraryPath {Piece : Type} (pieces : List Piece) : LazyLibraryPath Piece := ⟨pieces⟩

/--
Julia source: base/libdl.jl:319-319 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline Base.string(llp::LazyLibraryPath) = joinpath(String[string(p)::String for p in llp.pieces])
```
-/
def lazyPathString {World Piece Path : Type} (string : Piece → M World Path)
    (joinpath : List Path → M World Path) (llp : LazyLibraryPath Piece) : M World Path := do
  joinpath (← llp.pieces.mapM string)

/--
Julia source: base/libdl.jl:320-320 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.cconvert(::Type{Cstring}, llp::LazyLibraryPath) = Base.cconvert(Cstring, string(llp))
```
-/
def lazyPathCconvert {World Piece Path CString : Type}
    (string : LazyLibraryPath Piece → M World Path) (cconvert : Path → M World CString)
    (llp : LazyLibraryPath Piece) : M World CString := do cconvert (← string llp)

/--
Julia source: base/libdl.jl:322-322 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.print(io::IO, llp::LazyLibraryPath) = print(io, string(llp))
```
-/
def printLazyPath {World Io Piece Path : Type}
    (string : LazyLibraryPath Piece → M World Path) (print : Io → Path → M World Unit)
    (io : Io) (llp : LazyLibraryPath Piece) : M World Unit := do print io (← string llp)

/--
Julia source: base/libdl.jl:325-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct PrivateShlibdirGetter; end
```
-/
structure PrivateShlibdirGetter where

/--
Julia source: base/libdl.jl:326-337 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const private_shlibdir = Base.OncePerProcess{String}() do
    p = ccall(:jl_get_libjulia_internal_path, Cstring, ())
    if p == C_NULL
        # libjulia-internal is linked into the executable, so it cannot tell us
        # where the private libraries live. Assume the installed layout, which
        # keeps them in `$(private_shlibdir)` relative to the executable.
        return Sys.iswindows() ? Sys.BINDIR : abspath(Sys.BINDIR, Base.PRIVATE_LIBDIR)
    end
    path = unsafe_string(p)
    Sys.iswindows() && Libc.free(p)
    return dirname(path)
end
```
-/
def initPrivateShlibdir {World Handle Path : Type} (jlGetInternalPath : M World Handle)
    (isNull : Handle → Bool) (iswindows : Bool) (bindir privateLibdir : Path)
    (abspath : List Path → M World Path) (unsafeString : Handle → M World Path)
    (free : Handle → M World Unit) (dirname : Path → M World Path) : M World Path := do
  let p ← jlGetInternalPath
  if isNull p then
    if iswindows then return bindir else return ← abspath [bindir, privateLibdir]
  let path ← unsafeString p
  if iswindows then free p
  dirname path

/--
Julia source: base/libdl.jl:338-338 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.string(::PrivateShlibdirGetter) = private_shlibdir()
```
-/
def privateShlibdirString {World Path : Type} (privateShlibdir : M World Path)
    (_ : PrivateShlibdirGetter) : M World Path := privateShlibdir

/--
Julia source: base/libdl.jl:356-356 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
BundledLazyLibraryPath(subpath) = LazyLibraryPath(PrivateShlibdirGetter(), subpath)
```
-/
def bundledLazyLibraryPath {Piece : Type} (ofGetter : PrivateShlibdirGetter → Piece)
    (subpath : Piece) : LazyLibraryPath Piece := lazyLibraryPath [ofGetter ⟨⟩, subpath]

/--
Julia source: base/libdl.jl:358-369 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.show(io::IO, llp::LazyLibraryPath)
    pieces = llp.pieces
    # `PrivateShlibdirGetter()` dlopens. Avoid doing so in `show`.
    # Like `Library`, avoids printing the full path when bundled.
    if length(pieces) == 2 && pieces[1] isa PrivateShlibdirGetter
        show(io, pieces[2])
    else
        print(io, "LazyLibraryPath(")
        join(io, (sprint(show, p) for p in pieces), ", ")
        print(io, ")")
    end
end
```
-/
def showLazyPath {World Io Piece Text : Type}
    (isGetter : Piece → Bool) (showValue : Io → Piece → M World Unit)
    (print : Io → String → M World Unit) (sprintShow : Piece → M World Text)
    (join : Io → List (M World Text) → String → M World Unit) (io : Io) (llp : LazyLibraryPath Piece) : M World Unit := do
  let pieces := llp.pieces
  match pieces with
  | [first, second] =>
    if isGetter first then showValue io second
    else
      print io "LazyLibraryPath("
      join io (pieces.map sprintShow) ", "
      print io ")"
  | _ =>
    print io "LazyLibraryPath("
    join io (pieces.map sprintShow) ", "
    print io ")"

/--
Julia source: base/libdl.jl:393-395 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct InitialDependencies{T}
    dependencies::Vector{T}
end
```
-/
structure InitialDependencies (Vector : Type) where
  dependencies : Vector

/--
Julia source: base/libdl.jl:396-396 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(init::InitialDependencies)() = copy(init.dependencies)
```
-/
def initialDependenciesCall {World Vector : Type} (copy : Vector → M World Vector)
    (init : InitialDependencies Vector) : M World Vector := copy init.dependencies

/--
Julia source: base/libdl.jl:446-477 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mutable struct LazyLibrary
    # Name and flags to open with
    const path
    const flags::UInt32

    # Dependencies that must be loaded before we can load
    #
    # The OncePerProcess is introduced here so that any registered dependencies are
    # always ephemeral to a given process (instead of, e.g., persisting depending
    # on whether they were added in the process where this LazyLibrary was created)
    dependencies::Base.OncePerProcess{Vector{LazyLibrary}, InitialDependencies{LazyLibrary}}

    # Function that get called once upon initial load
    on_load_callback
    const lock::Base.ReentrantLock

    # Pointer that we eventually fill out upon first `dlopen()`
    @atomic handle::Ptr{Cvoid}
    function LazyLibrary(path; flags = default_rtld_flags, dependencies = LazyLibrary[],
                         on_load_callback = nothing)
        return new(
            path,
            UInt32(flags),
            Base.OncePerProcess{Vector{LazyLibrary}}(
                InitialDependencies{LazyLibrary}(dependencies)
            ),
            on_load_callback,
            Base.ReentrantLock(),
            C_NULL,
        )
    end
end
```
-/
structure LazyLibrary (Path Once Callback Lock Handle : Type) where
  path : Path
  flags : Flags
  dependencies : Once
  on_load_callback : Option Callback
  lock : Lock
  handle : Handle

/--
Julia source: base/libdl.jl:464-476 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function LazyLibrary(path; flags = default_rtld_flags, dependencies = LazyLibrary[],
                         on_load_callback = nothing)
        return new(
            path,
            UInt32(flags),
            Base.OncePerProcess{Vector{LazyLibrary}}(
                InitialDependencies{LazyLibrary}(dependencies)
            ),
            on_load_callback,
            Base.ReentrantLock(),
            C_NULL,
        )
    end
```
-/
def newLazyLibrary {World Path Vector Once Callback Lock Handle Integer : Type}
    (convertFlags : Integer → M World Flags)
    (oncePerProcess : InitialDependencies Vector → M World Once)
    (newLock : M World Lock) (null : Handle) (defaultFlags : Integer)
    (emptyDependencies : M World Vector) (path : Path)
    (flags : Integer := defaultFlags) (dependencies : Option Vector := none)
    (onLoadCallback : Option Callback := none) : M World (LazyLibrary Path Once Callback Lock Handle) := do
  let dependencies ← match dependencies with | some deps => pure deps | none => emptyDependencies
  let flags ← convertFlags flags
  let once ← oncePerProcess ⟨dependencies⟩
  let lock ← newLock
  pure ⟨path, flags, once, onLoadCallback, lock, null⟩

/--
Julia source: base/libdl.jl:480-480 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline _invoke_on_load_callback(@nospecialize(cb)) = cb()
```
-/
def invokeOnLoadCallback {World Callback : Type} (invoke : Callback → M World Unit)
    (cb : Callback) : M World Unit := invoke cb

/--
Julia source: base/libdl.jl:481-481 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline _lazy_library_path_string(@nospecialize(path)) = string(path)
```
-/
def lazyLibraryPathString {World Path Str : Type} (string : Path → M World Str)
    (path : Path) : M World Str := string path

/--
Julia source: base/libdl.jl:484-488 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.show(io::IO, ll::LazyLibrary)
    print(io, "LazyLibrary(")
    show(io, ll.path)
    print(io, ")")
end
```
-/
def showLazyLibrary {World Io Library Path : Type} (getPath : Library → M World Path)
    (print : Io → String → M World Unit) (showValue : Io → Path → M World Unit)
    (io : Io) (ll : Library) : M World Unit := do
  print io "LazyLibrary("
  showValue io (← getPath ll)
  print io ")"

/--
Julia source: base/libdl.jl:509-513 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function add_dependency!(ll::LazyLibrary, dep::LazyLibrary)
    @lock ll.lock begin
        push!(ll.dependencies(), dep)
    end
end
```
-/
def addDependency {World Library Path Callback Lock Dependencies Keywords Handle : Type}
    (ops : LazyOps World Library Path Callback Lock Dependencies Keywords Handle)
    (ll dep : Library) : M World Dependencies :=
  withLazyLock ops ll do
    let deps ← ops.getDependencies ll
    ops.pushDependency deps dep
    pure deps

/--
Julia source: base/libdl.jl:519-558 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function dlopen(ll::LazyLibrary, flags::Integer = ll.flags; kwargs...)
    handle = @atomic :acquire ll.handle
    if handle == C_NULL
        @lock ll.lock begin
            # Check to see if another thread has already run this
            if ll.handle == C_NULL
                # Ensure that all dependencies are loaded
                for dep in ll.dependencies()
                    dlopen(dep; kwargs...)
                end

                # Load our library
                handle = dlopen(_lazy_library_path_string(ll.path), flags; kwargs...)
                @atomic :release ll.handle = handle

                # Only the thread that loaded the library calls the `on_load_callback()`.
                if ll.on_load_callback !== nothing
                    _invoke_on_load_callback(ll.on_load_callback)
                end
            else
                # Another thread loaded the library while we were waiting
                handle = @atomic :acquire ll.handle
            end
        end
    else
        # Invoke our on load callback, if it exists
        if ll.on_load_callback !== nothing
            # This empty lock protects against the case where we have updated
            # `ll.handle` in the branch above, but not exited the lock.  We want
            # a second thread that comes in at just the wrong time to have to wait
            # for that lock to be released (and thus for the on_load_callback to
            # have finished), hence the empty lock here. But we want the
            # on_load_callback thread to bypass this, which will be happen thanks
            # to the fact that we're using a reentrant lock here.
            @lock ll.lock begin end
        end
    end

    return handle
end
```
-/
def dlopenLazy {World Library Path Callback Lock Dependencies Keywords Handle Integer : Type}
    (ops : LazyOps World Library Path Callback Lock Dependencies Keywords Handle)
    (getFlags : Library → M World Integer)
    (dlopen : Path → Integer → Keywords → M World (Option Handle))
    (ll : Library) (kwargs : Keywords) (flags : Option Integer := none) : M World Handle := do
  let flags ← match flags with | some flags => pure flags | none => getFlags ll
  let handle ← ops.acquireHandle ll
  if ops.isNull handle then
    withLazyLock ops ll do
      if ops.isNull (← ops.plainHandle ll) then
        for dep in ← ops.dependencyValues (← ops.getDependencies ll) do
          let _ ← ops.openDependency dep kwargs
        let loaded ← dlopen (← ops.pathString (← ops.getPath ll)) flags kwargs
        let handle ← match loaded with
          | some handle => pure handle
          | none => throw (.foreignError "TypeError" "expected Ptr{Cvoid} for atomic handle")
        ops.releaseHandle ll handle
        if (← ops.getCallback ll).isSome then
          match ← ops.getCallback ll with
          | some callback => ops.invokeCallback callback
          | none => throw (.jl (.methodError "Nothing"))
        pure handle
      else ops.acquireHandle ll
  else
    if (← ops.getCallback ll).isSome then withLazyLock ops ll (pure ())
    pure handle

/--
Julia source: base/libdl.jl:559-559 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
dlopen(x::Any) = throw(TypeError(:dlopen, "", Union{Symbol,String,LazyLibrary}, x))
```
-/
def dlopenAny {World Value : Type} (_x : Value) : M World Empty :=
  throw (.foreignError "TypeError" "dlopen expected Symbol, String or LazyLibrary")

/--
Julia source: base/libdl.jl:560-560 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
dlsym(ll::LazyLibrary, args...; kwargs...) = dlsym(dlopen(ll), args...; kwargs...)
```
-/
def dlsymLazy {World Library Handle Args Keywords Result : Type}
    (dlopen : Library → M World Handle) (dlsym : Handle → Args → Keywords → M World Result)
    (ll : Library) (args : Args) (kwargs : Keywords) : M World Result := do
  dlsym (← dlopen ll) args kwargs

/--
Julia source: base/libdl.jl:561-561 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
dlpath(ll::LazyLibrary) = dlpath(dlopen(ll))
```
-/
def dlpathLazy {World Library Handle Path : Type} (dlopen : Library → M World Handle)
    (dlpath : Handle → M World Path) (ll : Library) : M World Path := do dlpath (← dlopen ll)


/-! ## Source context (documentation, imports and declarations) -/
-- Source: base/libdl.jl:1-23 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- module Libdl
-- @doc """
-- Interface to libdl. Provides dynamic linking support.
-- """ Libdl
-- 
-- import Base: DL_LOAD_PATH, isdebugbuild
-- 
-- export DL_LOAD_PATH, RTLD_DEEPBIND, RTLD_FIRST, RTLD_GLOBAL, RTLD_LAZY, RTLD_LOCAL,
--     RTLD_NODELETE, RTLD_NOLOAD, RTLD_NOW, dlclose, dlopen, dlopen_e, dlsym, dlsym_e,
--     dlpath, find_library, dlext, dllist, LazyLibrary, LazyLibraryPath, BundledLazyLibraryPath
-- 
-- """
--     DL_LOAD_PATH
-- 
-- When calling [`dlopen`](@ref), the paths in this list will be searched first, in
-- order, before searching the system locations for a valid library handle.
-- """
-- DL_LOAD_PATH
-- 
-- # note: constants to match JL_RTLD_* in src/julia.h, translated
-- #       to system-specific values by JL_RTLD macro in src/dlload.c
-- /Source

-- Source: base/libdl.jl:32-48 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     RTLD_DEEPBIND
--     RTLD_FIRST
--     RTLD_GLOBAL
--     RTLD_LAZY
--     RTLD_LOCAL
--     RTLD_NODELETE
--     RTLD_NOLOAD
--     RTLD_NOW
-- 
-- Enum constant for [`dlopen`](@ref). See your platform man page for details, if
-- applicable.
-- """
-- (RTLD_DEEPBIND, RTLD_FIRST, RTLD_GLOBAL, RTLD_LAZY, RTLD_LOCAL, RTLD_NODELETE, RTLD_NOLOAD, RTLD_NOW)
-- 
-- # The default flags for `dlopen()`
-- /Source

-- Source: base/libdl.jl:50-58 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     dlsym(handle, sym; throw_error::Bool = true)
-- 
-- Look up a symbol from a shared library handle, return callable function pointer on success.
-- 
-- If the symbol cannot be found, this method throws an error, unless the keyword argument
-- `throw_error` is set to `false`, in which case this method returns `nothing`.
-- """
-- /Source

-- Source: base/libdl.jl:73-79 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     dlsym_e(handle, sym)
-- 
-- Look up a symbol from a shared library handle, silently return `C_NULL` on lookup failure.
-- This method is now deprecated in favor of `dlsym(handle, sym; throw_error=false)`.
-- """
-- /Source

-- Source: base/libdl.jl:83-117 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     dlopen(libfile::AbstractString [, flags::Integer]; throw_error:Bool = true)
-- 
-- Load a shared library, returning an opaque handle.
-- 
-- The extension given by the constant `dlext` (`.so`, `.dll`, or `.dylib`)
-- can be omitted from the `libfile` string, as it is automatically appended
-- if needed.   If `libfile` is not an absolute path name, then the paths
-- in the array `DL_LOAD_PATH` are searched for `libfile`, followed by the
-- system load path.
-- 
-- The optional flags argument is a bitwise-or of zero or more of `RTLD_LOCAL`, `RTLD_GLOBAL`,
-- `RTLD_LAZY`, `RTLD_NOW`, `RTLD_NODELETE`, `RTLD_NOLOAD`, `RTLD_DEEPBIND`, and `RTLD_FIRST`.
-- These are converted to the corresponding flags of the POSIX (and/or GNU libc and/or MacOS)
-- dlopen command, if possible, or are ignored if the specified functionality is not available
-- on the current platform. The default flags are platform specific. On MacOS the default
-- `dlopen` flags are `RTLD_LAZY|RTLD_DEEPBIND|RTLD_GLOBAL` while on other platforms the
-- defaults are `RTLD_LAZY|RTLD_DEEPBIND|RTLD_LOCAL`. An important usage of these flags is to
-- specify non default behavior for when the dynamic library loader binds library references to
-- exported symbols and if the bound references are put into process local or global scope. For
-- instance `RTLD_LAZY|RTLD_DEEPBIND|RTLD_GLOBAL` allows the library's symbols to be available
-- for usage in other shared libraries, addressing situations where there are dependencies
-- between shared libraries.
-- 
-- If the library cannot be found, this method throws an error, unless the keyword argument
-- `throw_error` is set to `false`, in which case this method returns `nothing`.
-- 
-- !!! note
--      From Julia 1.6 on, this method replaces paths starting with `@executable_path/` with
--      the path to the Julia executable, allowing for relocatable relative-path loads. In
--      Julia 1.5 and earlier, this only worked on macOS.
-- """
-- function dlopen end
-- 
-- /Source

-- Source: base/libdl.jl:120-120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/libdl.jl:128-145 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     dlopen(f::Function, args...; kwargs...)
-- 
-- Wrapper for usage with `do` blocks to automatically close the dynamic library once
-- control flow leaves the `do` block scope.
-- 
-- # Examples
-- ```julia
-- vendor = dlopen("libblas") do lib
--     if Libdl.dlsym(lib, :openblas_set_num_threads; throw_error=false) !== nothing
--         return :openblas
--     else
--         return :other
--     end
-- end
-- ```
-- """
-- /Source

-- Source: base/libdl.jl:155-161 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     dlopen_e(libfile::AbstractString [, flags::Integer])
-- 
-- Similar to [`dlopen`](@ref), except returns `C_NULL` instead of raising errors.
-- This method is now deprecated in favor of `dlopen(libfile::AbstractString [, flags::Integer]; throw_error=false)`.
-- """
-- /Source

-- Source: base/libdl.jl:163-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     dlclose(handle)
-- 
-- Close shared library referenced by handle.
-- """
-- /Source

-- Source: base/libdl.jl:172-188 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     dlclose(::Nothing)
-- 
-- For the very common usage pattern of
-- 
--     try
--         hdl = dlopen(library_name)
--         ... do something
--     finally
--         dlclose(hdl)
--     end
-- 
-- We define a `dlclose()` method that accepts a parameter of type `Nothing`, so
-- that user code does not have to change its behavior for the case that `library_name`
-- was not found.
-- """
-- /Source

-- Source: base/libdl.jl:191-200 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     find_library(names [, locations])
-- 
-- Searches for the first library in `names` in the paths in the `locations` list,
-- `DL_LOAD_PATH`, or system library paths (in that order) which can successfully be dlopen'd.
-- On success, the return value will be one of the names (potentially prefixed by one of the
-- paths in locations). This string can be assigned to a `global const` and used as the library
-- name in future `ccall`'s. On failure, it returns the empty string.
-- """
-- /Source

-- Source: base/libdl.jl:221-226 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     dlpath(handle::Ptr{Cvoid})
-- 
-- Given a library `handle` from `dlopen`, return the full path.
-- """
-- /Source

-- Source: base/libdl.jl:234-244 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     dlpath(libname::Union{AbstractString, Symbol})
-- 
-- Get the full path of the library `libname`.
-- 
-- # Examples
-- ```julia-repl
-- julia> dlpath("libjulia")
-- ```
-- """
-- /Source

-- Source: base/libdl.jl:251-251 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/libdl.jl:260-272 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     dlext
-- 
-- File extension for dynamic libraries (e.g. dll, dylib, so) on the current platform.
-- """
-- dlext
-- 
-- """
--     dllist()
-- 
-- Return the paths of dynamic libraries currently loaded in a `Vector{String}`.
-- """
-- /Source

-- Source: base/libdl.jl:295-314 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- 
-- """
--     LazyLibraryPath(path_pieces...)
-- 
-- Helper type for lazily constructed library paths for use with [`LazyLibrary`](@ref).
-- Path pieces are stored unevaluated and joined with `joinpath()` when the library is first
-- accessed. Arguments must be able to have `string()` called on them.
-- 
-- !!! compat "Julia 1.11"
--     `LazyLibraryPath` was added in Julia 1.11.
-- 
-- See also [`LazyLibrary`](@ref), [`BundledLazyLibraryPath`](@ref).
-- 
-- # Examples
-- 
-- ```julia
-- const mylib = LazyLibrary(LazyLibraryPath(artifact_dir, "lib", "libmylib.so.1.2.3"))
-- ```
-- """
-- /Source

-- Source: base/libdl.jl:321-321 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # Define `print` so that we can wrap this in a `LazyString`
-- /Source

-- Source: base/libdl.jl:323-324 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Helper to get `$(private_shlibdir)` at runtime
-- /Source

-- Source: base/libdl.jl:339-355 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     BundledLazyLibraryPath(subpath)
-- 
-- Helper type for lazily constructed library paths within the Julia distribution.
-- Constructs paths relative to Julia's private shared library directory.
-- 
-- Primarily used by Julia's standard library. For example:
-- ```julia
-- const libgmp = LazyLibrary(BundledLazyLibraryPath("libgmp.so.10"))
-- ```
-- 
-- !!! compat "Julia 1.11"
--     `BundledLazyLibraryPath` was added in Julia 1.11.
-- 
-- See also [`LazyLibrary`](@ref), [`LazyLibraryPath`](@ref).
-- """
-- /Source

-- Source: base/libdl.jl:357-357 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/libdl.jl:370-392 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     LazyLibraryCallback
-- 
-- Abstract supertype for `on_load_callback`s of a [`LazyLibrary`](@ref) that are usable
-- under `--trim`. Subtypes must be concrete and callable with no arguments:
-- 
-- ```julia
-- struct MyLibOnLoad <: Libdl.LazyLibraryCallback end
-- (::MyLibOnLoad)() = @ccall mylib.mylib_init()::Cvoid
-- 
-- const mylib = LazyLibrary("libmylib"; on_load_callback = MyLibOnLoad())
-- ```
-- 
-- Such Methods will be compiled unconditionally under `--trim`, even if the
-- type is never instantiated or called.
-- 
-- !!! compat "Julia 1.14"
--     `LazyLibraryCallback` was added in Julia 1.14.
-- """
-- const LazyLibraryCallback = Core.LazyLibraryCallback
-- 
-- # Small helper struct to initialize a LazyLibrary with its initial set of dependencies
-- /Source

-- Source: base/libdl.jl:397-445 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     LazyLibrary(name; flags = <default dlopen flags>,
--                 dependencies = LazyLibrary[], on_load_callback = nothing)
-- 
-- Represents a lazily-loaded shared library that delays loading itself and its dependencies
-- until first use in a `ccall()`, `@ccall`, `dlopen()`, `dlsym()`, `dlpath()`, or `cglobal()`.
-- This is a thread-safe mechanism for on-demand library initialization.
-- 
-- # Arguments
-- 
-- - `name`: Library name (or lazy path computation) as a `String`,
--   [`LazyLibraryPath`](@ref), or [`BundledLazyLibraryPath`](@ref).
-- - `flags`: Optional `dlopen` flags (default: `RTLD_LAZY | RTLD_DEEPBIND`). See [`dlopen`](@ref).
-- - `dependencies`: Vector of `LazyLibrary` object references to load before this one.
-- - `on_load_callback`: Optional function to run arbitrary code on first load (use sparingly,
--   as it is not expected that `ccall()` should result in large amounts of Julia code being run.
--   You may call `ccall()` from within the `on_load_callback` but only for the current library
--   and its dependencies, and user should not call `wait()` on any tasks within the on load
--   callback as they may deadlock). To be usable under `--trim`, this must be a
--   [`LazyLibraryCallback`](@ref Libdl.LazyLibraryCallback).
-- 
-- The dlopen operation is thread-safe: only one thread loads the library, acquired after the
-- release store of the reference to each dependency from loading of each dependency. Other
-- tasks block until loading completes. The handle is then cached and reused for all subsequent
-- calls (there is no dlclose for lazy library and dlclose should not be called on the returned handle).
-- 
-- !!! compat "Julia 1.11"
--     `LazyLibrary` was added in Julia 1.11.
-- 
-- See also [`LazyLibraryPath`](@ref), [`BundledLazyLibraryPath`](@ref), [`dlopen`](@ref),
-- [`dlsym`](@ref), [`add_dependency!`](@ref).
-- 
-- # Examples
-- 
-- ```julia
-- # Basic usage
-- const mylib = LazyLibrary("libmylib")
-- @ccall mylib.myfunc(42::Cint)::Cint
-- 
-- # With dependencies
-- const libfoo = LazyLibrary("libfoo")
-- const libbar = LazyLibrary("libbar"; dependencies=[libfoo])
-- ```
-- 
-- For more examples including platform-specific libraries, lazy path construction, and
-- migration from `__init__()` patterns, see the manual section on
-- [Using LazyLibrary for Lazy Loading](@ref man-lazylibrary).
-- """
-- /Source

-- Source: base/libdl.jl:478-479 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # overrides for JuliaC under `--trim`
-- /Source

-- Source: base/libdl.jl:482-483 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Only print the path and avoid printing all the dependencies
-- /Source

-- Source: base/libdl.jl:489-508 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # We support adding dependencies only because of very special situations
-- # such as LBT needing to have OpenBLAS_jll added as a dependency dynamically.
-- """
--     add_dependency!(library::LazyLibrary, dependency::LazyLibrary)
-- 
-- Dynamically add a dependency that must be loaded before `library`. Only needed when
-- dependencies cannot be determined at construction time.
-- 
-- !!! warning
--     Dependencies added with this function are **ephemeral** and only persist within the
--     current process. They will not persist across precompilation boundaries.
-- 
-- Prefer specifying dependencies in the `LazyLibrary` constructor when possible.
-- 
-- !!! compat "Julia 1.11"
--     `add_dependency!` was added in Julia 1.11.
-- 
-- See also [`LazyLibrary`](@ref).
-- """
-- /Source

-- Source: base/libdl.jl:514-518 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Register `jl_libdl_dlopen_func` so that `ccall()` lowering knows
-- # how to call `dlopen()`.
-- Base.unsafe_store!(cglobal(:jl_libdl_dlopen_func, Any), dlopen)
-- 
-- /Source

-- Source: base/libdl.jl:562-562 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- end # module Libdl
-- /Source


/--
Julia source: base/libdl.jl:517-517 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.unsafe_store!(cglobal(:jl_libdl_dlopen_func, Any), dlopen)
```
-/
def registerDlopen {World Pointer Function : Type} (cglobal : M World Pointer)
    (unsafeStore : Pointer → Function → M World Unit) (dlopen : Function) : M World Unit := do
  unsafeStore (← cglobal) dlopen

end JuliaLean.base.libdl

section

set_option linter.unusedSimpArgs false
namespace JuliaLean.IOCov.Libdl

open JuliaLean JuliaLean.IOCov

/-- Result of a Julia `dlopen`/`dlsym`: `none` is `nothing`, `some p` a pointer. -/
abbrev Handle := Option Nat

/-! ## `dlsym`, lines 59-82 -/

/-- `dlsym(hnd, s; throw_error)`, `base/libdl.jl:59-72`. `jlDlsym h s throw` returns
`(found, value)`, or throws itself when `throw` is set and the symbol is missing. -/
def dlsym (jlDlsym : Nat → String → Bool → R (Bool × Nat)) (hnd : Nat) (s : String)
    («throwError» : Bool) : R Handle := do
  if hnd == 0 then argErr "NULL library handle" else
  let (found, val) ← jlDlsym hnd s «throwError»
  if !found && !«throwError» then pure none else pure (some val)

/-- `dlsym_e(args...) = something(dlsym(args...; throw_error=false), C_NULL)`, lines 80-82. -/
def dlsymE (jlDlsym : Nat → String → Bool → R (Bool × Nat)) (hnd : Nat) (s : String) : R Nat := do
  let r ← dlsym jlDlsym hnd s false
  pure (r.getD 0)

/-! ## `dlopen`, `dlclose`, lines 116-190 -/

/-- `dlopen(s::AbstractString, flags; throw_error)`, `base/libdl.jl:121-127`: `flags` is
converted to `UInt32`; `load s flags throw` is `jl_load_dynamic_library`, which throws
itself when `throw` is set. -/
def dlopenStr (load : String → Nat → Bool → R Nat) (s : String) (flags : Int) («throwError» : Bool) :
    R Handle := do
  let f ← toInt .u32 flags
  let ret ← load s f.toNat «throwError»
  if !«throwError» && ret == 0 then pure none else pure (some ret)

/-- `dlopen(s::Symbol, flags; kwargs...) = dlopen(string(s), flags; kwargs...)`, lines 118-119. -/
def dlopenSym (load : String → Nat → Bool → R Nat) (s : String) (flags : Int) («throwError» : Bool) :
    R Handle := dlopenStr load s flags «throwError»

/-- `dlclose(p::Ptr) = 0 == jl_dlclose(p)`, lines 169-171; `dlclose(::Nothing)` returns
`nothing`, lines 189-190 (`none`). -/
def dlclose (jlDlclose : Nat → Int) : Handle → Option Bool
  | none => none
  | some p => some (0 == jlDlclose p)

/-- `dlopen(f::Function, name, args...)`, lines 146-154: opens, applies `f`, and always
calls `dlclose` on the handle (still `nothing` when `dlopen` threw). Returns the result and
the handle given to `dlclose`. -/
def dlopenDo {α} (open_ : R Handle) (f : Handle → R α) : R α × Handle :=
  match open_ with
  | .error e => (.error e, none)
  | .ok h => (f h, h)

/-- `dlopen_e(args...) = something(dlopen(args...; throw_error=false), C_NULL)`, line 162. -/
def dlopenE (load : String → Nat → Bool → R Nat) (s : String) (flags : Int) : R Nat := do
  let r ← dlopenStr load s flags false
  pure (r.getD 0)

/-! ## `find_library`, lines 201-220 -/

/-- `find_library(libnames, extrapaths)`, `base/libdl.jl:201-218`: for each name, try
`joinpath(path, lib)` for each extra path, then `lib`; the first one `dlopen(...;
throw_error=false)` opens is closed and returned; `""` otherwise. `canOpen` is whether
`dlopen` returns a handle. -/
def findLibrary (canOpen : List Char → Bool) (join : List Char → List Char → List Char) :
    List (List Char) → List (List Char) → List Char
  | [], _ => []
  | lib :: libs, extrapaths =>
    match extrapaths.find? (fun path => canOpen (join path lib)) with
    | some path => join path lib
    | none => if canOpen lib then lib else findLibrary canOpen join libs extrapaths

/-- `find_library(libname, extrapaths) = find_library([string(libname)], extrapaths)`, line 219-220. -/
def findLibrary1 (canOpen : List Char → Bool) (join : List Char → List Char → List Char)
    (lib : List Char) (extrapaths : List (List Char)) : List Char :=
  findLibrary canOpen join [lib] extrapaths

/-! ## `dlpath`, `dllist`, lines 227-294 -/

/-- `dlpath(handle::Ptr{Cvoid})`, lines 227-233. -/
def dlpathHandle (pathname : Nat → List UInt8) (handle : Nat) : R (List UInt8) :=
  if handle == 0 then argErr "NULL library handle" else .ok (pathname handle)

/-- `dlpath(libname)`, lines 245-250: `dlopen` (throwing), `dlpath`, `dlclose`. -/
def dlpathName (load : String → Nat → Bool → R Nat) (pathname : Nat → List UInt8)
    (defaultFlags : Int) (libname : String) : R (List UInt8) := do
  let h ← dlopenStr load libname defaultFlags true
  dlpathHandle pathname (h.getD 0)

/-- `dllist()`, lines 273-294 (Linux): the vector `jl_dllist` fills. -/
def dllist (jlDllist : Unit → List (List UInt8)) : List (List UInt8) := jlDllist ()

/-! ## `LazyLibraryPath`, lines 317-369 -/

/-- One path piece: a string, or `PrivateShlibdirGetter()`. -/
inductive Piece where
  | str (s : List Char)
  | shlibdir
  deriving DecidableEq, Repr

/-- `string(p)` of a piece; `string(::PrivateShlibdirGetter) = private_shlibdir()`, line 338. -/
def Piece.string (shlibdir : List Char) : Piece → List Char
  | .str s => s
  | .shlibdir => shlibdir

/-- `LazyLibraryPath(pieces...)`, line 317: stores the pieces. -/
def lazyLibraryPath (pieces : List Piece) : List Piece := pieces

/-- `string(llp) = joinpath(String[string(p) for p in llp.pieces])`, line 319, with the
Unix `joinpath` of `JuliaLean.Paths`. -/
def llpString (shlibdir : List Char) (llp : List Piece) : Jl (List Char) :=
  Paths.joinpath (llp.map (Piece.string shlibdir))

/-- `cconvert(Cstring, llp)`, line 320: the string, rejected if it contains NUL. -/
def llpCconvert (shlibdir : List Char) (llp : List Piece) : R (List Char) :=
  match llpString shlibdir llp with
  | .error e => .error (.jl e)
  | .ok s => if '\x00' ∈ s then argErr "embedded NULs are not allowed in C strings" else .ok s

/-- `print(io, llp) = print(io, string(llp))`, line 322. -/
def llpPrint (shlibdir : List Char) (llp : List Piece) : Jl (List Char) := llpString shlibdir llp

/-- `BundledLazyLibraryPath(subpath)`, line 356. -/
def bundled (subpath : List Char) : List Piece := lazyLibraryPath [.shlibdir, .str subpath]

/-- `show(io, llp)`, lines 358-369, with `showStr` the `show` of a string piece and
`"Base.Libc.Libdl.PrivateShlibdirGetter()"` that of the getter. -/
def llpShow (showStr : List Char → List Char) (llp : List Piece) : List Char :=
  let showP : Piece → List Char := fun
    | .str s => showStr s
    | .shlibdir => "Base.Libc.Libdl.PrivateShlibdirGetter()".toList
  match llp with
  | [.shlibdir, p] => showP p
  | _ => "LazyLibraryPath(".toList ++ List.intercalate ", ".toList (llp.map showP) ++ [')']

/-! ## `LazyLibrary`, lines 396-561 -/

/-- `(init::InitialDependencies)() = copy(init.dependencies)`, line 396. -/
def initialDependencies {α} (deps : List α) : List α := deps

/-- The state of a `LazyLibrary`. -/
structure LazyLib where
  path : List Piece
  flags : Nat
  deps : List Nat
  hasCallback : Bool
  handle : Nat
  deriving DecidableEq, Repr

/-- `LazyLibrary(path; flags, dependencies, on_load_callback)`, lines 464-476:
`UInt32(flags)`, `handle = C_NULL`. -/
def lazyLibrary (path : List Piece) (flags : Int) (deps : List Nat) (hasCallback : Bool) : R LazyLib := do
  let f ← toInt .u32 flags
  pure ⟨path, f.toNat, initialDependencies deps, hasCallback, 0⟩

/-- `_invoke_on_load_callback(cb) = cb()`, line 480. -/
def invokeOnLoadCallback {α} (cb : Unit → α) : α := cb ()
/-- `_lazy_library_path_string(path) = string(path)`, line 481. -/
def lazyLibraryPathString (shlibdir : List Char) (p : List Piece) : Jl (List Char) := llpString shlibdir p

/-- `show(io, ll)`, lines 484-488. -/
def showLazyLibrary (showPath : List Piece → List Char) (ll : LazyLib) : List Char :=
  "LazyLibrary(".toList ++ showPath ll.path ++ [')']

/-- `add_dependency!(ll, dep)`, lines 509-513. -/
def addDependency (ll : LazyLib) (dep : Nat) : LazyLib := { ll with deps := ll.deps ++ [dep] }

/-- The outcome of `dlopen(ll)`: the result, the new state, and how many times the
load callback ran. -/
structure LoadOutcome where
  result : R Handle
  ll : LazyLib
  callbacks : Nat

/-- `dlopen(ll::LazyLibrary, flags = ll.flags; kwargs...)`, lines 519-558, with
`openDeps` the result of opening every dependency (same keywords) and `openPath` the
`dlopen(string(path), flags; kwargs...)` result. Storing `nothing` into the
`handle::Ptr{Cvoid}` field throws (`convert` has no method). -/
def dlopenLL (openDeps : R Unit) (openPath : R Handle) (ll : LazyLib) : LoadOutcome :=
  if ll.handle == 0 then
    match openDeps with
    | .error e => ⟨.error e, ll, 0⟩
    | .ok () =>
      match openPath with
      | .error e => ⟨.error e, ll, 0⟩
      | .ok none => ⟨.error (.methodError "convert"), ll, 0⟩
      | .ok (some h) => ⟨.ok (some h), { ll with handle := h }, if ll.hasCallback then 1 else 0⟩
  else ⟨.ok (some ll.handle), ll, 0⟩

/-- `dlopen(x::Any)`, line 559. -/
def dlopenAny : R Nat := .error (.typeError "dlopen")
/-- `dlsym(ll, args...) = dlsym(dlopen(ll), args...)`, line 560. -/
def dlsymLL (jlDlsym : Nat → String → Bool → R (Bool × Nat)) (o : LoadOutcome) (s : String)
    («throwError» : Bool) : R Handle := do
  let h ← o.result
  dlsym jlDlsym (h.getD 0) s «throwError»
/-- `dlpath(ll) = dlpath(dlopen(ll))`, line 561. -/
def dlpathLL (pathname : Nat → List UInt8) (o : LoadOutcome) : R (List UInt8) := do
  let h ← o.result
  dlpathHandle pathname (h.getD 0)
end JuliaLean.IOCov.Libdl
end

section
namespace JuliaLean.IOCov.LibdlFaithful

open JuliaLean JuliaLean.Registry JuliaLean.IOCov

inductive Name where
  | symbol (value : String)
  | string (value : String)
  deriving DecidableEq, Repr

def Name.toString : Name -> String
  | .symbol s | .string s => s

/-! Basic dl operations. -/

/-- `dlsym`, `base/libdl.jl:59-72`. The primitive result contains
`symbol_found` and the value written through `Ref{Ptr{Cvoid}}`. -/
def dlsym (call : Nat -> String -> Bool -> Int × Nat) (handle : Nat)
    (name : Name) (shouldThrow : Bool) : R (Option Nat) :=
  if handle = 0 then argErr "NULL library handle"
  else
    let result := call handle name.toString shouldThrow
    if result.1 = 0 && !shouldThrow then .ok none else .ok (some result.2)

/-- `dlsym_e(args...)`, `base/libdl.jl:80-82`. -/
def dlsymE (lookup : Bool -> R (Option Nat)) : R Nat := do
  pure (match <- lookup false with | some p => p | none => 0)

/-- Symbol `dlopen`, `base/libdl.jl:118-119`. -/
def dlopenSymbol (openString : String -> Int -> Bool -> R (Option Nat))
    (name : String) (flags : Int) (shouldThrow : Bool) : R (Option Nat) :=
  openString name flags shouldThrow

/-- AbstractString `dlopen`, `base/libdl.jl:121-127`, including Cstring and
UInt32 conversions and the dynamic-loader call. -/
def dlopenString (cstring : String -> R String) (toUInt32 : Int -> R Nat)
    (call : String -> Nat -> Bool -> Nat) (name : String) (flags : Int)
    (shouldThrow : Bool) : R (Option Nat) := do
  let s <- cstring name
  let f <- toUInt32 flags
  let handle := call s f shouldThrow
  if !shouldThrow && handle = 0 then .ok none else .ok (some handle)

structure DoTrace (alpha : Type) where
  result : R alpha
  closed : Option Nat

/-- do-block `dlopen`, `base/libdl.jl:146-154`, including the callback and
the handle passed to `dlclose` in `finally`. -/
def dlopenDo {alpha : Type} (opened : R (Option Nat))
    (f : Option Nat -> R alpha) : DoTrace alpha :=
  match opened with
  | .error e => ⟨.error e, none⟩
  | .ok handle => ⟨f handle, handle⟩

/-- `dlopen_e(args...)`, `base/libdl.jl:162`. -/
def dlopenE (loader : Bool -> R (Option Nat)) : R Nat := do
  pure (match <- loader false with | some p => p | none => 0)

structure FindTrace where
  path : String
  closed : List Nat
  tried : List String
  deriving DecidableEq, Repr

def findCandidates : List String -> (String -> Option Nat) -> List String -> FindTrace
  | [], _, tried => ⟨"", [], tried⟩
  | candidate :: rest, loader, tried =>
      match loader candidate with
      | some handle => ⟨candidate, [handle], tried ++ [candidate]⟩
      | none => findCandidates rest loader (tried ++ [candidate])

/-- `find_library`, `base/libdl.jl:201-218`. -/
def findLibrary (join : String -> String -> String) (loader : String -> Option Nat)
    (names paths : List String) : FindTrace :=
  let candidates := names.flatMap (fun name => paths.map (fun path => join path name) ++ [name])
  findCandidates candidates loader []

/-- Single-name `find_library`, `base/libdl.jl:219-220`. -/
def findLibraryOne (stringify : Name -> String) (join : String -> String -> String)
    (loader : String -> Option Nat) (name : Name) (paths : List String) : FindTrace :=
  findLibrary join loader [stringify name] paths

structure PathTrace where
  path : String
  freed : Bool
  deriving DecidableEq, Repr

/-- `dlpath(handle)`, `base/libdl.jl:227-233`. -/
def dlpathHandle (windows : Bool) (pathname : Nat -> String) (handle : Nat) : R PathTrace :=
  if handle = 0 then argErr "NULL library handle"
  else .ok ⟨pathname handle, windows⟩

/-- `dlpath(libname)`, `base/libdl.jl:245-250`, returning the handle closed
after pathname lookup. -/
def dlpathName (stringify : Name -> String) (loader : String -> R Nat)
    (pathname : Nat -> R String) (name : Name) : R (String × Nat) := do
  let handle <- loader (stringify name)
  let path <- pathname handle
  pure (path, handle)

inductive Platform where | apple | windows | linux | bsd | other deriving DecidableEq

/-- `dllist`, `base/libdl.jl:273-294`. -/
def dllist (platform : Platform) (appleImages cList : List String) : List String :=
  match platform with
  | .apple => appleImages.drop 1
  | .windows | .linux | .bsd => cList
  | .other => []

/-! LazyLibraryPath. -/

structure LazyPath where pieces : List String deriving DecidableEq, Repr

/-- `LazyLibraryPath(pieces...)`, `base/libdl.jl:317`, for every stringable type. -/
def lazyPath {alpha : Type} (stringify : alpha -> String) (pieces : List alpha) : LazyPath :=
  ⟨pieces.map stringify⟩

/-- `string(::LazyLibraryPath)`, `base/libdl.jl:319`. -/
def lazyPathString (joinpath : List String -> String) (path : LazyPath) : String :=
  joinpath path.pieces

/-- `cconvert(Cstring, ::LazyLibraryPath)`, `base/libdl.jl:320`. -/
def lazyPathCconvert (cconvert : String -> R String) (joinpath : List String -> String)
    (path : LazyPath) : R String := cconvert (lazyPathString joinpath path)

/-- `print(io, ::LazyLibraryPath)`, `base/libdl.jl:322`. -/
def lazyPathPrint (out : String) (joinpath : List String -> String) (path : LazyPath) : String :=
  out ++ lazyPathString joinpath path

/-- Runtime private shared-library directory lookup, `base/libdl.jl:326-338`.
The Boolean records the Windows `free` call for a non-null C path. -/
def privateShlibdir (windows : Bool) (cpath : Option String)
    (bindir privateLibdir : String) : String × Bool :=
  match cpath with
  | some path => (path, windows)
  | none => (if windows then bindir else bindir ++ "/" ++ privateLibdir, false)

/-- `BundledLazyLibraryPath`, `base/libdl.jl:356`. -/
def bundledPath {alpha : Type} (stringify : alpha -> String)
    (privateDir : String) (subpath : alpha) : LazyPath :=
  ⟨[privateDir, stringify subpath]⟩

/-- `show(io, ::LazyLibraryPath)`, `base/libdl.jl:358-369`. -/
def showLazyPath (render : String -> String) (out : String)
    (hasPrivateGetter : Bool) (path : LazyPath) : String :=
  if hasPrivateGetter && path.pieces.length = 2 then out ++ render (path.pieces.getD 1 "")
  else out ++ "LazyLibraryPath(" ++ String.intercalate ", " (path.pieces.map render) ++ ")"

structure InitialDeps where
  values : List Nat
  freshVector : Bool
  deriving DecidableEq, Repr

/-- `(init::InitialDependencies)()`, `base/libdl.jl:396`. -/
def initialDependencies (deps : List Nat) : InitialDeps := ⟨deps, true⟩

/-! LazyLibrary. -/

structure LazyLib where
  path : String
  flags : UInt32
  dependencies : List Nat
  callback : Option Nat
  lockCreated : Bool
  handle : Option Nat
  deriving DecidableEq, Repr

/-- `LazyLibrary` constructor, `base/libdl.jl:464-476`. -/
def lazyLibrary (path : String) (flags : UInt32) (dependencies : List Nat)
    (callback : Option Nat) : LazyLib :=
  ⟨path, flags, dependencies, callback, true, none⟩

/-- `_lazy_library_path_string`, `base/libdl.jl:481`. -/
def pathString {alpha : Type} (stringify : alpha -> String) (path : alpha) : String := stringify path

/-- `show(io, ::LazyLibrary)`, `base/libdl.jl:484-488`. -/
def showLazyLibrary (render : String -> String) (out : String) (library : LazyLib) : String :=
  out ++ "LazyLibrary(" ++ render library.path ++ ")"

/-- `add_dependency!`, `base/libdl.jl:509-513`, after acquiring the lock and
calling the OncePerProcess dependency getter. -/
def addDependency (library : LazyLib) (dependency : Nat) : LazyLib :=
  { library with dependencies := library.dependencies ++ [dependency] }

structure LoadTrace where
  result : R Nat
  library : LazyLib
  lockAcquired : Bool
  loadedDependencies : List Nat
  callbackCalled : Bool

/-- `dlopen(::LazyLibrary)`, `base/libdl.jl:519-558`, as one atomic execution. -/
def dlopenLazy (loadDependency : Nat -> R Nat)
    (openPath : String -> Int -> R (Option Nat)) (flags : Int) (library : LazyLib) : LoadTrace :=
  match library.handle with
  | some handle => ⟨.ok handle, library, library.callback.isSome, [], false⟩
  | none =>
      match library.dependencies.mapM loadDependency with
      | .error e => ⟨.error e, library, true, [], false⟩
      | .ok loaded =>
          match openPath library.path flags with
          | .error e => ⟨.error e, library, true, loaded, false⟩
          | .ok none => ⟨.error (.methodError "atomic_store!"), library, true, loaded, false⟩
          | .ok (some handle) =>
              ⟨.ok handle, { library with handle := some handle }, true, loaded, library.callback.isSome⟩

/-- `dlopen(x::Any)`, `base/libdl.jl:559`, retaining the input type. -/
def dlopenAny (typeName : String) : R Nat := .error (.typeError ("dlopen:" ++ typeName))

/-- `dlsym(::LazyLibrary, args...)`, `base/libdl.jl:560`. -/
def dlsymLazy (load : LazyLib -> R Nat) (lookup : Nat -> String -> R Nat)
    (library : LazyLib) (name : String) : R Nat := do
  lookup (<- load library) name

/-- `dlpath(::LazyLibrary)`, `base/libdl.jl:561`. -/
def dlpathLazy (load : LazyLib -> R Nat) (pathname : Nat -> R String)
    (library : LazyLib) : R String := do pathname (<- load library)
end JuliaLean.IOCov.LibdlFaithful
end
