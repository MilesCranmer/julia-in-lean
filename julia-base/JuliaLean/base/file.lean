import JuliaLean.Core
import JuliaLean.base.io
import JuliaLean.base.int
import JuliaLean.base.filesystem
import JuliaLean.base.stat

/-!
# Model of `base/file.jl`

Typed models of the path-level filesystem operations in Julia
`f755f49a9e41380d7da126b3c1db9fe7f83dd027`: `pwd`, `cd`, `mkdir`, `mkpath`, `rm`, `cp`, `mv`,
`touch`, `tempdir`, `tempname`, `mktemp`, `mktempdir`, `readdir`, `eachentry`, `walkdir`, `unlink`,
`rename`, `sendfile`, `hardlink`, `symlink`, `readlink`, `chmod`, `chown` and `diskstat`.

Metadata queries use the installed `base/stat.jl` model (`JuliaLean.base.stat`). The libuv and libc
calls, request memory, string buffers, `path.jl` functions, printing, logging, sorting, hashing,
channels, the temporary-path cleanup registry with its lock, and process spawning are explicit
typed operations in `FileOps`; no laws are assumed about them. Paths are Julia `String` values,
represented by their Lean `String` value as in the `stat.jl` model. `Integer` arguments (modes,
owners, groups) are generic: `IntegerOps` gives their exact value and their printed forms, and the
`Cint` conversion of a `ccall` is Julia's exact `convert`, which raises `InexactError` out of range.
`Sys.iswindows()` and its `@static` branches read the `isWindows` flag. `M` keeps the world on
exceptions; recursion (`mkpath`, `rm`, `cptree`, `chmod`, `_walkdir`, `_resolved_path`) is a
`partial_fixpoint`, where `none` means divergence.
-/

namespace JuliaLean.base.file

open JuliaLean
open JuliaLean.base.io (M Error whileLoop)

abbrev I32 := JInt .i32
abbrev I64 := JInt .i64
abbrev U16 := JInt .u16
abbrev U32 := JInt .u32
abbrev U64 := JInt .u64
abbrev Byte := JInt .u8

/-! ## Recursion through `try`/`catch`/`finally` -/

instance monoBindM {World : Type} : Lean.Order.MonoBind (M World) where
  bind_mono_left h := by
    intro w
    exact Lean.Order.MonoBind.bind_mono_left (m := Option) (h w)
  bind_mono_right h := by
    intro w
    apply Lean.Order.MonoBind.bind_mono_right (m := Option)
    intro r
    rcases r with e | ⟨v, w'⟩
    · exact Lean.Order.PartialOrder.rel_refl
    · exact h v w'

/-- `try action catch err; handler(err) end`: the `tryCatch` of `M`. -/
def tryCatchM {World A : Type} (action : M World A) (handler : Error → M World A) : M World A :=
  fun world => match action world with
  | none => none
  | some (.ok result) => some (.ok result)
  | some (.error (error, world)) => handler error world

@[partial_fixpoint_monotone]
theorem monotone_tryCatchM {World A : Type} {γ : Sort _} [Lean.Order.PartialOrder γ]
    (f : γ → M World A) (g : γ → Error → M World A)
    (hf : Lean.Order.monotone f) (hg : Lean.Order.monotone g) :
    Lean.Order.monotone (fun x => tryCatchM (f x) (g x)) := by
  intro x y hxy w
  have h1 : Lean.Order.PartialOrder.rel (f x w) (f y w) := hf x y hxy w
  dsimp only [tryCatchM]
  revert h1
  generalize f x w = a
  generalize f y w = b
  intro h1
  cases h1 with
  | bot => exact Lean.Order.FlatOrder.rel.bot
  | refl =>
    rcases a with _ | (⟨e, w'⟩ | r)
    · exact Lean.Order.FlatOrder.rel.refl
    · exact hg x y hxy e w'
    · exact Lean.Order.FlatOrder.rel.refl

/-- `try action finally cleanup end`: `cleanup` runs after a result or an exception, and the
exception is thrown again afterwards. -/
def tryFinally {World A B : Type} (action : M World A) (cleanup : M World B) : M World A := do
  let result ← tryCatchM (do pure (Except.ok (← action))) (fun error => pure (Except.error error))
  let _ ← cleanup
  match result with
  | .ok value => pure value
  | .error error => throw error

@[partial_fixpoint_monotone]
theorem monotone_tryFinally {World A B : Type} {γ : Sort _} [Lean.Order.PartialOrder γ]
    (f : γ → M World A) (g : γ → M World B)
    (hf : Lean.Order.monotone f) (hg : Lean.Order.monotone g) :
    Lean.Order.monotone (fun x => tryFinally (f x) (g x)) := by
  unfold tryFinally
  apply Lean.Order.monotone_bind (M World)
  · apply monotone_tryCatchM
    · apply Lean.Order.monotone_bind (M World)
      · exact hf
      · exact Lean.Order.monotone_const _
    · exact Lean.Order.monotone_const _
  · intro x y hxy r
    exact Lean.Order.MonoBind.bind_mono_left (hg x y hxy)

def argumentError (message : String) : Error := .jl (.argumentError message)

/-! ## Inputs -/

/-- A generic `Integer` argument: its exact value and its printed forms (`string(n; base)` and
string interpolation, from `intfuncs.jl` and `show.jl`). -/
structure IntegerOps (World N : Type) where
  value : N → Int
  string : N → Nat → M World String
  display : N → M World String

/-- `cconvert(Cint, n)`: Julia's exact conversion, `InexactError` out of range. -/
def toCint {World N : Type} (intOps : IntegerOps World N) (n : N) : M World I32 :=
  JuliaLean.base.io.liftJl (JInt.convert "convert" .i32 (intOps.value n))

/-- Operations supplied by libuv, libc, the runtime and later-loaded Base files. -/
structure FileOps (World Handle CString StatMemory IOBuf User Group Req StrBuf SizeRef Dirent Stream
    WString Chan Cmd Pipe IterObj DirPtr DiskBuf DiskStatRaw PathVal : Type) where
  stat : JuliaLean.base.stat.StatOps World Handle CString StatMemory IOBuf User Group PathVal
  isWindows : Bool
  uvEnoent : I32
  uvEacces : I32
  uvEnobufs : I32
  uvEof : I32
  /-- `err isa IOError`, with `err.code`. -/
  ioErrorCode : Error → Option I32
  isSystemError : Error → Bool
  isInterruptException : Error → Bool
  /-- `string(ex)` of an exception. -/
  errorString : Error → M World String
  u64Ops : IntegerOps World U64
  i64Ops : IntegerOps World I64
  repr : String → M World String
  /-- `path.jl`. -/
  joinpath : List String → M World String
  dirname : String → M World String
  basename : String → M World String
  abspath : String → M World String
  normpath : String → M World String
  realpath : String → M World String
  isabspath : String → M World Bool
  homedir : Unit → M World String
  isseparator : Char → M World Bool
  pathSeparator : String
  /-- `last(s)` of a nonempty string. -/
  lastChar : String → M World Char
  /-- `Libc.malloc(_sizeof_uv_fs)`, `Libc.free`, `uv_fs_req_cleanup`. -/
  mallocReq : Unit → M World Req
  freeReq : Req → M World Unit
  reqCleanup : Req → M World Unit
  uvFsMkdir : Req → CString → I32 → M World I32
  uvFsRmdir : Req → CString → M World I32
  uvFsMkdtemp : Req → CString → M World I32
  uvFsReadlink : Req → CString → M World I32
  uvFsScandir : Req → CString → I32 → M World I32
  uvFsScandirNext : Req → Dirent → M World I32
  /-- `unsafe_string(ccall(:jl_uv_fs_t_path, ...))`. -/
  uvFsTPath : Req → M World String
  /-- `unsafe_string(ccall(:jl_uv_fs_t_ptr, ...))`. -/
  uvFsTPtr : Req → M World String
  newDirent : Unit → M World Dirent
  direntName : Dirent → M World String
  direntType : Dirent → M World I32
  /-- `AVG_PATH`. -/
  avgPath : I64
  newStringVector : I64 → M World StrBuf
  stringVectorLength : StrBuf → M World I64
  stringVectorSet : StrBuf → I64 → Byte → M World Unit
  /-- `resize!(buf, n)` for a `Csize_t` length. -/
  resizeStringVector : StrBuf → U64 → M World Unit
  /-- `String(buf)`. -/
  stringVectorString : StrBuf → M World String
  newSizeRef : U64 → M World SizeRef
  getSizeRef : SizeRef → M World U64
  uvCwd : StrBuf → SizeRef → M World I32
  uvOsTmpdir : StrBuf → SizeRef → M World I32
  uvChdir : CString → M World I32
  /-- `ccall(:open, Int32, (Cstring, Int32, UInt32...), :., 0)`. -/
  openDot : Unit → M World I32
  fchdir : I32 → M World I32
  closeFd : I32 → M World I32
  fsUnlink : CString → M World I32
  fsRename : CString → CString → M World I32
  fsCopyfile : CString → CString → I32 → M World I32
  fsHardlink : CString → CString → M World I32
  fsSymlink : CString → CString → I32 → M World I32
  fsChmod : CString → I32 → M World I32
  fsChown : CString → I32 → I32 → M World I32
  /-- `Sys.windows_version() < Sys.WINDOWS_VISTA_VER`. -/
  windowsBeforeVista : Unit → M World Bool
  /-- `JL_O_WRONLY` and `JL_O_CREAT` (`file_constants.jl`). -/
  jlOWronly : I64
  jlOCreat : I64
  /-- `open(path, flags, mode)` (`filesystem.jl`). -/
  openFlags : String → I64 → U16 → M World Stream
  /-- `open(path, mode::AbstractString)` (`iostream.jl`). -/
  openMode : String → String → M World Stream
  touchStream : Stream → M World Unit
  closeStream : Stream → M World Unit
  printString : Stream → String → M World Unit
  fdio : I32 → Bool → M World Stream
  /-- `ccall(:mkstemp, ...)` with the template's C string, and that string afterwards. -/
  mkstemp : CString → M World I32
  cstringContents : CString → M World String
  /-- `cwstring` and `GetTempFileNameW` writing its 32767-element `UInt16` buffer. -/
  cwstring : String → M World WString
  getTempFileName : WString → WString → U32 → M World (U32 × List U16)
  getLastError : Unit → M World U32
  /-- `transcode(String, ::Vector{UInt16})`. -/
  utf16String : List U16 → M World String
  logWarn : String → M World Unit
  logDebug : String → M World Unit
  /-- `@error message exception=(ex, catch_backtrace())`. -/
  logError : String → Error → M World Unit
  /-- `Channel{Tuple{String,Vector{String},Vector{String}}}(producer)` (`channels.jl`). -/
  newChannel : (Chan → M World Unit) → M World Chan
  channelPush : Chan → (String × List String × List String) → M World Unit
  channelClose : Chan → Error → M World Unit
  /-- `for item in chnl; body(item); end`. -/
  channelForEach : Chan → ((String × List String × List String) → M World Unit) → M World Unit
  /-- `@lock TEMP_CLEANUP_LOCK body`. -/
  withCleanupLock : {A : Type} → M World A → M World A
  /-- `TEMP_CLEANUP::Dict{String,Bool}`. -/
  cleanupGet : String → Bool → M World Bool
  cleanupSet : String → Bool → M World Unit
  cleanupLength : Unit → M World I64
  cleanupDelete : String → M World Unit
  cleanupKeys : Unit → M World (List String)
  /-- `filter!(pred, TEMP_CLEANUP)` with a predicate that also updates a local state. -/
  cleanupFilter : {S : Type} → S → (S → String → Bool → M World (Bool × S)) → M World S
  cleanupMinGet : Unit → M World I64
  cleanupMaxGet : Unit → M World I64
  cleanupMaxSet : I64 → M World Unit
  /-- `GC.gc(true)`. -/
  gcFull : Unit → M World Unit
  atexit : M World Unit → M World Unit
  /-- `Cmd(Base.cmd_gen(((Base.julia_cmd(),), ("--startup-file=no",), ("-e",), (code,)));
  ignorestatus = true, detach = true)`. -/
  cleanupCommand : String → M World Cmd
  newPipeEndpoint : Unit → M World Pipe
  /-- `run(cmd, pw, devnull, stderr; wait=false)`. -/
  runDetached : Cmd → Pipe → M World Unit
  /-- `join(pw, items, delim)`. -/
  joinWrite : Pipe → List String → String → M World Unit
  /-- `Base.dup(Base._fd(pw))`. -/
  dupPipe : Pipe → M World Unit
  closePipe : Pipe → M World Unit
  libcRand : Unit → M World U32
  /-- `isless(::String, ::String)` and `sort!` (`sort.jl`). -/
  islessString : String → String → M World Bool
  sortBy : {A : Type} → (A → A → M World Bool) → List A → M World (List A)
  hashString : String → U64 → M World U64
  hashI32 : I32 → U64 → M World U64
  /-- `DirEntryIterator` objects: allocation with a finalizer, and their mutable fields. -/
  newIterator : String → Bool → M World IterObj
  iterUvdir : IterObj → M World DirPtr
  iterSwapUvdir : IterObj → DirPtr → M World DirPtr
  iterSetUvdir : IterObj → DirPtr → M World Unit
  iterStatus : IterObj → M World I32
  iterClosed : IterObj → M World Bool
  iterSetClosed : IterObj → Bool → M World Unit
  nullDir : DirPtr
  isNullDir : DirPtr → Bool
  /-- `jl_uv_fs_opendir`, with the pointer it writes. -/
  uvFsOpendir : CString → M World (I32 × DirPtr)
  uvFsClosedir : DirPtr → M World I32
  /-- `jl_uv_fs_readdir1`: the next name, or `nothing` at the end, writing the status. -/
  uvFsReaddir1 : DirPtr → IterObj → M World (Option String)
  /-- `zeros(UInt8, _sizeof_uv_fs)`, `uv_fs_statfs`, and the loaded `DiskStat`. -/
  newStatfsBuffer : Unit → M World DiskBuf
  uvFsStatfs : DiskBuf → CString → M World I32
  loadDiskStat : DiskBuf → M World DiskStatRaw
  diskStatFields : DiskStatRaw → List U64 × List U64

section
variable {World Handle CString StatMemory IOBuf User Group Req StrBuf SizeRef Dirent Stream WString
  Chan Cmd Pipe IterObj DirPtr DiskBuf DiskStatRaw PathVal : Type}
variable (ops : FileOps World Handle CString StatMemory IOBuf User Group Req StrBuf SizeRef Dirent
  Stream WString Chan Cmd Pipe IterObj DirPtr DiskBuf DiskStatRaw PathVal)

/-! ## Calls into the `stat.jl` model -/

/-- `isdir(path)`, `islink(path)`, `isfile(path)`, ... for a path argument: the `stat.jl` predicate of
`stat(path)` (or `lstat(path)` for `islink`), over every `AbstractString` the `stat` methods accept
(`JuliaLean.base.stat.PathString`; a `String` coerces to it). -/
def isdirPath (path : JuliaLean.base.stat.PathString PathVal) : M World Bool := do
  pure (JuliaLean.base.stat.isDirectory (← JuliaLean.base.stat.statPath ops.stat path))

def islinkPath (path : JuliaLean.base.stat.PathString PathVal) : M World Bool := do
  pure (JuliaLean.base.stat.isLink (← JuliaLean.base.stat.lstatPath ops.stat path))

def isfilePath (path : JuliaLean.base.stat.PathString PathVal) : M World Bool := do
  pure (JuliaLean.base.stat.isRegularFile (← JuliaLean.base.stat.statPath ops.stat path))

def isfifoPath (path : JuliaLean.base.stat.PathString PathVal) : M World Bool := do
  pure (JuliaLean.base.stat.isFifo (← JuliaLean.base.stat.statPath ops.stat path))

def issocketPath (path : JuliaLean.base.stat.PathString PathVal) : M World Bool := do
  pure (JuliaLean.base.stat.isSocket (← JuliaLean.base.stat.statPath ops.stat path))

def ischardevPath (path : JuliaLean.base.stat.PathString PathVal) : M World Bool := do
  pure (JuliaLean.base.stat.isCharDevice (← JuliaLean.base.stat.statPath ops.stat path))

def isblockdevPath (path : JuliaLean.base.stat.PathString PathVal) : M World Bool := do
  pure (JuliaLean.base.stat.isBlockDevice (← JuliaLean.base.stat.statPath ops.stat path))

/-- `ispath(path::String)` and `ispath(path::AbstractString) = ispath(String(path)::String)`. -/
def ispathPath (path : JuliaLean.base.stat.PathString PathVal) : M World Bool :=
  JuliaLean.base.stat.isPathAbstract ops.stat path

def filemodePath (path : JuliaLean.base.stat.PathString PathVal) : M World U64 := do
  pure (JuliaLean.base.stat.fileMode (← JuliaLean.base.stat.statPath ops.stat path))

def samefilePaths (a b : JuliaLean.base.stat.PathString PathVal) : M World Bool :=
  JuliaLean.base.stat.sameFilePaths ops.stat a b

def cstr (path : String) : M World CString := ops.stat.toCString path

def uvError (message : String) (code : I32) : M World Unit :=
  ops.stat.errors.uvError message code

def isIOErrorCode (err : Error) (code : I32) : Bool :=
  match ops.ioErrorCode err with
  | some c => c == code
  | none => false

def isIOError (err : Error) : Bool := (ops.ioErrorCode err).isSome

/-! ## Methods -/

-- Reason: The export list is load-time metadata; the exported methods are modelled below.
-- UNTRANSLATED
-- Source: base/file.jl:1-33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- # Operations with the file system (paths) ##
-- 
-- export
--     cd,
--     chmod,
--     chown,
--     cp,
--     cptree,
--     DirEntry,
--     diskstat,
--     eachentry,
--     hardlink,
--     mkdir,
--     mkpath,
--     mktemp,
--     mktempdir,
--     mv,
--     pwd,
--     rename,
--     readlink,
--     readdir,
--     rm,
--     samefile,
--     sendfile,
--     symlink,
--     tempdir,
--     tempname,
--     touch,
--     unlink,
--     walkdir
-- 
-- /Source

/--
Julia source: base/file.jl:34-70 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
# get and set current directory

"""
    pwd()::String

Get the current working directory.

See also: [`cd`](@ref), [`tempdir`](@ref).

# Examples
```julia-repl
julia> pwd()
"/home/JuliaUser"

julia> cd("/home/JuliaUser/Projects/julia")

julia> pwd()
"/home/JuliaUser/Projects/julia"
```
"""
function pwd()
    buf = Base.StringVector(AVG_PATH - 1) # space for null-terminator implied by StringVector
    sz = RefValue{Csize_t}(length(buf) + 1) # total buffer size including null
    while true
        rc = ccall(:uv_cwd, Cint, (Ptr{UInt8}, Ptr{Csize_t}), buf, sz)
        if rc == 0
            resize!(buf, sz[])
            return String(buf)
        elseif rc == Base.UV_ENOBUFS
            resize!(buf, sz[] - 1) # space for null-terminator implied by StringVector
        else
            uv_error("pwd()", rc)
        end
    end
end


````
-/
def pwd : M World String := do
  let buf ← ops.newStringVector (JuliaLean.base.int.sub ops.avgPath (JInt.lit .i64 1))
  let len ← ops.stringVectorLength buf
  let size ← JuliaLean.base.io.liftJl
    (JInt.convert "convert" .u64 (JuliaLean.base.int.add len (JInt.lit .i64 1)).val)
  let sz ← ops.newSizeRef size
  whileLoop (fun (_ : Unit) => do
    let rc ← ops.uvCwd buf sz
    if rc.val == 0 then
      ops.resizeStringVector buf (← ops.getSizeRef sz)
      return Sum.inl (← ops.stringVectorString buf)
    else if rc == ops.uvEnobufs then
      ops.resizeStringVector buf (JuliaLean.base.int.sub (← ops.getSizeRef sz) (JInt.lit .u64 1))
      return Sum.inr ()
    else
      uvError ops "pwd()" rc
      return Sum.inr ()) ()

/--
Julia source: base/file.jl:71-97 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    cd(dir::AbstractString=homedir())

Set the current working directory.

See also: [`pwd`](@ref), [`mkdir`](@ref), [`mkpath`](@ref), [`mktempdir`](@ref).

# Examples
```julia-repl
julia> cd("/home/JuliaUser/Projects/julia")

julia> pwd()
"/home/JuliaUser/Projects/julia"

julia> cd()

julia> pwd()
"/home/JuliaUser"
```
"""
function cd(dir::AbstractString)
    err = ccall(:uv_chdir, Cint, (Cstring,), dir)
    err < 0 && uv_error("cd($(repr(dir)))", err)
    return nothing
end
cd() = cd(homedir())

````
-/
def cd (dir : String) : M World Unit := do
  let cdir ← cstr ops dir
  let err ← ops.uvChdir cdir
  if err.val < 0 then
    uvError ops ("cd(" ++ (← ops.repr dir) ++ ")") err
  pure ()

def cdHome : M World Unit := do
  cd ops (← ops.homedir ())

/--
Julia source: base/file.jl:98-120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
if Sys.iswindows()
    function cd(f::Function, dir::AbstractString)
        old = pwd()
        try
            cd(dir)
            f()
       finally
            cd(old)
        end
    end
else
    function cd(f::Function, dir::AbstractString)
        fd = ccall(:open, Int32, (Cstring, Int32, UInt32...), :., 0)
        systemerror(:open, fd == -1)
        try
            cd(dir)
            f()
        finally
            systemerror(:fchdir, ccall(:fchdir, Int32, (Int32,), fd) != 0)
            systemerror(:close, ccall(:close, Int32, (Int32,), fd) != 0)
        end
    end
end
```
-/
def cdWithWindows {A : Type} (f : Unit → M World A) (dir : String) : M World A := do
  let old ← pwd ops
  tryFinally (do
    cd ops dir
    f ()) (cd ops old)

def cdWithUnix {A : Type} (f : Unit → M World A) (dir : String) : M World A := do
  let fd ← ops.openDot ()
  ops.stat.errors.systemError "open" (fd.val == -1)
  tryFinally (do
    cd ops dir
    f ()) (do
    ops.stat.errors.systemError "fchdir" ((← ops.fchdir fd).val != 0)
    ops.stat.errors.systemError "close" ((← ops.closeFd fd).val != 0))

/-- `cd(f, dir)`: the method defined for the platform. -/
def cdWith {A : Type} (f : Unit → M World A) (dir : String) : M World A :=
  if ops.isWindows then cdWithWindows ops f dir else cdWithUnix ops f dir

/--
Julia source: base/file.jl:121-150 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    cd(f::Function, dir::AbstractString=homedir())

Temporarily change the current working directory to `dir`, apply function `f` and
finally return to the original directory.

# Examples
```julia-repl
julia> pwd()
"/home/JuliaUser"

julia> cd(readdir, "/home/JuliaUser/Projects/julia")
34-element Vector{String}:
 ".circleci"
 ".freebsdci.sh"
 ".git"
 ".gitattributes"
 ".github"
 ⋮
 "test"
 "ui"
 "usr"
 "usr-staging"

julia> pwd()
"/home/JuliaUser"
```
"""
cd(f::Function) = cd(f, homedir())

````
-/
def cdWithHome {A : Type} (f : Unit → M World A) : M World A := do
  cdWith ops f (← ops.homedir ())

/--
Julia source: base/file.jl:151-157 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function checkmode(mode::Integer)
    if !(0 <= mode <= 511)
        throw(ArgumentError("Mode must be between 0 and 511 = 0o777"))
    end
    mode
end

```
-/
def checkmode {N : Type} (mode : N) (intOps : IntegerOps World N) : M World N :=
  if !(0 ≤ intOps.value mode ∧ intOps.value mode ≤ 511) then
    throw (argumentError "Mode must be between 0 and 511 = 0o777")
  else pure mode

/--
Julia source: base/file.jl:158-195 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    mkdir(path::AbstractString; mode::Unsigned = 0o777)

Make a new directory with name `path` and permissions `mode`. `mode` defaults to `0o777`,
modified by the current file creation mask. This function never creates more than one
directory. If the directory already exists, or some intermediate directories do not exist,
this function throws an error. See [`mkpath`](@ref) for a function which creates all
required intermediate directories.
Return `path`.

# Examples
```jldoctest; setup = :(curdir = pwd(); testdir = mktempdir(); cd(testdir)), teardown = :(cd(curdir); rm(testdir, recursive=true)), filter = r"^\\".*testingdir\\"\$"
julia> mkdir("testingdir")
"testingdir"

julia> cd("testingdir")

julia> pwd()
"/home/JuliaUser/testingdir"
```
"""
function mkdir(path::AbstractString; mode::Integer = 0o777)
    req = Libc.malloc(_sizeof_uv_fs)
    try
        ret = ccall(:uv_fs_mkdir, Cint,
                    (Ptr{Cvoid}, Ptr{Cvoid}, Cstring, Cint, Ptr{Cvoid}),
                    C_NULL, req, path, checkmode(mode), C_NULL)
        if ret < 0
            uv_fs_req_cleanup(req)
            uv_error("mkdir($(repr(path)); mode=0o$(string(mode,base=8)))", ret)
        end
        uv_fs_req_cleanup(req)
        return path
    finally
        Libc.free(req)
    end
end

````
-/
def mkdir {N : Type} (intOps : IntegerOps World N) (path : String) (mode : N) :
    M World String := do
  let req ← ops.mallocReq ()
  tryFinally (do
    let checked ← checkmode mode intOps
    let cmode ← toCint intOps checked
    let cpath ← cstr ops path
    let ret ← ops.uvFsMkdir req cpath cmode
    if ret.val < 0 then
      ops.reqCleanup req
      uvError ops ("mkdir(" ++ (← ops.repr path) ++ "; mode=0o" ++ (← intOps.string mode 8) ++ ")") ret
    ops.reqCleanup req
    pure path) (ops.freeReq req)

/--
Julia source: base/file.jl:196-257 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    mkpath(path::AbstractString; mode::Unsigned = 0o777)

Create all intermediate directories in the `path` as required. Directories are created with
the permissions `mode` which defaults to `0o777` and is modified by the current file
creation mask. Unlike [`mkdir`](@ref), `mkpath` does not error if `path` (or parts of it)
already exists. However, an error will be thrown if `path` (or parts of it) points to an
existing file. Return `path`.

If `path` includes a filename you will probably want to use `mkpath(dirname(path))` to
avoid creating a directory using the filename.

# Examples
```julia-repl
julia> cd(mktempdir())

julia> mkpath("my/test/dir") # creates three directories
"my/test/dir"

julia> readdir()
1-element Vector{String}:
 "my"

julia> cd("my")

julia> readdir()
1-element Vector{String}:
 "test"

julia> readdir("test")
1-element Vector{String}:
 "dir"

julia> mkpath("intermediate_dir/actually_a_directory.txt") # creates two directories
"intermediate_dir/actually_a_directory.txt"

julia> isdir("intermediate_dir/actually_a_directory.txt")
true

julia> mkpath("my/test/dir/") # returns the original `path`
"my/test/dir/"
```
"""
function mkpath(path::AbstractString; mode::Integer = 0o777)
    parent = dirname(path)
    # stop recursion for `""`, `"/"`, or existing dir
    (path == parent || isdir(path)) && return path
    mkpath(parent, mode = checkmode(mode))
    try
        # The `isdir` check could be omitted, then `mkdir` will throw an error in cases like `x/`.
        # Although the error will not be rethrown, we avoid it in advance for performance reasons.
        isdir(path) || mkdir(path, mode = mode)
    catch err
        # If there is a problem with making the directory, but the directory
        # does in fact exist, then ignore the error. Else re-throw it.
        if !isa(err, IOError) || !isdir(path)
            rethrow()
        end
    end
    return path
end

````
-/
def mkpath {N : Type} (intOps : IntegerOps World N) (path : String) (mode : N) :
    M World String := do
  let parent ← ops.dirname path
  if path == parent then return path
  if ← isdirPath ops path then return path
  let _ ← mkpath intOps parent (← checkmode mode intOps)
  tryCatchM (do
      if !(← isdirPath ops path) then
        let _ ← mkdir ops intOps path mode
      pure ())
    (fun err => do
      if !isIOError ops err then throw err
      if !(← isdirPath ops path) then throw err)
  pure path
partial_fixpoint

/--
Julia source: base/file.jl:1445-1450 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unlink(p::AbstractString)
    err = ccall(:jl_fs_unlink, Int32, (Cstring,), p)
    err < 0 && uv_error("unlink($(repr(p)))", err)
    nothing
end

```
-/
def unlink (p : String) : M World Unit := do
  let cp ← cstr ops p
  let err ← ops.fsUnlink cp
  if err.val < 0 then uvError ops ("unlink(" ++ (← ops.repr p) ++ ")") err

/--
Julia source: base/file.jl:1451-1484 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Base.rename(oldpath::AbstractString, newpath::AbstractString)

Change the name of a file or directory from `oldpath` to `newpath`.
If `newpath` is an existing file or empty directory it may be replaced.
Equivalent to [rename(2)](https://man7.org/linux/man-pages/man2/rename.2.html) on Unix.
If a path contains a "\\0" throw an `ArgumentError`.
On other failures throw an `IOError`.
Return `newpath`.

This is a lower level filesystem operation used to implement [`mv`](@ref).

OS-specific restrictions may apply when `oldpath` and `newpath` are in different directories.

Currently there are a few differences in behavior on Windows which may be resolved in a future release.
Specifically, currently on Windows:
1. `rename` will fail if `oldpath` or `newpath` are opened files.
2. `rename` will fail if `newpath` is an existing directory.
3. `rename` may work if `newpath` is a file and `oldpath` is a directory.
4. `rename` may remove `oldpath` if it is a hardlink to `newpath`.

See also: [`mv`](@ref).

!!! compat "Julia 1.12"
    This method was made public in Julia 1.12.
"""
function rename(oldpath::AbstractString, newpath::AbstractString)
    err = ccall(:jl_fs_rename, Int32, (Cstring, Cstring), oldpath, newpath)
    if err < 0
        uv_error("rename($(repr(oldpath)), $(repr(newpath)))", err)
    end
    newpath
end

```
-/
def rename (oldpath newpath : String) : M World String := do
  let cold ← cstr ops oldpath
  let cnew ← cstr ops newpath
  let err ← ops.fsRename cold cnew
  if err.val < 0 then
    uvError ops ("rename(" ++ (← ops.repr oldpath) ++ ", " ++ (← ops.repr newpath) ++ ")") err
  pure newpath

/--
Julia source: base/file.jl:1485-1487 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const UV_FS_COPYFILE_EXCL = 0x0001
const UV_FS_COPYFILE_FICLONE = 0x0002

```
-/
def uvFsCopyfileExcl : U16 := JInt.lit .u16 0x0001
def uvFsCopyfileFiclone : U16 := JInt.lit .u16 0x0002

/--
Julia source: base/file.jl:1488-1495 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sendfile(src::AbstractString, dst::AbstractString; force::Bool=true)
    flags = force ? UV_FS_COPYFILE_FICLONE : UV_FS_COPYFILE_FICLONE | UV_FS_COPYFILE_EXCL
    result = ccall(:jl_fs_copyfile, Cint, (Cstring, Cstring, Cint),
                    src, dst, flags % Cint)
    uv_error("copyfile", result)
    return nothing
end

```
-/
def sendfile (src dst : String) (force : Bool) : M World Unit := do
  let flags := if force then uvFsCopyfileFiclone
    else JuliaLean.base.int.bor uvFsCopyfileFiclone uvFsCopyfileExcl
  let csrc ← cstr ops src
  let cdst ← cstr ops dst
  let result ← ops.fsCopyfile csrc cdst (JInt.wrap .i32 flags.val)
  uvError ops "copyfile" result

/--
Julia source: base/file.jl:1496-1501 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
if Sys.iswindows()
    const UV_FS_SYMLINK_DIR      = 0x0001
    const UV_FS_SYMLINK_JUNCTION = 0x0002
    const UV__EPERM              = -4048
end

```
-/
def uvFsSymlinkDir : U16 := JInt.lit .u16 0x0001
def uvFsSymlinkJunction : U16 := JInt.lit .u16 0x0002
def uvEpermWindows : I64 := JInt.lit .i64 (-4048)

/--
Julia source: base/file.jl:1502-1521 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    hardlink(src::AbstractString, dst::AbstractString)

Create a hard link to an existing source file `src` with the name `dst`. The
destination, `dst`, must not exist.

See also: [`symlink`](@ref).

!!! compat "Julia 1.8"
    This method was added in Julia 1.8.
"""
function hardlink(src::AbstractString, dst::AbstractString)
    err = ccall(:jl_fs_hardlink, Int32, (Cstring, Cstring), src, dst)
    if err < 0
        msg = "hardlink($(repr(src)), $(repr(dst)))"
        uv_error(msg, err)
    end
    return nothing
end

```
-/
def hardlink (src dst : String) : M World Unit := do
  let csrc ← cstr ops src
  let cdst ← cstr ops dst
  let err ← ops.fsHardlink csrc cdst
  if err.val < 0 then
    let msg := "hardlink(" ++ (← ops.repr src) ++ ", " ++ (← ops.repr dst) ++ ")"
    uvError ops msg err

/--
Julia source: base/file.jl:1522-1597 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    symlink(target::AbstractString, link::AbstractString; dir_target = false)

Create a symbolic link to `target` with the name `link`.

On Windows, symlinks must be explicitly declared as referring to a directory
or not.  If `target` already exists, by default the type of `link` will be auto-
detected, however if `target` does not exist, this function defaults to creating
a file symlink unless `dir_target` is set to `true`.  Note that if the user
sets `dir_target` but `target` exists and is a file, a directory symlink will
still be created, but dereferencing the symlink will fail, just as if the user
creates a file symlink (by calling `symlink()` with `dir_target` set to `false`
before the directory is created) and tries to dereference it to a directory.

Additionally, there are two methods of making a link on Windows; symbolic links
and junction points.  Junction points are slightly more efficient, but do not
support relative paths, so if a relative directory symlink is requested (as
denoted by `isabspath(target)` returning `false`) a symlink will be used, else
a junction point will be used.  Best practice for creating symlinks on Windows
is to create them only after the files/directories they reference are already
created.

See also: [`hardlink`](@ref).

!!! note
    This function raises an error under operating systems that do not support
    soft symbolic links, such as Windows XP.

!!! compat "Julia 1.6"
    The `dir_target` keyword argument was added in Julia 1.6.  Prior to this,
    symlinks to nonexistent paths on windows would always be file symlinks, and
    relative symlinks to directories were not supported.
"""
function symlink(target::AbstractString, link::AbstractString;
                 dir_target::Bool = false)
    @static if Sys.iswindows()
        if Sys.windows_version() < Sys.WINDOWS_VISTA_VER
            error("Windows XP does not support soft symlinks")
        end
    end
    flags = 0
    @static if Sys.iswindows()
        # If we're going to create a directory link, we need to know beforehand.
        # First, if `target` is not an absolute path, let's immediately resolve
        # it so that we can peek and see if it's a directory.
        resolved_target = target
        if !isabspath(target)
            resolved_target = joinpath(dirname(link), target)
        end

        # If it is a directory (or `dir_target` is set), we'll need to add one
        # of `UV_FS_SYMLINK_{DIR,JUNCTION}` to the flags, depending on whether
        # `target` is an absolute path or not.
        if (ispath(resolved_target) && isdir(resolved_target)) || dir_target
            if isabspath(target)
                flags |= UV_FS_SYMLINK_JUNCTION
            else
                flags |= UV_FS_SYMLINK_DIR
            end
        end
    end
    err = ccall(:jl_fs_symlink, Int32, (Cstring, Cstring, Cint), target, link, flags)
    if err < 0
        msg = "symlink($(repr(target)), $(repr(link)))"
        @static if Sys.iswindows()
            # creating file/directory symlinks requires Administrator privileges
            # while junction points apparently do not
            if flags & UV_FS_SYMLINK_JUNCTION == 0 && err == UV__EPERM
                msg = "On Windows, creating symlinks requires Administrator privileges.\n$msg"
            end
        end
        uv_error(msg, err)
    end
    return nothing
end

```
-/
def symlink (target link : String) (dirTarget : Bool) : M World Unit := do
  if ops.isWindows then
    if ← ops.windowsBeforeVista () then
      throw (.errorException "Windows XP does not support soft symlinks")
  let mut flags : I64 := JInt.lit .i64 0
  if ops.isWindows then
    let resolvedTarget ← do
      if !(← ops.isabspath target) then ops.joinpath [← ops.dirname link, target]
      else pure target
    let isDirectory ← do
      if ← ispathPath ops resolvedTarget then isdirPath ops resolvedTarget
      else pure false
    if isDirectory || dirTarget then
      if ← ops.isabspath target then
        flags := JuliaLean.base.int.bor flags (JInt.wrap .i64 uvFsSymlinkJunction.val)
      else
        flags := JuliaLean.base.int.bor flags (JInt.wrap .i64 uvFsSymlinkDir.val)
  let cflags ← JuliaLean.base.io.liftJl (JInt.convert "convert" .i32 flags.val)
  let ctarget ← cstr ops target
  let clink ← cstr ops link
  let err ← ops.fsSymlink ctarget clink cflags
  if err.val < 0 then
    let mut msg := "symlink(" ++ (← ops.repr target) ++ ", " ++ (← ops.repr link) ++ ")"
    if ops.isWindows then
      if (JuliaLean.base.int.and_int flags (JInt.wrap .i64 uvFsSymlinkJunction.val)).val == 0 &&
          err.val == uvEpermWindows.val then
        msg := "On Windows, creating symlinks requires Administrator privileges.\n" ++ msg
    uvError ops msg err

/--
Julia source: base/file.jl:1598-1621 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    readlink(path::AbstractString)::String

Return the target location a symbolic link `path` points to.
"""
function readlink(path::AbstractString)
    req = Libc.malloc(_sizeof_uv_fs)
    try
        ret = ccall(:uv_fs_readlink, Int32,
            (Ptr{Cvoid}, Ptr{Cvoid}, Cstring, Ptr{Cvoid}),
            C_NULL, req, path, C_NULL)
        if ret < 0
            uv_fs_req_cleanup(req)
            uv_error("readlink($(repr(path)))", ret)
            @assert false "unexpected uv readlink error"
        end
        tgt = unsafe_string(ccall(:jl_uv_fs_t_ptr, Cstring, (Ptr{Cvoid},), req))
        uv_fs_req_cleanup(req)
        return tgt
    finally
        Libc.free(req)
    end
end

```
-/
def readlink (path : String) : M World String := do
  let req ← ops.mallocReq ()
  tryFinally (do
    let cpath ← cstr ops path
    let ret ← ops.uvFsReadlink req cpath
    if ret.val < 0 then
      ops.reqCleanup req
      uvError ops ("readlink(" ++ (← ops.repr path) ++ ")") ret
      throw (.foreignError "AssertionError" "unexpected uv readlink error")
    let tgt ← ops.uvFsTPtr req
    ops.reqCleanup req
    pure tgt) (ops.freeReq req)

/--
Julia source: base/file.jl:1000-1004 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct uv_dirent_t
    name::Ptr{UInt8}
    typ::Cint
end

```
-/
structure UvDirentT (Ptr : Type) where
  name : Ptr
  typ : I32

/--
Julia source: base/file.jl:1084-1094 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# this might be better as an Enum but they're not available here
# UV_DIRENT_T
const UV_DIRENT_UNKNOWN = Cint(0)
const UV_DIRENT_FILE = Cint(1)
const UV_DIRENT_DIR = Cint(2)
const UV_DIRENT_LINK = Cint(3)
const UV_DIRENT_FIFO = Cint(4)
const UV_DIRENT_SOCKET = Cint(5)
const UV_DIRENT_CHAR = Cint(6)
const UV_DIRENT_BLOCK = Cint(7)

```
-/
def uvDirentUnknown : I32 := JInt.lit .i32 0
def uvDirentFile : I32 := JInt.lit .i32 1
def uvDirentDir : I32 := JInt.lit .i32 2
def uvDirentLink : I32 := JInt.lit .i32 3
def uvDirentFifo : I32 := JInt.lit .i32 4
def uvDirentSocket : I32 := JInt.lit .i32 5
def uvDirentChar : I32 := JInt.lit .i32 6
def uvDirentBlock : I32 := JInt.lit .i32 7

/--
Julia source: base/file.jl:1095-1121 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    DirEntry

A type representing a filesystem entry that contains the name of the entry, the directory, and
the raw type of the entry. The full path of the entry can be obtained lazily via [`joinpath(entry)`](@ref).

The directory and name components are accessed via [`dirname`](@ref) and [`basename`](@ref),
respectively, mirroring the behavior of the corresponding string-returning functions.

The type of the entry can be checked for by calling [`isfile`](@ref), [`isdir`](@ref),
[`islink`](@ref), [`isfifo`](@ref), [`issocket`](@ref), [`ischardev`](@ref), and [`isblockdev`](@ref)
on the entry object. These predicates use the raw type cached at scan time when available; on
filesystems that report `UV_DIRENT_UNKNOWN` (some network/FUSE mounts) and for symlinks they fall
through to a `stat` syscall on each call. Callers in tight loops that need multiple predicates for
the same entry should call [`stat`](@ref) once and reuse the result.

!!! warning "Staleness"
    A `DirEntry` is a snapshot from when the directory was scanned. The underlying filesystem may
    have changed in the meantime: the entry may no longer exist, may have been replaced by a
    different type, or the cached `rawtype` may be wrong. Treat `DirEntry` values as advisory
    and re-`stat` if up-to-date information is required.
"""
struct DirEntry
    dir::String
    name::String
    rawtype::Cint
end
```
-/
structure DirEntry where
  dir : String
  name : String
  rawtype : I32
  deriving DecidableEq

/--
Julia source: base/file.jl:1122-1137 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
basename(obj::DirEntry) = getfield(obj, :name)
dirname(obj::DirEntry) = getfield(obj, :dir)
joinpath(obj::DirEntry, args...) = joinpath(dirname(obj), basename(obj), args...)
Base.isless(a::DirEntry, b::DirEntry) = dirname(a) == dirname(b) ? isless(basename(a), basename(b)) : isless(dirname(a), dirname(b))
Base.hash(o::DirEntry, h::UInt) = hash(dirname(o), hash(basename(o), hash(o.rawtype, h)))
Base.:(==)(a::DirEntry, b::DirEntry) = basename(a) == basename(b) && dirname(a) == dirname(b) && a.rawtype == b.rawtype
isunknown(obj::DirEntry) =  obj.rawtype == UV_DIRENT_UNKNOWN
islink(obj::DirEntry) =     isunknown(obj) ? islink(joinpath(obj)) : obj.rawtype == UV_DIRENT_LINK
isfile(obj::DirEntry) =     (isunknown(obj) || islink(obj)) ? isfile(joinpath(obj))      : obj.rawtype == UV_DIRENT_FILE
isdir(obj::DirEntry) =      (isunknown(obj) || islink(obj)) ? isdir(joinpath(obj))       : obj.rawtype == UV_DIRENT_DIR
isfifo(obj::DirEntry) =     (isunknown(obj) || islink(obj)) ? isfifo(joinpath(obj))      : obj.rawtype == UV_DIRENT_FIFO
issocket(obj::DirEntry) =   (isunknown(obj) || islink(obj)) ? issocket(joinpath(obj))    : obj.rawtype == UV_DIRENT_SOCKET
ischardev(obj::DirEntry) =  (isunknown(obj) || islink(obj)) ? ischardev(joinpath(obj))   : obj.rawtype == UV_DIRENT_CHAR
isblockdev(obj::DirEntry) = (isunknown(obj) || islink(obj)) ? isblockdev(joinpath(obj))  : obj.rawtype == UV_DIRENT_BLOCK
realpath(obj::DirEntry) = realpath(joinpath(obj))

```
-/
def basenameEntry (obj : DirEntry) : String := obj.name

def dirnameEntry (obj : DirEntry) : String := obj.dir

def joinpathEntry (obj : DirEntry) (args : List String) : M World String :=
  ops.joinpath ([dirnameEntry obj, basenameEntry obj] ++ args)

def islessEntry (a b : DirEntry) : M World Bool :=
  if dirnameEntry a == dirnameEntry b then ops.islessString (basenameEntry a) (basenameEntry b)
  else ops.islessString (dirnameEntry a) (dirnameEntry b)

def hashEntry (o : DirEntry) (h : U64) : M World U64 := do
  ops.hashString (dirnameEntry o) (← ops.hashString (basenameEntry o) (← ops.hashI32 o.rawtype h))

def eqEntry (a b : DirEntry) : Bool :=
  basenameEntry a == basenameEntry b && dirnameEntry a == dirnameEntry b && a.rawtype == b.rawtype

def isunknownEntry (obj : DirEntry) : Bool := obj.rawtype == uvDirentUnknown

def islinkEntry (obj : DirEntry) : M World Bool := do
  if isunknownEntry obj then islinkPath ops (← joinpathEntry ops obj [])
  else pure (obj.rawtype == uvDirentLink)

/-- `(isunknown(obj) || islink(obj)) ? pred(joinpath(obj)) : obj.rawtype == code`. -/
def entryTypeTest (obj : DirEntry) (pred : String → M World Bool) (code : I32) : M World Bool := do
  let fallBack ← if isunknownEntry obj then pure true else islinkEntry ops obj
  if fallBack then pred (← joinpathEntry ops obj []) else pure (obj.rawtype == code)

def isfileEntry (obj : DirEntry) : M World Bool :=
  entryTypeTest ops obj (fun path => isfilePath ops path) uvDirentFile

def isdirEntry (obj : DirEntry) : M World Bool :=
  entryTypeTest ops obj (fun path => isdirPath ops path) uvDirentDir

def isfifoEntry (obj : DirEntry) : M World Bool :=
  entryTypeTest ops obj (fun path => isfifoPath ops path) uvDirentFifo

def issocketEntry (obj : DirEntry) : M World Bool :=
  entryTypeTest ops obj (fun path => issocketPath ops path) uvDirentSocket

def ischardevEntry (obj : DirEntry) : M World Bool :=
  entryTypeTest ops obj (fun path => ischardevPath ops path) uvDirentChar

def isblockdevEntry (obj : DirEntry) : M World Bool :=
  entryTypeTest ops obj (fun path => isblockdevPath ops path) uvDirentBlock

def realpathEntry (obj : DirEntry) : M World String := do
  ops.realpath (← joinpathEntry ops obj [])

/-- The vector built by `_readdir`: `String[]` or `DirEntry[]`. -/
inductive ReaddirList where
  | names (values : List String)
  | entries (values : List DirEntry)

/--
Julia source: base/file.jl:1176-1208 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _readdir(dir::AbstractString; return_objects::Bool=false, join::Bool=false, sort::Bool=true)
    # Allocate space for uv_fs_t struct
    req = Libc.malloc(_sizeof_uv_fs)
    try
        err = ccall(:uv_fs_scandir, Int32, (Ptr{Cvoid}, Ptr{Cvoid}, Cstring, Cint, Ptr{Cvoid}),
                    C_NULL, req, dir, 0, C_NULL)
        err < 0 && uv_error("readdir($(repr(dir)))", err)

        # iterate the listing into entries
        entries = return_objects ? DirEntry[] : String[]
        ent = Ref{uv_dirent_t}()
        while Base.UV_EOF != ccall(:uv_fs_scandir_next, Cint, (Ptr{Cvoid}, Ptr{uv_dirent_t}), req, ent)
            name = unsafe_string(ent[].name)
            if return_objects
                rawtype = ent[].typ
                push!(entries, DirEntry(dir, name, rawtype))
            else
                push!(entries, join ? joinpath(dir, name) : name)
            end
        end

        # Clean up the request string
        uv_fs_req_cleanup(req)

        # sort entries unless opted out
        sort && sort!(entries)

        return entries
    finally
        Libc.free(req)
    end
end

```
-/
def readdirInternal (dir : String) (returnObjects join sort : Bool) : M World ReaddirList := do
  let req ← ops.mallocReq ()
  tryFinally (do
    let cdir ← cstr ops dir
    let err ← ops.uvFsScandir req cdir (JInt.lit .i32 0)
    if err.val < 0 then uvError ops ("readdir(" ++ (← ops.repr dir) ++ ")") err
    let initial := if returnObjects then ReaddirList.entries [] else ReaddirList.names []
    let ent ← ops.newDirent ()
    let entries ← whileLoop (fun (entries : ReaddirList) => do
      let r ← ops.uvFsScandirNext req ent
      if ops.uvEof == r then return Sum.inl entries
      let name ← ops.direntName ent
      if returnObjects then
        let rawtype ← ops.direntType ent
        match entries with
        | .entries values => return Sum.inr (.entries (values ++ [DirEntry.mk dir name rawtype]))
        | .names _ => throw (.jl (.methodError "convert"))
      else
        let value ← if join then ops.joinpath [dir, name] else pure name
        match entries with
        | .names values => return Sum.inr (.names (values ++ [value]))
        | .entries _ => throw (.jl (.methodError "convert"))) initial
    ops.reqCleanup req
    let entries ← if sort then
        match entries with
        | .names values => do pure (.names (← ops.sortBy ops.islessString values))
        | .entries values => do pure (.entries (← ops.sortBy (islessEntry ops) values))
      else pure entries
    pure entries) (ops.freeReq req)

def typeassertNames : ReaddirList → M World (List String)
  | .names values => pure values
  | .entries _ => throw (.foreignError "TypeError" "typeassert")

def typeassertEntries : ReaddirList → M World (List DirEntry)
  | .entries values => pure values
  | .names _ => throw (.foreignError "TypeError" "typeassert")

/--
Julia source: base/file.jl:1005-1083 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    readdir(dir::AbstractString=pwd();
        join::Bool = false,
        sort::Bool = true,
    )::Vector{String}

Return the names in the directory `dir` or the current working directory if not
given. When `join` is false, `readdir` returns just the names in the directory
as is; when `join` is true, it returns `joinpath(dir, name)` for each `name` so
that the returned strings are full paths. If you want to get absolute paths
back, call `readdir` with an absolute directory path and `join` set to true.

By default, `readdir` sorts the list of names it returns. If you want to skip
sorting the names and get them in the order that the file system lists them,
you can use `readdir(dir, sort=false)` to opt out of sorting.

See also: [`walkdir`](@ref).

!!! compat "Julia 1.4"
    The `join` and `sort` keyword arguments require at least Julia 1.4.

# Examples
```julia-repl
julia> cd("/home/JuliaUser/dev/julia")

julia> readdir()
30-element Vector{String}:
 ".appveyor.yml"
 ".git"
 ".gitattributes"
 ⋮
 "ui"
 "usr"
 "usr-staging"

julia> readdir(join=true)
30-element Vector{String}:
 "/home/JuliaUser/dev/julia/.appveyor.yml"
 "/home/JuliaUser/dev/julia/.git"
 "/home/JuliaUser/dev/julia/.gitattributes"
 ⋮
 "/home/JuliaUser/dev/julia/ui"
 "/home/JuliaUser/dev/julia/usr"
 "/home/JuliaUser/dev/julia/usr-staging"

julia> readdir("base")
145-element Vector{String}:
 ".gitignore"
 "Base.jl"
 "Enums.jl"
 ⋮
 "version_git.sh"
 "views.jl"
 "weakdict.jl"

julia> readdir("base", join=true)
145-element Vector{String}:
 "base/.gitignore"
 "base/Base.jl"
 "base/Enums.jl"
 ⋮
 "base/version_git.sh"
 "base/views.jl"
 "base/weakdict.jl"

julia> readdir(abspath("base"), join=true)
145-element Vector{String}:
 "/home/JuliaUser/dev/julia/base/.gitignore"
 "/home/JuliaUser/dev/julia/base/Base.jl"
 "/home/JuliaUser/dev/julia/base/Enums.jl"
 ⋮
 "/home/JuliaUser/dev/julia/base/version_git.sh"
 "/home/JuliaUser/dev/julia/base/views.jl"
 "/home/JuliaUser/dev/julia/base/weakdict.jl"
```
"""
readdir(; join::Bool=false, kwargs...) = readdir(join ? pwd() : "."; join, kwargs...)::Vector{String}
readdir(dir::AbstractString; kwargs...) = _readdir(dir; return_objects=false, kwargs...)::Vector{String}

````
-/
def readdir (dir : String) (join sort : Bool) : M World (List String) := do
  typeassertNames (← readdirInternal ops dir false join sort)

def readdirDefault (join sort : Bool) : M World (List String) := do
  let dir ← if join then pwd ops else pure "."
  readdir ops dir join sort

/--
Julia source: base/file.jl:1138-1175 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    readdir(dir::AbstractString, ::Type{DirEntry}; sort::Bool=true)::Vector{DirEntry}
    readdir(::Type{DirEntry}; sort::Bool=true)::Vector{DirEntry}
    readdir(entry::DirEntry, ::Type{DirEntry}; sort::Bool=true)::Vector{DirEntry}
    readdir(entry::DirEntry; join::Bool=false, sort::Bool=true)::Vector{String}

Return a vector of [`DirEntry`](@ref) objects representing the contents of the directory `dir`,
or the current working directory if not given. If `sort` is true, the returned vector is
sorted by name.

The element type is selected by the trailing `DirEntry` type argument (mirroring
[`read(io, String)`](@ref)): include it to get [`DirEntry`](@ref) objects (which carry the
type of each entry as determined during the directory scan, so [`isfile`](@ref),
[`isdir`](@ref), etc. can be called without further `stat` calls), or omit it to get a
`Vector{String}` of names — independent of whether the directory was specified as an
`AbstractString` or a `DirEntry`. For some filesystems the type of the entry cannot be
determined without a `stat` call; in those cases the `rawtype` field of the
[`DirEntry`](@ref) is 0 (`UV_DIRENT_UNKNOWN`) and the predicates fall back to a `stat` call.

# Examples
```julia
for entry in readdir(".", DirEntry)
    if isfile(entry)
        println("\$(basename(entry)) is a file with path \$(joinpath(entry))")
        continue
    end
    isdir(entry) || continue
    for entry2 in readdir(entry, DirEntry)
        ...
    end
end
```
"""
readdir(dir::AbstractString, ::Type{DirEntry}; sort::Bool=true) = _readdir(dir; return_objects=true, sort)::Vector{DirEntry}
readdir(::Type{DirEntry}; sort::Bool=true) = readdir(pwd(), DirEntry; sort)::Vector{DirEntry}
readdir(entry::DirEntry, ::Type{DirEntry}; sort::Bool=true) = readdir(joinpath(entry), DirEntry; sort)::Vector{DirEntry}
readdir(entry::DirEntry; kwargs...) = readdir(joinpath(entry); kwargs...)::Vector{String}

````
-/
def readdirEntries (dir : String) (sort : Bool) : M World (List DirEntry) := do
  typeassertEntries (← readdirInternal ops dir true false sort)

def readdirEntriesCwd (sort : Bool) : M World (List DirEntry) := do
  readdirEntries ops (← pwd ops) sort

def readdirEntryEntries (entry : DirEntry) (sort : Bool) : M World (List DirEntry) := do
  readdirEntries ops (← joinpathEntry ops entry []) sort

def readdirEntryNames (entry : DirEntry) (join sort : Bool) : M World (List String) := do
  readdir ops (← joinpathEntry ops entry []) join sort

/-- The element type `T` of a `DirEntryIterator{T}`. -/
inductive Eltype where
  | string
  | dirEntry
  | other (name : String)
  deriving DecidableEq

/--
Julia source: base/file.jl:1209-1240 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    DirEntryIterator{T}

A stateful, single-pass iterator over the entries of a directory, yielding
either filename `String`s or [`DirEntry`](@ref) objects depending on the
element type `T`. Created by [`eachentry`](@ref).

The underlying directory handle is opened lazily on the first call to
`iterate` (via `uv_fs_opendir`) and is released when iteration reaches
end-of-directory, when [`close`](@ref) is called, or by a finalizer.
Entries are streamed one at a time from the operating system; the full
listing is never materialized in memory. For deterministic cleanup on
very large directories, prefer the do-block form of `eachentry`.

A `DirEntryIterator` is single-consumer: do not iterate or close it from
multiple tasks concurrently. Calling `close` from a finalizer while the
owning task has finished iterating is safe.
"""
mutable struct DirEntryIterator{T}
    const dir::String
    # Yield joinpath(dir, name) instead of the bare name (String eltype only)
    const join::Bool
    # Opaque uv_dir_t*, C_NULL before opening and after closing. Whoever swaps it to C_NULL closes it.
    @atomic uvdir::Ptr{Cvoid}
    const status::RefValue{Cint}
    closed::Bool
    function DirEntryIterator{T}(dir::AbstractString, join::Bool=false) where {T}
        T === String || T === DirEntry || throw(ArgumentError("element type must be String or DirEntry"))
        finalizer(close, new{T}(String(dir), join, C_NULL, RefValue{Cint}(0), false))
    end
end

```
-/
structure DirEntryIterator (Obj : Type) where
  object : Obj
  eltype : Eltype
  dir : String
  join : Bool

def DirEntryIterator.new (eltype : Eltype) (dir : String) (join : Bool) :
    M World (DirEntryIterator IterObj) := do
  if !(eltype == .string || eltype == .dirEntry) then
    throw (argumentError "element type must be String or DirEntry")
  pure ⟨← ops.newIterator dir join, eltype, dir, join⟩

/--
Julia source: base/file.jl:1241-1255 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _eachentry_open!(it::DirEntryIterator)
    it.uvdir == C_NULL || return
    it.closed && throw(ArgumentError("DirEntryIterator has already been consumed"))
    dir_out = Ref{Ptr{Cvoid}}(C_NULL)
    err = ccall(:jl_uv_fs_opendir, Cint,
                (Cstring, Ptr{Ptr{Cvoid}}),
                it.dir, dir_out)
    if err < 0
        it.closed = true
        uv_error("eachentry($(repr(it.dir)))", err)
    end
    @atomic it.uvdir = dir_out[]
    return
end

```
-/
def eachentryOpen (it : DirEntryIterator IterObj) : M World Unit := do
  if !ops.isNullDir (← ops.iterUvdir it.object) then return ()
  if ← ops.iterClosed it.object then
    throw (argumentError "DirEntryIterator has already been consumed")
  let cdir ← cstr ops it.dir
  let (err, dirOut) ← ops.uvFsOpendir cdir
  if err.val < 0 then
    ops.iterSetClosed it.object true
    uvError ops ("eachentry(" ++ (← ops.repr it.dir) ++ ")") err
  ops.iterSetUvdir it.object dirOut

/--
Julia source: base/file.jl:1256-1265 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.close(it::DirEntryIterator)
    # Atomically claim the dir pointer so a concurrent finalizer cannot double-free.
    uvdir = @atomicswap it.uvdir = C_NULL
    if uvdir != C_NULL
        ccall(:jl_uv_fs_closedir, Cint, (Ptr{Cvoid},), uvdir)
    end
    it.closed = true
    return
end

```
-/
def closeIterator (it : DirEntryIterator IterObj) : M World Unit := do
  let uvdir ← ops.iterSwapUvdir it.object ops.nullDir
  if !ops.isNullDir uvdir then
    let _ ← ops.uvFsClosedir uvdir
  ops.iterSetClosed it.object true

/-- `Base.IteratorSize` values. -/
inductive IteratorSizeTrait where
  | sizeUnknown

/--
Julia source: base/file.jl:1266-1269 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.IteratorSize(::Type{<:DirEntryIterator}) = Base.SizeUnknown()
Base.eltype(::Type{DirEntryIterator{T}}) where {T} = T
Base.isdone(it::DirEntryIterator, _=nothing) = it.closed

```
-/
def iteratorSize : IteratorSizeTrait := .sizeUnknown

def iteratorEltype (eltype : Eltype) : Eltype := eltype

def isdoneIterator (it : DirEntryIterator IterObj) : M World Bool := ops.iterClosed it.object

/-- A value produced by a `DirEntryIterator`. -/
inductive DirValue where
  | name (value : String)
  | entry (value : DirEntry)

/--
Julia source: base/file.jl:1270-1284 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.iterate(it::DirEntryIterator{T}, _=nothing) where {T}
    _eachentry_open!(it)
    name = ccall(:jl_uv_fs_readdir1, Any, (Ptr{Cvoid}, Ptr{Cint}), it.uvdir, it.status)
    if name === nothing
        err = it.status[]
        close(it)
        err < 0 && uv_error("eachentry($(repr(it.dir)))", err)
        return nothing
    end
    name = name::String
    value = T === DirEntry ? DirEntry(it.dir, name, it.status[]) :
            it.join ? joinpath(it.dir, name) : name
    return value, nothing
end

```
-/
def iterateIterator (it : DirEntryIterator IterObj) : M World (Option DirValue) := do
  eachentryOpen ops it
  let name ← ops.uvFsReaddir1 (← ops.iterUvdir it.object) it.object
  match name with
  | none =>
    let err ← ops.iterStatus it.object
    closeIterator ops it
    if err.val < 0 then uvError ops ("eachentry(" ++ (← ops.repr it.dir) ++ ")") err
    pure none
  | some name =>
    if it.eltype == .dirEntry then
      pure (some (.entry (DirEntry.mk it.dir name (← ops.iterStatus it.object))))
    else if it.join then pure (some (.name (← ops.joinpath [it.dir, name])))
    else pure (some (.name name))

/-- The directory argument of `eachentry(f, dir; ...)`. -/
inductive DirArg where
  | path (value : String)
  | entry (value : DirEntry)

/--
Julia source: base/file.jl:1285-1352 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    eachentry(dir::AbstractString=pwd(); join::Bool=false)::DirEntryIterator{String}
    eachentry(entry::DirEntry; join::Bool=false)::DirEntryIterator{String}
    eachentry(dir::AbstractString, ::Type{DirEntry})::DirEntryIterator{DirEntry}
    eachentry(::Type{DirEntry})::DirEntryIterator{DirEntry}
    eachentry(entry::DirEntry, ::Type{DirEntry})::DirEntryIterator{DirEntry}
    eachentry(f, dir[, ::Type{DirEntry}]; kwargs...) -> f(::DirEntryIterator)

Return a stateful, single-pass iterator over the contents of the directory `dir`
(or the current working directory if not given), without first materializing the
full listing. Useful for very large directories or when iteration may be
short-circuited (e.g. with `break` or [`Iterators.take`](@ref)).

By default the iterator yields filename `String`s, matching [`readdir`](@ref);
if `join` is true it yields `joinpath(dir, name)` for each name instead.
Pass `DirEntry` as the trailing type argument to yield [`DirEntry`](@ref)
objects, which carry the entry type as cached at scan time so [`isfile`](@ref),
[`isdir`](@ref), etc. can be checked without further `stat` calls (the full
path of a `DirEntry` is available via `joinpath(entry)`, so there is no `join`
keyword for that form, as with `readdir(dir, DirEntry)`).

Unlike [`readdir`](@ref), the entries are returned in filesystem order (not
sorted) and the iterator can only be traversed once. The do-block form ensures
the underlying directory handle is released as soon as `f` returns; otherwise
cleanup happens at end-of-iteration, on [`close`](@ref), or via a finalizer.

See also [`readdir`](@ref), [`DirEntry`](@ref), [`walkdir`](@ref).

!!! compat "Julia 1.14"
    `eachentry` requires Julia 1.14 or later.

# Examples
```julia
# short-circuit a huge directory
for entry in eachentry("/very/large/dir", DirEntry)
    isfile(entry) && basename(entry) == "needle.txt" && break
end

# deterministic cleanup
eachentry("/very/large/dir") do names
    for name in names
        ...
    end
end
```
"""
eachentry(dir::AbstractString=pwd(); join::Bool=false) = DirEntryIterator{String}(dir, join)
eachentry(entry::DirEntry; join::Bool=false) = DirEntryIterator{String}(joinpath(entry), join)
eachentry(dir::AbstractString, ::Type{DirEntry}) = DirEntryIterator{DirEntry}(dir)
eachentry(::Type{DirEntry}) = DirEntryIterator{DirEntry}(pwd())
eachentry(entry::DirEntry, ::Type{DirEntry}) = DirEntryIterator{DirEntry}(joinpath(entry))
function eachentry(f, dir; join::Bool=false)
    it = eachentry(dir; join)
    try
        return f(it)
    finally
        close(it)
    end
end
function eachentry(f, dir, ::Type{DirEntry})
    it = eachentry(dir, DirEntry)
    try
        return f(it)
    finally
        close(it)
    end
end

````
-/
def eachentry (dir : String) (join : Bool) : M World (DirEntryIterator IterObj) :=
  DirEntryIterator.new ops .string dir join

def eachentryOfEntry (entry : DirEntry) (join : Bool) : M World (DirEntryIterator IterObj) := do
  DirEntryIterator.new ops .string (← joinpathEntry ops entry []) join

def eachentryEntries (dir : String) : M World (DirEntryIterator IterObj) :=
  DirEntryIterator.new ops .dirEntry dir false

def eachentryEntriesCwd : M World (DirEntryIterator IterObj) := do
  DirEntryIterator.new ops .dirEntry (← pwd ops) false

def eachentryEntryEntries (entry : DirEntry) : M World (DirEntryIterator IterObj) := do
  DirEntryIterator.new ops .dirEntry (← joinpathEntry ops entry []) false

def eachentryWith {A : Type} (f : DirEntryIterator IterObj → M World A) (dir : DirArg)
    (join : Bool) : M World A := do
  let it ← match dir with
    | .path p => eachentry ops p join
    | .entry e => eachentryOfEntry ops e join
  tryFinally (f it) (closeIterator ops it)

def eachentryWithEntries {A : Type} (f : DirEntryIterator IterObj → M World A) (dir : DirArg) :
    M World A := do
  let it ← match dir with
    | .path p => eachentryEntries ops p
    | .entry e => eachentryEntryEntries ops e
  tryFinally (f it) (closeIterator ops it)

/-- `tryf(f, p)` inside `_walkdir`: `nothing` after an `IOError`, which `onerror` handles; an
exception from `onerror` closes the channel with it. -/
def walkTry {A B : Type} (chnl : Chan) (onerror : Error → M World Unit) (f : A → M World B) (x : A) :
    M World (Option B) :=
  tryCatchM (do pure (some (← f x))) (fun err => do
    if !isIOError ops err then throw err
    tryCatchM (onerror err) (fun err2 => ops.channelClose chnl err2)
    pure none)

/--
Julia source: base/file.jl:1408-1444 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _walkdir(chnl, path, topdown, follow_symlinks, onerror)
    tryf(f, p) = try
            f(p)
        catch err
            isa(err, IOError) || rethrow()
            try
                onerror(err)
            catch err2
                close(chnl, err2)
            end
            return
        end
    entries = tryf(p -> readdir(p, DirEntry), path)
    entries === nothing && return
    dirs = Vector{String}()
    files = Vector{String}()
    for entry in entries
        # If we're not following symlinks, then treat all symlinks as files
        if (!follow_symlinks && something(tryf(islink, entry), true)) || !something(tryf(isdir, entry), false)
            push!(files, basename(entry))
        else
            push!(dirs, basename(entry))
        end
    end

    if topdown
        push!(chnl, (path, dirs, files))
    end
    for dir in dirs
        _walkdir(chnl, joinpath(path, dir), topdown, follow_symlinks, onerror)
    end
    if !topdown
        push!(chnl, (path, dirs, files))
    end
    nothing
end

```
-/
def walkdirInner (chnl : Chan) (path : String) (topdown followSymlinks : Bool)
    (onerror : Error → M World Unit) : M World Unit := do
  let entries? ← walkTry ops chnl onerror (fun p => readdirEntries ops p true) path
  match entries? with
  | none => pure ()
  | some entries => do
    let mut dirs : List String := []
    let mut files : List String := []
    for entry in entries do
      let linkAsFile ← if !followSymlinks then do
          pure ((← walkTry ops chnl onerror (islinkEntry ops) entry).getD true)
        else pure false
      let asFile ← if linkAsFile then pure true else do
        pure !((← walkTry ops chnl onerror (isdirEntry ops) entry).getD false)
      if asFile then files := files ++ [basenameEntry entry]
      else dirs := dirs ++ [basenameEntry entry]
    if topdown then ops.channelPush chnl (path, dirs, files)
    for dir in dirs do
      walkdirInner chnl (← ops.joinpath [path, dir]) topdown followSymlinks onerror
    if !topdown then ops.channelPush chnl (path, dirs, files)
partial_fixpoint

/--
Julia source: base/file.jl:1353-1407 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    walkdir(dir = pwd(); topdown=true, follow_symlinks=false, onerror=throw)

Return an iterator that walks the directory tree of a directory.

The iterator returns a tuple containing `(path, dirs, files)`.
Each iteration `path` will change to the next directory in the tree;
then `dirs` and `files` will be vectors containing the directories and files
in the current `path` directory.
The directory tree can be traversed top-down or bottom-up.
If `walkdir` or `stat` encounters a `IOError` it will rethrow the error by default.
A custom error handling function can be provided through `onerror` keyword argument.
`onerror` is called with a `IOError` as argument.
The returned iterator is stateful so when accessed repeatedly each access will
resume where the last left off, like [`Iterators.Stateful`](@ref).

See also: [`readdir`](@ref).

!!! compat "Julia 1.12"
    `pwd()` as the default directory was added in Julia 1.12.

# Examples
```julia
for (path, dirs, files) in walkdir(".")
    println("Directories in \$path")
    for dir in dirs
        println(joinpath(path, dir)) # path to directories
    end
    println("Files in \$path")
    for file in files
        println(joinpath(path, file)) # path to files
    end
end
```

```jldoctest; setup = :(prevdir = pwd(); tmpdir = mktempdir(); cd(tmpdir)), teardown = :(cd(prevdir); rm(tmpdir, recursive=true))
julia> mkpath("my/test/dir");

julia> itr = walkdir("my");

julia> (path, dirs, files) = first(itr)
("my", ["test"], String[])

julia> (path, dirs, files) = first(itr)
("my/test", ["dir"], String[])

julia> (path, dirs, files) = first(itr)
("my/test/dir", String[], String[])
```
"""
function walkdir(path = pwd(); topdown=true, follow_symlinks=false, onerror=throw)
    return Channel{Tuple{String,Vector{String},Vector{String}}}(chnl ->
        _walkdir(chnl, path, topdown, follow_symlinks, onerror))
end

````
-/
def walkdir (path : String) (topdown followSymlinks : Bool) (onerror : Error → M World Unit) :
    M World Chan :=
  ops.newChannel (fun chnl => walkdirInner ops chnl path topdown followSymlinks onerror)

def walkdirDefault (topdown followSymlinks : Bool) (onerror : Error → M World Unit) :
    M World Chan := do
  walkdir ops (← pwd ops) topdown followSymlinks onerror

/--
Julia source: base/file.jl:1622-1647 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    chmod(path::AbstractString, mode::Integer; recursive::Bool=false)

Change the permissions mode of `path` to `mode`. Only integer `mode`s (e.g. `0o777`) are
currently supported. If `recursive=true` and the path is a directory all permissions in
that directory will be recursively changed.
Return `path`.

!!! note
     Prior to Julia 1.6, this did not correctly manipulate filesystem ACLs
     on Windows, therefore it would only set read-only bits on files.  It
     now is able to manipulate ACLs.
"""
function chmod(path::AbstractString, mode::Integer; recursive::Bool=false)
    err = ccall(:jl_fs_chmod, Int32, (Cstring, Cint), path, mode)
    err < 0 && uv_error("chmod($(repr(path)), 0o$(string(mode, base=8)))", err)
    if recursive && isdir(path)
        for p in readdir(path)
            if !islink(joinpath(path, p))
                chmod(joinpath(path, p), mode, recursive=true)
            end
        end
    end
    path
end

```
-/
def chmod {N : Type} (intOps : IntegerOps World N) (path : String) (mode : N) (recursive : Bool) :
    M World String := do
  let cmode ← toCint intOps mode
  let cpath ← cstr ops path
  let err ← ops.fsChmod cpath cmode
  if err.val < 0 then
    uvError ops ("chmod(" ++ (← ops.repr path) ++ ", 0o" ++ (← intOps.string mode 8) ++ ")") err
  let descend ← if recursive then isdirPath ops path else pure false
  if descend then
    for p in (← readdir ops path false true) do
      if !(← islinkPath ops (← ops.joinpath [path, p])) then
        let _ ← chmod intOps (← ops.joinpath [path, p]) mode true
  pure path
partial_fixpoint

/--
Julia source: base/file.jl:1648-1661 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    chown(path::AbstractString, owner::Integer, group::Integer=-1)

Change the owner and/or group of `path` to `owner` and/or `group`. If the value entered for `owner` or `group`
is `-1` the corresponding ID will not change. Only integer `owner`s and `group`s are currently supported.
Return `path`.
"""
function chown(path::AbstractString, owner::Integer, group::Integer=-1)
    err = ccall(:jl_fs_chown, Int32, (Cstring, Cint, Cint), path, owner, group)
    err < 0 && uv_error("chown($(repr(path)), $owner, $group)", err)
    path
end


```
-/
def chown {N G : Type} (ownerOps : IntegerOps World N) (groupOps : IntegerOps World G)
    (path : String) (owner : N) (group : G) : M World String := do
  let cowner ← toCint ownerOps owner
  let cgroup ← toCint groupOps group
  let cpath ← cstr ops path
  let err ← ops.fsChown cpath cowner cgroup
  if err.val < 0 then
    uvError ops ("chown(" ++ (← ops.repr path) ++ ", " ++ (← ownerOps.display owner) ++ ", " ++
      (← groupOps.display group) ++ ")") err
  pure path

/-- `chown(path, owner)`: the default `group = -1`. -/
def chownDefault {N : Type} (ownerOps : IntegerOps World N) (path : String) (owner : N) :
    M World String :=
  chown ops ownerOps ops.i64Ops path owner (JInt.lit .i64 (-1))

/--
Julia source: base/file.jl:597-633 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    tempdir()

Get the path of the temporary directory. On Windows, `tempdir()` uses the first environment
variable found in the ordered list `TMP`, `TEMP`, `USERPROFILE`. On all other operating
systems, `tempdir()` uses the first environment variable found in the ordered list `TMPDIR`,
`TMP`, `TEMP`, and `TEMPDIR`. If none of these are found, the path `"/tmp"` is used.
"""
function tempdir()
    buf = Base.StringVector(AVG_PATH - 1) # space for null-terminator implied by StringVector
    sz = RefValue{Csize_t}(length(buf) + 1) # total buffer size including null
    while true
        rc = ccall(:uv_os_tmpdir, Cint, (Ptr{UInt8}, Ptr{Csize_t}), buf, sz)
        if rc == 0
            resize!(buf, sz[])
            break
        elseif rc == Base.UV_ENOBUFS
            resize!(buf, sz[] - 1)  # space for null-terminator implied by StringVector
        else
            uv_error("tempdir()", rc)
        end
    end
    tempdir = String(buf)
    try
        s = stat(tempdir)
        if !ispath(s)
            @warn "tempdir path does not exist" tempdir
        elseif !isdir(s)
            @warn "tempdir path is not a directory" tempdir
        end
    catch ex
        ex isa IOError || ex isa SystemError || rethrow()
        @warn "accessing tempdir path failed" _exception=ex
    end
    return tempdir
end

```
-/
def tempdirFn : M World String := do
  let buf ← ops.newStringVector (JuliaLean.base.int.sub ops.avgPath (JInt.lit .i64 1))
  let len ← ops.stringVectorLength buf
  let size ← JuliaLean.base.io.liftJl
    (JInt.convert "convert" .u64 (JuliaLean.base.int.add len (JInt.lit .i64 1)).val)
  let sz ← ops.newSizeRef size
  whileLoop (fun (_ : Unit) => do
    let rc ← ops.uvOsTmpdir buf sz
    if rc.val == 0 then
      ops.resizeStringVector buf (← ops.getSizeRef sz)
      return Sum.inl ()
    else if rc == ops.uvEnobufs then
      ops.resizeStringVector buf (JuliaLean.base.int.sub (← ops.getSizeRef sz) (JInt.lit .u64 1))
      return Sum.inr ()
    else
      uvError ops "tempdir()" rc
      return Sum.inr ()) ()
  let tempdir ← ops.stringVectorString buf
  tryCatchM (do
      let s ← JuliaLean.base.stat.statPath ops.stat tempdir
      if !JuliaLean.base.stat.isPathStat s then
        ops.logWarn "tempdir path does not exist"
      else if !JuliaLean.base.stat.isDirectory s then
        ops.logWarn "tempdir path is not a directory")
    (fun ex => do
      if !(isIOError ops ex || ops.isSystemError ex) then throw ex
      ops.logWarn "accessing tempdir path failed")
  pure tempdir

/--
Julia source: base/file.jl:258-261 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Files that were requested to be deleted but can't be by the current process,
# i.e. loaded DLLs on Windows, are listed in the directory below
delayed_delete_ref() = joinpath(tempdir(), "julia_delayed_deletes_ref")

```
-/
def delayedDeleteRef : M World String := do
  ops.joinpath [← tempdirFn ops, "julia_delayed_deletes_ref"]

/--
Julia source: base/file.jl:765-766 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const temp_prefix = "jl_"

```
-/
def tempPrefix : String := "jl_"

/-- The bytes of `b"0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"`. -/
def filenameChars : List Byte :=
  ("0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ".toList.map
    (fun c => JInt.lit .u8 c.toNat))

/--
Julia source: base/file.jl:767-776 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Use `Libc.rand()` to generate random strings
function _rand_filename(len = 10)
    slug = Base.StringVector(len)
    chars = b"0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
    for i = 1:len
        slug[i] = chars[(Libc.rand() % length(chars)) + 1]
    end
    return String(slug)
end

```
-/
def randFilename (len : I64) : M World String := do
  let slug ← ops.newStringVector len
  for i in List.range len.val.toNat do
    let r ← ops.libcRand ()
    let index := (r.val % (filenameChars.length : Int)) + 1
    let byte ← match filenameChars[(index - 1).toNat]? with
      | some b => pure b
      | none => throw (.jl .boundsError)
    ops.stringVectorSet slug (JInt.lit .i64 (i + 1)) byte
  ops.stringVectorString slug

/-- `for _ in 1:max_tries` in `_tempname`: `remaining` iterations left. -/
def tempnameTries (pfx suffix : String) : Nat → M World (Option String)
  | 0 => pure none
  | remaining + 1 => do
    let filename := pfx ++ (← randFilename ops (JInt.lit .i64 10)) ++ suffix
    if ← ispathPath ops filename then tempnameTries pfx suffix remaining
    else pure (some filename)

/--
Julia source: base/file.jl:785-805 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _tempname(parent::AbstractString, suffix::AbstractString, max_tries::Int = 100)
    isdir(parent) || throw(ArgumentError("$(repr(parent)) is not a directory"))

    prefix = joinpath(parent, temp_prefix)
    filename = nothing
    for _ in 1:max_tries
        filename = string(prefix, _rand_filename(), suffix)
        if ispath(filename)
            filename = nothing
        else
            break
        end
    end

    if filename === nothing
        error("tempname: max_tries exhausted")
    end

    return filename
end

```
-/
def tempnameInternal (parent suffix : String) (maxTries : I64) : M World String := do
  if !(← isdirPath ops parent) then
    throw (argumentError ((← ops.repr parent) ++ " is not a directory"))
  let pfx ← ops.joinpath [parent, tempPrefix]
  match ← tempnameTries ops pfx suffix maxTries.val.toNat with
  | some filename => pure filename
  | none => throw (.errorException "tempname: max_tries exhausted")

/--
Julia source: base/file.jl:806-824 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
if Sys.iswindows()
# While this isn't a true analog of `mkstemp`, it _does_ create an
# empty file for us, ensuring that other simultaneous calls to
# `_win_mkstemp()` won't collide, so it's a better name for the
# function than `tempname()`.
function _win_mkstemp(temppath::AbstractString)
    tempp = cwstring(temppath)
    temppfx = cwstring(temp_prefix)
    tname = Vector{UInt16}(undef, 32767)
    uunique = ccall(:GetTempFileNameW, stdcall, UInt32,
                    (Ptr{UInt16}, Ptr{UInt16}, UInt32, Ptr{UInt16}),
                    tempp, temppfx, UInt32(0), tname)
    windowserror("GetTempFileName", uunique == 0)
    lentname = something(findfirst(iszero, tname))
    @assert lentname > 0 "unexpected index"
    resize!(tname, lentname - 1)
    return transcode(String, tname)
end

```
-/
def winMkstemp (temppath : String) : M World String := do
  let tempp ← ops.cwstring temppath
  let temppfx ← ops.cwstring tempPrefix
  let (uunique, tname) ← ops.getTempFileName tempp temppfx (JInt.lit .u32 0)
  if uunique.val == 0 then
    let code ← ops.getLastError ()
    JuliaLean.base.filesystem.eliminateEmpty (ops.stat.errors.windowsError "GetTempFileName" code)
  let lentname ← match tname.findIdx? (fun c => c.val == 0) with
    | some i => pure (i + 1)
    | none => throw (argumentError "No value arguments present")
  if !(lentname > 0) then throw (.foreignError "AssertionError" "unexpected index")
  ops.utf16String (tname.take (lentname - 1))

/--
Julia source: base/file.jl:328-344 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# Loaded DLLs cannot be deleted on Windows, even with posix delete mode but they can be renamed.
# delayed_delete_dll(path) does so temporarily, until later cleanup by Pkg.gc().
function delayed_delete_dll(path)
    # in-use DLL must be kept on the same drive
    temp_path = _tempname(abspath(dirname(path)), string("_", basename(path)))
    @debug "Could not delete DLL most likely because it is loaded, moving to a temporary path" path temp_path
    mkpath(delayed_delete_ref())
    io = Base.open(_win_mkstemp(delayed_delete_ref()), "r+")
    try
        print(io, temp_path) # record the temporary path for Pkg.gc()
    finally
        close(io)
    end
    rename(path, temp_path) # do not call mv which could recursively call rm(path)
end

```
-/
def delayedDeleteDll (path : String) : M World String := do
  let tempPath ← tempnameInternal ops (← ops.abspath (← ops.dirname path))
    ("_" ++ (← ops.basename path)) (JInt.lit .i64 100)
  ops.logDebug "Could not delete DLL most likely because it is loaded, moving to a temporary path"
  let _ ← mkpath ops ops.i64Ops (← delayedDeleteRef ops) (JInt.lit .i64 0o777)
  let io ← ops.openMode (← winMkstemp ops (← delayedDeleteRef ops)) "r+"
  tryFinally (ops.printString io tempPath) (ops.closeStream io)
  rename ops path tempPath

/--
Julia source: base/file.jl:262-327 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    rm(path::AbstractString; force::Bool=false, recursive::Bool=false)

Delete the file, link, or empty directory at the given path. If `force=true` is passed, a
non-existing path is not treated as error. If `recursive=true` is passed and the path is a
directory, then all contents are removed recursively.

# Examples
```jldoctest
julia> mkpath("my/test/dir");

julia> rm("my", recursive=true)

julia> rm("this_file_does_not_exist", force=true)

julia> rm("this_file_does_not_exist")
ERROR: IOError: unlink("this_file_does_not_exist"): no such file or directory (ENOENT)
Stacktrace:
[...]
```
"""
function rm(path::AbstractString; force::Bool=false, recursive::Bool=false, allow_delayed_delete::Bool=true)
    # allow_delayed_delete is used by Pkg.gc() but is otherwise not part of the public API
    if islink(path) || !isdir(path)
        try
            unlink(path)
        catch err
            if isa(err, IOError)
                force && err.code==Base.UV_ENOENT && return
                @static if Sys.iswindows()
                    if allow_delayed_delete && err.code==Base.UV_EACCES && endswith(path, ".dll")
                        delayed_delete_dll(path)
                        return
                    end
                end
            end
            rethrow()
        end
    else
        if recursive
            try
                for p in readdir(path)
                    try
                        rm(joinpath(path, p), force=force, recursive=true)
                    catch err
                        (isa(err, IOError) && err.code==Base.UV_EACCES) || rethrow()
                    end
                end
            catch err
                (isa(err, IOError) && err.code==Base.UV_EACCES) || rethrow()
            end
        end
        req = Libc.malloc(_sizeof_uv_fs)
        try
            ret = ccall(:uv_fs_rmdir, Cint, (Ptr{Cvoid}, Ptr{Cvoid}, Cstring, Ptr{Cvoid}), C_NULL, req, path, C_NULL)
            uv_fs_req_cleanup(req)
            if ret < 0 && !(force && ret == Base.UV_ENOENT)
                uv_error("rm($(repr(path)))", ret)
            end
            nothing
        finally
            Libc.free(req)
        end
    end
end

````
-/
def rm (path : String) (force recursive allowDelayedDelete : Bool) : M World Unit := do
  let unlinkFirst ← do
    if ← islinkPath ops path then pure true
    else pure !(← isdirPath ops path)
  if unlinkFirst then
    tryCatchM (unlink ops path) (fun err => do
      match ops.ioErrorCode err with
      | some code =>
        if force && code == ops.uvEnoent then return ()
        if ops.isWindows then
          if allowDelayedDelete && code == ops.uvEacces && path.endsWith ".dll" then
            let _ ← delayedDeleteDll ops path
            return ()
        throw err
      | none => throw err)
  else
    if recursive then
      tryCatchM (do
          for p in (← readdir ops path false true) do
            tryCatchM (do rm (← ops.joinpath [path, p]) force true true)
              (fun err => if isIOErrorCode ops err ops.uvEacces then pure () else throw err))
        (fun err => if isIOErrorCode ops err ops.uvEacces then pure () else throw err)
    let req ← ops.mallocReq ()
    tryFinally (do
      let cpath ← cstr ops path
      let ret ← ops.uvFsRmdir req cpath
      ops.reqCleanup req
      if ret.val < 0 && !(force && ret == ops.uvEnoent) then
        uvError ops ("rm(" ++ (← ops.repr path) ++ ")") ret
      pure ()) (ops.freeReq req)
partial_fixpoint

/--
Julia source: base/file.jl:345-358 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# The absolute path with symlinks resolved in the parts that exist. With `keep_link`, a final
# symlink is kept, for operations that act on the link rather than its target. `..` is left
# for the filesystem to resolve, since after a symlink it does not undo the previous part.
function _resolved_path(path::AbstractString, keep_link::Bool)
    isabspath(path) || (path = joinpath(pwd(), path))
    if ispath(path)
        keep_link && islink(path) || return realpath(path)
        return joinpath(realpath(dirname(path)), basename(path))
    end
    parent = dirname(path)
    parent == path && return path
    return normpath(joinpath(_resolved_path(parent, false), basename(path)))
end

```
-/
def resolvedPath (path : String) (keepLink : Bool) : M World String := do
  let path ← do
    if ← ops.isabspath path then pure path
    else ops.joinpath [← pwd ops, path]
  if ← ispathPath ops path then
    let keep ← if keepLink then islinkPath ops path else pure false
    if !keep then return (← ops.realpath path)
    return (← ops.joinpath [← ops.realpath (← ops.dirname path), ← ops.basename path])
  let parent ← ops.dirname path
  if parent == path then return path
  ops.normpath (← ops.joinpath [← resolvedPath parent false, ← ops.basename path])
partial_fixpoint

/--
Julia source: base/file.jl:359-361 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_is_within(inner::AbstractString, outer::AbstractString) =
    inner == outer || startswith(inner, joinpath(outer, ""))

```
-/
def isWithin (inner outer : String) : M World Bool := do
  if inner == outer then pure true
  else pure (inner.startsWith (← ops.joinpath [outer, ""]))

/--
Julia source: base/file.jl:362-392 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# The following use Unix command line facilities
function checkfor_mv_cp_cptree(src::AbstractString, dst::AbstractString, txt::AbstractString;
                               force::Bool=false, follow_symlinks::Bool=false)
    src_path = _resolved_path(src, !follow_symlinks)
    dst_path = _resolved_path(dst, true)
    if isdir(src) && (follow_symlinks || !islink(src)) && dst_path != src_path && _is_within(dst_path, src_path)
        throw(ArgumentError("'$dst' is inside '$src'; a directory cannot be moved or copied into itself."))
    end
    if ispath(dst)
        if force
            # Check for issue when: (src == dst) or when one is a link to the other
            # https://github.com/JuliaLang/julia/pull/11172#issuecomment-100391076
            if Base.samefile(src, dst)
                abs_src = islink(src) ? abspath(readlink(src)) : abspath(src)
                abs_dst = islink(dst) ? abspath(readlink(dst)) : abspath(dst)
                throw(ArgumentError(string("'src' and 'dst' refer to the same file/dir. ",
                                           "This is not supported.\n  ",
                                           "`src` refers to: $(abs_src)\n  ",
                                           "`dst` refers to: $(abs_dst)\n")))
            end
            if _is_within(src_path, dst_path)
                throw(ArgumentError("'$dst' contains '$src', so it cannot be removed before $(txt)."))
            end
            rm(dst; recursive=true, force=true)
        else
            throw(ArgumentError(string("'$dst' exists. `force=true` ",
                                       "is required to remove '$dst' before $(txt).")))
        end
    end
end

```
-/
def checkforMvCpCptree (src dst txt : String) (force followSymlinks : Bool) : M World Unit := do
  let srcPath ← resolvedPath ops src (!followSymlinks)
  let dstPath ← resolvedPath ops dst true
  let inside ← do
    if !(← isdirPath ops src) then pure false
    else do
      let linkOk ← do
        if followSymlinks then pure true
        else pure !(← islinkPath ops src)
      if !linkOk then pure false
      else if dstPath == srcPath then pure false
      else isWithin ops dstPath srcPath
  if inside then
    throw (argumentError ("'" ++ dst ++ "' is inside '" ++ src ++
      "'; a directory cannot be moved or copied into itself."))
  if ← ispathPath ops dst then
    if force then
      if ← samefilePaths ops src dst then
        let absSrc ← do
          if ← islinkPath ops src then ops.abspath (← readlink ops src)
          else ops.abspath src
        let absDst ← do
          if ← islinkPath ops dst then ops.abspath (← readlink ops dst)
          else ops.abspath dst
        throw (argumentError ("'src' and 'dst' refer to the same file/dir. " ++
          "This is not supported.\n  " ++ "`src` refers to: " ++ absSrc ++ "\n  " ++
          "`dst` refers to: " ++ absDst ++ "\n"))
      if ← isWithin ops srcPath dstPath then
        throw (argumentError ("'" ++ dst ++ "' contains '" ++ src ++
          "', so it cannot be removed before " ++ txt ++ "."))
      rm ops dst true true true
    else
      throw (argumentError ("'" ++ dst ++ "' exists. `force=true` " ++
        "is required to remove '" ++ dst ++ "' before " ++ txt ++ "."))

mutual
/--
Julia source: base/file.jl:393-399 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function cptree(src::String, dst::String; force::Bool=false,
                                          follow_symlinks::Bool=false)
    isdir(src) || throw(ArgumentError("'$src' is not a directory. Use `cp(src, dst)`"))
    checkfor_mv_cp_cptree(src, dst, "copying"; force=force, follow_symlinks=true)
    _cptree(src, dst, follow_symlinks)
end

```
-/
def cptree (src dst : String) (force followSymlinks : Bool) : M World Unit := do
  if !(← isdirPath ops src) then
    throw (argumentError ("'" ++ src ++ "' is not a directory. Use `cp(src, dst)`"))
  checkforMvCpCptree ops src dst "copying" force true
  cptreeInner src dst followSymlinks
partial_fixpoint

/--
Julia source: base/file.jl:400-418 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Nested directories need no checks: they cannot overlap once `src` and `dst` do not, and each
# nested destination is new. A followed symlink can lead anywhere, so it is checked again.
function _cptree(src::String, dst::String, follow_symlinks::Bool)
    mkdir(dst)
    for name in readdir(src)
        srcname = joinpath(src, name)
        if !follow_symlinks && islink(srcname)
            symlink(readlink(srcname), joinpath(dst, name))
        elseif isdir(srcname)
            if islink(srcname)
                cptree(srcname, joinpath(dst, name); follow_symlinks)
            else
                _cptree(srcname, joinpath(dst, name), follow_symlinks)
            end
        else
            sendfile(srcname, joinpath(dst, name))
        end
    end
end
```
-/
def cptreeInner (src dst : String) (followSymlinks : Bool) : M World Unit := do
  let _ ← mkdir ops ops.i64Ops dst (JInt.lit .i64 0o777)
  for name in (← readdir ops src false true) do
    let srcname ← ops.joinpath [src, name]
    let linkSkip ← if !followSymlinks then islinkPath ops srcname else pure false
    if linkSkip then
      symlink ops (← readlink ops srcname) (← ops.joinpath [dst, name]) false
    else if ← isdirPath ops srcname then
      if ← islinkPath ops srcname then
        cptree srcname (← ops.joinpath [dst, name]) false followSymlinks
      else
        cptreeInner srcname (← ops.joinpath [dst, name]) followSymlinks
    else
      sendfile ops srcname (← ops.joinpath [dst, name]) true
partial_fixpoint
end

/--
Julia source: base/file.jl:419-421 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cptree(src::AbstractString, dst::AbstractString; kwargs...) =
    cptree(String(src)::String, String(dst)::String; kwargs...)

```
-/
def cptreeAbstract (src dst : JuliaLean.base.stat.PathString PathVal) (force followSymlinks : Bool) :
    M World Unit := do
  let src ← JuliaLean.base.stat.stringOfPath ops.stat src
  let dst ← JuliaLean.base.stat.stringOfPath ops.stat dst
  cptree ops src dst force followSymlinks

/--
Julia source: base/file.jl:422-459 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    cp(src::AbstractString, dst::AbstractString; force::Bool=false, follow_symlinks::Bool=false)

Copy the file, link, or directory from `src` to `dst`.
`force=true` will first remove an existing `dst`.

If `follow_symlinks=false`, and `src` is a symbolic link, `dst` will be created as a
symbolic link. If `follow_symlinks=true` and `src` is a symbolic link, `dst` will be a copy
of the file or directory `src` refers to.
Return `dst`.

The timestamps, permissions, and ownership (if possible) of the destination file(s) are copied
from those of the source file(s), similar to the Unix `cp -p` command.

!!! note
    The `cp` function is different from the `cp` Unix command. The `cp` function always operates on
    the assumption that `dst` is a file, while the command does different things depending
    on whether `dst` is a directory or a file.
    Using `force=true` when `dst` is a directory will result in loss of all the contents present
    in the `dst` directory, and `dst` will become a file that has the contents of `src` instead.

!!! compat "Julia 1.13"
    Prior to Julia 1.13, the file permissions and other metadata were not necessarily
    preserved (e.g. the permissions were modified by the current `umask` on Unix systems).
"""
function cp(src::AbstractString, dst::AbstractString; force::Bool=false,
                                                      follow_symlinks::Bool=false)
    checkfor_mv_cp_cptree(src, dst, "copying"; force, follow_symlinks)
    if !follow_symlinks && islink(src)
        symlink(readlink(src), dst)
    elseif isdir(src)
        cptree(src, dst; force=force, follow_symlinks=follow_symlinks)
    else
        sendfile(src, dst; force)
    end
    dst
end

```
-/
def cp (src dst : String) (force followSymlinks : Bool) : M World String := do
  checkforMvCpCptree ops src dst "copying" force followSymlinks
  let linkCopy ← if !followSymlinks then islinkPath ops src else pure false
  if linkCopy then
    symlink ops (← readlink ops src) dst false
  else if ← isdirPath ops src then
    cptree ops src dst force followSymlinks
  else
    sendfile ops src dst force
  pure dst

/--
Julia source: base/file.jl:513-543 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _mv_replace(src::AbstractString, dst::AbstractString)
    # This check is copied from checkfor_mv_cp_cptree
    if ispath(dst) && Base.samefile(src, dst)
        abs_src = islink(src) ? abspath(readlink(src)) : abspath(src)
        abs_dst = islink(dst) ? abspath(readlink(dst)) : abspath(dst)
        throw(ArgumentError(string("'src' and 'dst' refer to the same file/dir. ",
                                   "This is not supported.\n  ",
                                   "`src` refers to: $(abs_src)\n  ",
                                   "`dst` refers to: $(abs_dst)\n")))
    end
    # First try to do a regular rename, because this might avoid a situation
    # where dst is deleted or truncated.
    try
        rename(src, dst)
    catch err
        err isa IOError || rethrow()
        err.code==Base.UV_ENOENT && rethrow()
        # on rename error try to delete dst if it exists and isn't the same as src
        checkfor_mv_cp_cptree(src, dst, "moving"; force=true)
        try
            rename(src, dst)
        catch err
            err isa IOError || rethrow()
            # on second error, default to force cp && rm
            cp(src, dst; force=true, follow_symlinks=false)
            rm(src; recursive=true)
        end
    end
    dst
end

```
-/
def mvReplace (src dst : String) : M World String := do
  let same ← do
    if ← ispathPath ops dst then samefilePaths ops src dst
    else pure false
  if same then
    let absSrc ← do
      if ← islinkPath ops src then ops.abspath (← readlink ops src)
      else ops.abspath src
    let absDst ← do
      if ← islinkPath ops dst then ops.abspath (← readlink ops dst)
      else ops.abspath dst
    throw (argumentError ("'src' and 'dst' refer to the same file/dir. " ++
      "This is not supported.\n  " ++ "`src` refers to: " ++ absSrc ++ "\n  " ++
      "`dst` refers to: " ++ absDst ++ "\n"))
  tryCatchM (do let _ ← rename ops src dst; pure ()) (fun err => do
    if !isIOError ops err then throw err
    if isIOErrorCode ops err ops.uvEnoent then throw err
    checkforMvCpCptree ops src dst "moving" true false
    tryCatchM (do let _ ← rename ops src dst; pure ()) (fun err => do
      if !isIOError ops err then throw err
      let _ ← cp ops src dst true false
      rm ops src false true true))
  pure dst

/--
Julia source: base/file.jl:544-560 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _mv_noreplace(src::AbstractString, dst::AbstractString)
    # Error if dst exists.
    # This check currently has TOCTTOU issues.
    checkfor_mv_cp_cptree(src, dst, "moving"; force=false)
    try
        rename(src, dst)
    catch err
        err isa IOError || rethrow()
        err.code==Base.UV_ENOENT && rethrow()
        # on error, default to cp && rm
        cp(src, dst; force=false, follow_symlinks=false)
        rm(src; recursive=true)
    end
    dst
end


```
-/
def mvNoreplace (src dst : String) : M World String := do
  checkforMvCpCptree ops src dst "moving" false false
  tryCatchM (do let _ ← rename ops src dst; pure ()) (fun err => do
    if !isIOError ops err then throw err
    if isIOErrorCode ops err ops.uvEnoent then throw err
    let _ ← cp ops src dst false false
    rm ops src false true true)
  pure dst

/--
Julia source: base/file.jl:460-512 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    mv(src::AbstractString, dst::AbstractString; force::Bool=false)

Move the file, link, or directory from `src` to `dst`.
`force=true` will first remove an existing `dst`.
Return `dst`.

# Examples
```jldoctest; filter = r"Stacktrace:(\\n \\[[0-9]+\\].*)*"
julia> write("hello.txt", "world");

julia> mv("hello.txt", "goodbye.txt")
"goodbye.txt"

julia> "hello.txt" in readdir()
false

julia> readline("goodbye.txt")
"world"

julia> write("hello.txt", "world2");

julia> mv("hello.txt", "goodbye.txt")
ERROR: ArgumentError: 'goodbye.txt' exists. `force=true` is required to remove 'goodbye.txt' before moving.
Stacktrace:
 [1] #checkfor_mv_cp_cptree#10(::Bool, ::Function, ::String, ::String, ::String) at ./file.jl:293
[...]

julia> mv("hello.txt", "goodbye.txt", force=true)
"goodbye.txt"

julia> rm("goodbye.txt");

```

!!! note
    The `mv` function is different from the `mv` Unix command. The `mv` function by
    default will error if `dst` exists, while the command will delete
    an existing `dst` file by default.
    Also the `mv` function always operates on
    the assumption that `dst` is a file, while the command does different things depending
    on whether `dst` is a directory or a file.
    Using `force=true` when `dst` is a directory will result in loss of all the contents present
    in the `dst` directory, and `dst` will become a file that has the contents of `src` instead.
"""
function mv(src::AbstractString, dst::AbstractString; force::Bool=false)
    if force
        _mv_replace(src, dst)
    else
        _mv_noreplace(src, dst)
    end
end

````
-/
def mvWith {S D R : Type} (replace noreplace : S → D → R)
    (src : S) (dst : D) (force : Bool) : R :=
  if force then replace src dst else noreplace src dst

/-- String specialization of the selected move methods. -/
def mv (src dst : String) (force : Bool) : M World String :=
  mvWith (mvReplace ops) (mvNoreplace ops) src dst force

/--
Julia source: base/file.jl:561-596 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    touch(path::AbstractString)
    touch(fd::File)

Update the last-modified timestamp on a file to the current time.

If the file does not exist a new file is created.

Return `path`.

# Examples
```jldoctest; setup = :(curdir = pwd(); testdir = mktempdir(); cd(testdir)), teardown = :(cd(curdir); rm(testdir, recursive=true)), filter = r"[\\d\\.]+e[\\+\\-]?\\d+"
julia> write("my_little_file", 2);

julia> mtime("my_little_file")
1.5273815391135583e9

julia> touch("my_little_file");

julia> mtime("my_little_file")
1.527381559163435e9
```

We can see the [`mtime`](@ref) has been modified by `touch`.
"""
function touch(path::AbstractString)
    f = open(path, JL_O_WRONLY | JL_O_CREAT, 0o0666)
    try
        touch(f)
    finally
        close(f)
    end
    path
end


````
-/
def touch (path : String) : M World String := do
  let f ← ops.openFlags path (JuliaLean.base.int.bor ops.jlOWronly ops.jlOCreat) (JInt.lit .u16 0o0666)
  tryFinally (ops.touchStream f) (ops.closeStream f)
  pure path

/--
Julia source: base/file.jl:634-665 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    prepare_for_deletion(path::AbstractString)

Prepares the given `path` for deletion by ensuring that all directories within that
`path` have write permissions, so that files can be removed from them.  This is
automatically invoked by methods such as `mktempdir()` to ensure that no matter what
weird permissions a user may have created directories with within the temporary prefix,
it will always be deleted.
"""
function prepare_for_deletion(path::AbstractString)
    # Nothing to do for non-directories
    if !isdir(path)
        return
    end

    try
        chmod(path, filemode(path) | 0o333)
    catch ex
        ex isa IOError || ex isa SystemError || rethrow()
    end
    for (root, dirs, _) in walkdir(path; onerror=x->())
        for dir in dirs
            dpath = joinpath(root, dir)
            try
                chmod(dpath, filemode(dpath) | 0o333)
            catch ex
                ex isa IOError || ex isa SystemError || rethrow()
            end
        end
    end
end

```
-/
def prepareForDeletion (path : String) : M World Unit := do
  if !(← isdirPath ops path) then return ()
  tryCatchM (do
      let _ ← chmod ops ops.u64Ops path
        (JuliaLean.base.int.bor (← filemodePath ops path) (JInt.lit .u64 0o333)) false
      pure ())
    (fun ex => if isIOError ops ex || ops.isSystemError ex then pure () else throw ex)
  let chnl ← walkdir ops path true false (fun _ => pure ())
  ops.channelForEach chnl (fun (root, dirs, _) => do
    for dir in dirs do
      let dpath ← ops.joinpath [root, dir]
      tryCatchM (do
          let _ ← chmod ops ops.u64Ops dpath
            (JuliaLean.base.int.bor (← filemodePath ops dpath) (JInt.lit .u64 0o333)) false
          pure ())
        (fun ex => if isIOError ops ex || ops.isSystemError ex then pure () else throw ex))

-- Reason: The cleanup registry, its bounds and its lock are global mutable state; the World holds them and `FileOps.cleanup*` and `withCleanupLock` access them.
-- UNTRANSLATED
-- Source: base/file.jl:666-670 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- const TEMP_CLEANUP_MIN = Ref(1024)
-- const TEMP_CLEANUP_MAX = Ref(1024)
-- const TEMP_CLEANUP = Dict{String,Bool}()
-- const TEMP_CLEANUP_LOCK = ReentrantLock()
-- 
-- /Source

/--
Julia source: base/file.jl:690-710 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function temp_cleanup_purge_prelocked(force::Bool)
    filter!(TEMP_CLEANUP) do (path, asap)
        try
            ispath(path) || return false
            if force || asap
                prepare_for_deletion(path)
                rm(path, recursive=true, force=true)
            end
            return ispath(path)
        catch ex
            @warn """
                Failed to clean up temporary path $(repr(path))
                $ex
                """ _group=:file
            ex isa InterruptException && rethrow()
            return true
        end
    end
    nothing
end

```
-/
def tempCleanupPurgePrelocked (force : Bool) : M World Unit := do
  let _ ← ops.cleanupFilter () (fun _ path asap => tryCatchM (do
      if !(← ispathPath ops path) then return (false, ())
      if force || asap then
        prepareForDeletion ops path
        rm ops path true true true
      return (← ispathPath ops path, ()))
    (fun ex => do
      ops.logWarn ("Failed to clean up temporary path " ++ (← ops.repr path) ++ "\n" ++
        (← ops.errorString ex) ++ "\n")
      if ops.isInterruptException ex then throw ex
      return (true, ())))
  pure ()

/--
Julia source: base/file.jl:671-684 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function temp_cleanup_later(path::AbstractString; asap::Bool=false)
    @lock TEMP_CLEANUP_LOCK begin
    # each path should only be inserted here once, but if there
    # is a collision, let !asap win over asap: if any user might
    # still be using the path, don't delete it until process exit
    TEMP_CLEANUP[path] = get(TEMP_CLEANUP, path, true) & asap
    if length(TEMP_CLEANUP) > TEMP_CLEANUP_MAX[]
        temp_cleanup_purge_prelocked(false)
        TEMP_CLEANUP_MAX[] = max(TEMP_CLEANUP_MIN[], 2*length(TEMP_CLEANUP))
    end
    end
    nothing
end

```
-/
def tempCleanupLater (path : String) (asap : Bool) : M World Unit := do
  ops.withCleanupLock (do
    let current ← ops.cleanupGet path true
    ops.cleanupSet path (current && asap)
    if (← ops.cleanupLength ()).val > (← ops.cleanupMaxGet ()).val then
      tempCleanupPurgePrelocked ops false
      let low ← ops.cleanupMinGet ()
      let doubled := JuliaLean.base.int.mul (JInt.lit .i64 2) (← ops.cleanupLength ())
      ops.cleanupMaxSet (if low.val < doubled.val then doubled else low))
  pure ()

/--
Julia source: base/file.jl:685-689 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function temp_cleanup_forget(path::AbstractString)
    @lock TEMP_CLEANUP_LOCK delete!(TEMP_CLEANUP, path)
    nothing
end

```
-/
def tempCleanupForget (path : String) : M World Unit := do
  ops.withCleanupLock (ops.cleanupDelete path)
  pure ()

/--
Julia source: base/file.jl:711-730 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function temp_cleanup_purge_all()
    may_need_gc = Ref(false)
    @lock TEMP_CLEANUP_LOCK filter!(TEMP_CLEANUP) do (path, _)
        try
            ispath(path) || return false
            may_need_gc[] = true
            return true
        catch ex
            ex isa InterruptException && rethrow()
            return true
        end
    end
    if may_need_gc[]
        # this is only usually required on Sys.iswindows(), but may as well do it everywhere
        GC.gc(true)
    end
    @lock TEMP_CLEANUP_LOCK temp_cleanup_purge_prelocked(true)
    nothing
end

```
-/
def tempCleanupPurgeAll : M World Unit := do
  let mayNeedGc ← ops.withCleanupLock (ops.cleanupFilter false (fun flag path _ => tryCatchM (do
      if !(← ispathPath ops path) then return (false, flag)
      return (true, true))
    (fun ex => do
      if ops.isInterruptException ex then throw ex
      return (true, flag))))
  if mayNeedGc then ops.gcFull ()
  ops.withCleanupLock (tempCleanupPurgePrelocked ops true)
  pure ()

/--
Julia source: base/file.jl:731-733 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# deprecated internal function used by some packages
temp_cleanup_purge(; force=false) = force ? temp_cleanup_purge_all() : @lock TEMP_CLEANUP_LOCK temp_cleanup_purge_prelocked(false)

```
-/
def tempCleanupPurge (force : Bool) : M World Unit :=
  if force then tempCleanupPurgeAll ops else ops.withCleanupLock (tempCleanupPurgePrelocked ops false)

/-- The Julia code that the cleanup process runs (the `rmcmd` literal). -/
def cleanupScript : String :=
  "cleanuplist = readlines(stdin) # This loop won't start running until stdin is closed, which is supposed to be sequenced after the process exits\n" ++
  "sleep(1) # Wait for the operating system to hopefully be ready, since the OS implementation is probably incorrect, given the history of buggy work-arounds like this that have existed for ages in dotNet and libuv\n" ++
  "for path in cleanuplist\n" ++
  "    try\n" ++
  "        rm(path, force=true, recursive=true)\n" ++
  "    catch ex\n" ++
  "        @warn \"Failed to clean up temporary path $(repr(path))\n$ex\" _group=:file\n" ++
  "    end\n" ++
  "end\n"

/--
Julia source: base/file.jl:734-755 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function temp_cleanup_postprocess(cleanup_dirs)
    if !isempty(cleanup_dirs)
        rmcmd = """
        cleanuplist = readlines(stdin) # This loop won't start running until stdin is closed, which is supposed to be sequenced after the process exits
        sleep(1) # Wait for the operating system to hopefully be ready, since the OS implementation is probably incorrect, given the history of buggy work-arounds like this that have existed for ages in dotNet and libuv
        for path in cleanuplist
            try
                rm(path, force=true, recursive=true)
            catch ex
                @warn "Failed to clean up temporary path \$(repr(path))\n\$ex" _group=:file
            end
        end
        """
        cmd = Cmd(Base.cmd_gen(((Base.julia_cmd(),), ("--startup-file=no",), ("-e",), (rmcmd,))); ignorestatus = true, detach = true)
        pw = Base.PipeEndpoint()
        run(cmd, pw, devnull, stderr; wait=false)
        join(pw, cleanup_dirs, "\n")
        Base.dup(Base._fd(pw)) # intentionally leak a reference, until the process exits
        close(pw)
    end
end

```
-/
def tempCleanupPostprocess (cleanupDirs : List String) : M World Unit := do
  if !cleanupDirs.isEmpty then
    let cmd ← ops.cleanupCommand cleanupScript
    let pw ← ops.newPipeEndpoint ()
    ops.runDetached cmd pw
    ops.joinWrite pw cleanupDirs "\n"
    ops.dupPipe pw
    ops.closePipe pw

/--
Julia source: base/file.jl:756-760 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function temp_cleanup_atexit()
    temp_cleanup_purge_all()
    @lock TEMP_CLEANUP_LOCK temp_cleanup_postprocess(keys(TEMP_CLEANUP))
end

```
-/
def tempCleanupAtexit : M World Unit := do
  tempCleanupPurgeAll ops
  ops.withCleanupLock (do tempCleanupPostprocess ops (← ops.cleanupKeys ()))

/--
Julia source: base/file.jl:761-764 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function __postinit__()
    Base.atexit(temp_cleanup_atexit)
end

```
-/
def postinit : M World Unit :=
  ops.atexit (tempCleanupAtexit ops)

/--
Julia source: base/file.jl:777-784 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# Obtain a temporary filename.
function tempname(parent::AbstractString=tempdir(); max_tries::Int = 100, cleanup::Bool=true, suffix::AbstractString="")
    filename = _tempname(parent, suffix, max_tries)
    cleanup && temp_cleanup_later(filename)
    return filename
end

```
-/
def tempname (parent : String) (maxTries : I64) (cleanup : Bool) (suffix : String) :
    M World String := do
  let filename ← tempnameInternal ops parent suffix maxTries
  if cleanup then tempCleanupLater ops filename false
  pure filename

/-- `tempname()` and the other calls that take the default `parent = tempdir()`. -/
def tempnameDefault (maxTries : I64) (cleanup : Bool) (suffix : String) : M World String := do
  tempname ops (← tempdirFn ops) maxTries cleanup suffix

/--
Julia source: base/file.jl:825-830 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function mktemp(parent::AbstractString=tempdir(); cleanup::Bool=true)
    filename = _win_mkstemp(parent)
    cleanup && temp_cleanup_later(filename)
    return (filename, Base.open(filename, "r+"))
end

```
-/
def mktempWindows (parent : String) (cleanup : Bool) : M World (String × Stream) := do
  let filename ← winMkstemp ops parent
  if cleanup then tempCleanupLater ops filename false
  pure (filename, ← ops.openMode filename "r+")

/--
Julia source: base/file.jl:831-843 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
else # !windows

# Create and return the name of a temporary file along with an IOStream
function mktemp(parent::AbstractString=tempdir(); cleanup::Bool=true)
    b = joinpath(parent, temp_prefix * "XXXXXX")
    p = ccall(:mkstemp, Int32, (Cstring,), b) # modifies b
    systemerror(:mktemp, p == -1)
    cleanup && temp_cleanup_later(b)
    return (b, fdio(p, true))
end

end # os-test

```
-/
def mktempUnix (parent : String) (cleanup : Bool) : M World (String × Stream) := do
  let b ← ops.joinpath [parent, tempPrefix ++ "XXXXXX"]
  let cb ← cstr ops b
  let p ← ops.mkstemp cb
  let b ← ops.cstringContents cb
  ops.stat.errors.systemError "mktemp" (p.val == -1)
  if cleanup then tempCleanupLater ops b false
  pure (b, ← ops.fdio p true)

/-- `mktemp(parent; cleanup)`: the method defined for the platform. -/
def mktemp (parent : String) (cleanup : Bool) : M World (String × Stream) :=
  if ops.isWindows then mktempWindows ops parent cleanup else mktempUnix ops parent cleanup

def mktempDefault (cleanup : Bool) : M World (String × Stream) := do
  mktemp ops (← tempdirFn ops) cleanup

-- Reason: A docstring attached to the `tempname` function; it defines no method.
-- UNTRANSLATED
-- Source: base/file.jl:844-881 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     tempname(parent=tempdir(); cleanup=true, suffix="")::String
-- 
-- Generate a temporary file path. This function only returns a path; no file is
-- created. The path is likely to be unique, but this cannot be guaranteed due to
-- the very remote possibility of two simultaneous calls to `tempname` generating
-- the same file name. The name is guaranteed to differ from all files already
-- existing at the time of the call to `tempname`.
-- 
-- When called with no arguments, the temporary name will be an absolute path to a
-- temporary name in the system temporary directory as given by `tempdir()`. If a
-- `parent` directory argument is given, the temporary path will be in that
-- directory instead. If a suffix is given the tempname will end with that suffix
-- and be tested for uniqueness with that suffix.
-- 
-- The `cleanup` option controls whether the process attempts to delete the
-- returned path automatically when the process exits. Note that the `tempname`
-- function does not create any file or directory at the returned location, so
-- there is nothing to cleanup unless you create a file or directory there. If
-- you do and `cleanup` is `true` it will be deleted upon process termination.
-- 
-- !!! compat "Julia 1.4"
--     The `parent` and `cleanup` arguments were added in 1.4. Prior to Julia 1.4
--     the path `tempname` would never be cleaned up at process termination.
-- 
-- !!! compat "Julia 1.12"
--     The `suffix` keyword argument was added in Julia 1.12.
-- 
-- !!! warning
-- 
--     This can lead to security holes if another process obtains the same
--     file name and creates the file before you are able to. Open the file with
--     `JL_O_EXCL` if this is a concern. Using [`mktemp()`](@ref) is also
--     recommended instead.
-- """
-- tempname()
-- 
-- /Source

-- Reason: A docstring attached to the `mktemp` function; it defines no method.
-- UNTRANSLATED
-- Source: base/file.jl:882-895 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     mktemp(parent=tempdir(); cleanup=true) -> (path, io)
-- 
-- Return `(path, io)`, where `path` is the path of a new temporary file in `parent`
-- and `io` is an open file object for this path. The `cleanup` option controls whether
-- the temporary file is automatically deleted when the process exits.
-- 
-- !!! compat "Julia 1.3"
--     The `cleanup` keyword argument was added in Julia 1.3. Relatedly, starting from 1.3,
--     Julia will remove the temporary paths created by `mktemp` when the Julia process exits,
--     unless `cleanup` is explicitly set to `false`.
-- """
-- mktemp(parent)
-- 
-- /Source

/--
Julia source: base/file.jl:896-942 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    mktempdir(parent=tempdir(); prefix=$(repr(temp_prefix)), cleanup=true) -> path

Create a temporary directory in the `parent` directory with a name
constructed from the given `prefix` and a random suffix, and return its path.
Additionally, on some platforms, any trailing `'X'` characters in `prefix` may be replaced
with random characters.
If `parent` does not exist, throw an error. The `cleanup` option controls whether
the temporary directory is automatically deleted when the process exits.

!!! compat "Julia 1.2"
    The `prefix` keyword argument was added in Julia 1.2.

!!! compat "Julia 1.3"
    The `cleanup` keyword argument was added in Julia 1.3. Relatedly, starting from 1.3,
    Julia will remove the temporary paths created by `mktempdir` when the Julia process
    exits, unless `cleanup` is explicitly set to `false`.

See also: [`mktemp`](@ref), [`mkdir`](@ref).
"""
function mktempdir(parent::AbstractString=tempdir();
    prefix::AbstractString=temp_prefix, cleanup::Bool=true)
    if isempty(parent) || isseparator(last(parent))
        # append a path_separator only if parent didn't already have one
        tpath = "$(parent)$(prefix)XXXXXX"
    else
        tpath = "$(parent)$(path_separator)$(prefix)XXXXXX"
    end

    req = Libc.malloc(_sizeof_uv_fs)
    try
        ret = ccall(:uv_fs_mkdtemp, Cint,
                    (Ptr{Cvoid}, Ptr{Cvoid}, Cstring, Ptr{Cvoid}),
                    C_NULL, req, tpath, C_NULL)
        if ret < 0
            uv_fs_req_cleanup(req)
            uv_error("mktempdir($(repr(parent)))", ret)
        end
        path = unsafe_string(ccall(:jl_uv_fs_t_path, Cstring, (Ptr{Cvoid},), req))
        uv_fs_req_cleanup(req)
        cleanup && temp_cleanup_later(path)
        return path
    finally
        Libc.free(req)
    end
end

```
-/
def mktempdir (parent pfx : String) (cleanup : Bool) : M World String := do
  let appendDirectly ← do
    if parent.isEmpty then pure true
    else ops.isseparator (← ops.lastChar parent)
  let tpath := if appendDirectly then parent ++ pfx ++ "XXXXXX"
    else parent ++ ops.pathSeparator ++ pfx ++ "XXXXXX"
  let req ← ops.mallocReq ()
  tryFinally (do
    let cpath ← cstr ops tpath
    let ret ← ops.uvFsMkdtemp req cpath
    if ret.val < 0 then
      ops.reqCleanup req
      uvError ops ("mktempdir(" ++ (← ops.repr parent) ++ ")") ret
    let path ← ops.uvFsTPath req
    ops.reqCleanup req
    if cleanup then tempCleanupLater ops path false
    pure path) (ops.freeReq req)

def mktempdirDefault (pfx : String) (cleanup : Bool) : M World String := do
  mktempdir ops (← tempdirFn ops) pfx cleanup

/--
Julia source: base/file.jl:943-968 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

"""
    mktemp(f::Function, parent=tempdir())

Apply the function `f` to the result of [`mktemp(parent)`](@ref) and remove the
temporary file upon completion.

See also: [`mktempdir`](@ref).
"""
function mktemp(fn::Function, parent::AbstractString=tempdir())
    (tmp_path, tmp_io) = mktemp(parent)
    try
        fn(tmp_path, tmp_io)
    finally
        temp_cleanup_forget(tmp_path)
        try
            close(tmp_io)
            ispath(tmp_path) && rm(tmp_path)
        catch ex
            @error "mktemp cleanup" _group=:file exception=(ex, catch_backtrace())
            # might be possible to remove later
            temp_cleanup_later(tmp_path, asap=true)
        end
    end
end

```
-/
def mktempWith {A : Type} (fn : String → Stream → M World A) (parent : String) : M World A := do
  let (tmpPath, tmpIo) ← mktemp ops parent true
  tryFinally (fn tmpPath tmpIo) (do
    tempCleanupForget ops tmpPath
    tryCatchM (do
        ops.closeStream tmpIo
        if ← ispathPath ops tmpPath then rm ops tmpPath false false true)
      (fun ex => do
        ops.logError "mktemp cleanup" ex
        tempCleanupLater ops tmpPath true))

/--
Julia source: base/file.jl:969-999 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    mktempdir(f::Function, parent=tempdir(); prefix=$(repr(temp_prefix)))

Apply the function `f` to the result of [`mktempdir(parent; prefix)`](@ref) and remove the
temporary directory and all of its contents upon completion.

See also: [`mktemp`](@ref), [`mkdir`](@ref).

!!! compat "Julia 1.2"
    The `prefix` keyword argument was added in Julia 1.2.
"""
function mktempdir(fn::Function, parent::AbstractString=tempdir();
    prefix::AbstractString=temp_prefix)
    tmpdir = mktempdir(parent; prefix=prefix)
    try
        fn(tmpdir)
    finally
        temp_cleanup_forget(tmpdir)
        try
            if ispath(tmpdir)
                prepare_for_deletion(tmpdir)
                rm(tmpdir, recursive=true)
            end
        catch ex
            @error "mktempdir cleanup" _group=:file exception=(ex, catch_backtrace())
            # might be possible to remove later
            temp_cleanup_later(tmpdir, asap=true)
        end
    end
end

```
-/
def mktempdirWith {A : Type} (fn : String → M World A) (parent pfx : String) : M World A := do
  let tmpdir ← mktempdir ops parent pfx true
  tryFinally (fn tmpdir) (do
    tempCleanupForget ops tmpdir
    tryCatchM (do
        if ← ispathPath ops tmpdir then
          prepareForDeletion ops tmpdir
          rm ops tmpdir false true true)
      (fun ex => do
        ops.logError "mktempdir cleanup" ex
        tempCleanupLater ops tmpdir true))

/--
Julia source: base/file.jl:1662-1679 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# - http://docs.libuv.org/en/v1.x/fs.html#c.uv_fs_statfs (libuv function docs)
# - http://docs.libuv.org/en/v1.x/fs.html#c.uv_statfs_t (libuv docs of the returned struct)
"""
    DiskStat

Stores information about the disk in bytes. Populate by calling `diskstat`.
"""
struct DiskStat
    ftype::UInt64
    bsize::UInt64
    blocks::UInt64
    bfree::UInt64
    bavail::UInt64
    files::UInt64
    ffree::UInt64
    fspare::NTuple{4, UInt64} # reserved
end

```
-/
structure DiskStat where
  ftype : U64
  bsize : U64
  blocks : U64
  bfree : U64
  bavail : U64
  files : U64
  ffree : U64
  fspare : List U64

/-- A property of a `DiskStat`. -/
inductive DiskStatField where
  | ftype | bsize | blocks | bfree | bavail | files | ffree | fspare
  | total | available | used
  | other (name : String)

/-- The value of a `DiskStat` property. -/
inductive DiskStatValue where
  | signed (value : I64)
  | unsigned (value : U64)
  | tuple (values : List U64)

/--
Julia source: base/file.jl:1680-1688 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.getproperty(stats::DiskStat, field::Symbol)
    total = Int64(getfield(stats, :bsize) * getfield(stats, :blocks))
    available = Int64(getfield(stats, :bsize) * getfield(stats, :bavail))
    field === :total && return total
    field === :available && return available
    field === :used && return total - available
    return getfield(stats, field)
end

```
-/
def diskStatProperty (stats : DiskStat) (field : DiskStatField) : M World DiskStatValue := do
  let total ← JuliaLean.base.io.liftJl
    (JInt.convert "convert" .i64 (JuliaLean.base.int.mul stats.bsize stats.blocks).val)
  let available ← JuliaLean.base.io.liftJl
    (JInt.convert "convert" .i64 (JuliaLean.base.int.mul stats.bsize stats.bavail).val)
  match field with
  | .total => pure (.signed total)
  | .available => pure (.signed available)
  | .used => pure (.signed (JuliaLean.base.int.sub total available))
  | .ftype => pure (.unsigned stats.ftype)
  | .bsize => pure (.unsigned stats.bsize)
  | .blocks => pure (.unsigned stats.blocks)
  | .bfree => pure (.unsigned stats.bfree)
  | .bavail => pure (.unsigned stats.bavail)
  | .files => pure (.unsigned stats.files)
  | .ffree => pure (.unsigned stats.ffree)
  | .fspare => pure (.tuple stats.fspare)
  | .other name => throw (.foreignError "FieldError" ("type DiskStat has no field `" ++ name ++ "`"))

/--
Julia source: base/file.jl:1689-1691 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@eval Base.propertynames(stats::DiskStat) =
    $((fieldnames(DiskStat)[1:end-1]..., :available, :total, :used))

```
-/
def diskStatPropertynames : List String :=
  ["ftype", "bsize", "blocks", "bfree", "bavail", "files", "ffree", "available", "total", "used"]

def signedProperty (stats : DiskStat) (field : DiskStatField) : M World I64 := do
  match ← diskStatProperty stats field with
  | .signed value => pure value
  | _ => throw (.foreignError "TypeError" "DiskStat property")

/--
Julia source: base/file.jl:1692-1694 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.show(io::IO, x::DiskStat) =
    print(io, "DiskStat(total=$(x.total), used=$(x.used), available=$(x.available))")

```
-/
def showDiskStat (io : Stream) (x : DiskStat) : M World Unit := do
  let total ← ops.i64Ops.display (← signedProperty x .total)
  let used ← ops.i64Ops.display (← signedProperty x .used)
  let available ← ops.i64Ops.display (← signedProperty x .available)
  ops.printString io ("DiskStat(total=" ++ total ++ ", used=" ++ used ++ ", available=" ++ available ++ ")")

/-- The fields of a loaded `uv_statfs_t`, in declaration order. -/
def diskStatOfRaw (raw : DiskStatRaw) : M World DiskStat := do
  match ops.diskStatFields raw with
  | ([ftype, bsize, blocks, bfree, bavail, files, ffree], fspare) =>
    pure ⟨ftype, bsize, blocks, bfree, bavail, files, ffree, fspare⟩
  | _ => throw (.foreignError "TypeError" "DiskStat layout")

/--
Julia source: base/file.jl:1695-1713 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    diskstat(path=pwd())

Return statistics in bytes about the disk that contains the file or directory pointed at by
`path`. If no argument is passed, statistics about the disk that contains the current
working directory are returned.

!!! compat "Julia 1.8"
    This method was added in Julia 1.8.
"""
function diskstat(path::AbstractString=pwd())
    req = zeros(UInt8, _sizeof_uv_fs)
    err = ccall(:uv_fs_statfs, Cint, (Ptr{Cvoid}, Ptr{Cvoid}, Cstring, Ptr{Cvoid}),
                C_NULL, req, path, C_NULL)
    err < 0 && uv_error("diskstat($(repr(path)))", err)
    statfs_ptr = ccall(:jl_uv_fs_t_ptr, Ptr{Nothing}, (Ptr{Cvoid},), req)

    return unsafe_load(reinterpret(Ptr{DiskStat}, statfs_ptr))
end
```
-/
def diskstat (path : String) : M World DiskStat := do
  let req ← ops.newStatfsBuffer ()
  let cpath ← cstr ops path
  let err ← ops.uvFsStatfs req cpath
  if err.val < 0 then uvError ops ("diskstat(" ++ (← ops.repr path) ++ ")") err
  diskStatOfRaw ops (← ops.loadDiskStat req)

def diskstatDefault : M World DiskStat := do
  diskstat ops (← pwd ops)

end

end JuliaLean.base.file


/-!
# Filesystem models

The models expose filesystem calls as finite state supplied by the caller. The
Julia control flow around those calls is mirrored from `base/file.jl`,
`base/stat.jl`, and `base/filesystem.jl` on master `bbfa0ce4150`.
-/

namespace JuliaLean.Files

inductive PathShape where
  | relative
  | absolute
  | trailingSlash
  | symlink
  | empty
  deriving Repr, DecidableEq

/-! ## `mkpath`, `base/file.jl:239-256` -/

inductive Component where
  | missing
  | directory
  | file
  | symlinkDirectory
  | symlinkFile
  deriving Repr, DecidableEq

def Component.isDir : Component → Bool
  | .directory | .symlinkDirectory => true
  | _ => false

def Component.create : Component → Result Component
  | .missing => .ok .directory
  | .directory => .ok .directory
  | .symlinkDirectory => .ok .symlinkDirectory
  | c => .error .io c

structure PathState where
  shape : PathShape
  components : List Component
  deriving Repr, DecidableEq

/-- Forward form of the recursive parent-first calls in `mkpath`. -/
def mkpathComponents : List Component → Result (List Component)
  | [] => .ok []
  | c :: cs =>
      match c.create with
      | .error e c' => .error e (c' :: cs)
      | .ok c' =>
          match mkpathComponents cs with
          | .ok cs' => .ok (c' :: cs')
          | .error e cs' => .error e (c' :: cs')

def mkpath (path : PathState) : Result PathState :=
  match mkpathComponents path.components with
  | .ok components => .ok { path with components }
  | .error e components => .error e { path with components }

/-! ## `rm`, `base/file.jl:283-326` -/

inductive RmEntry where
  | missing
  | file
  | link
  | directory (children : Nat)
  /-- A directory link observed through a trailing slash: `islink` is false,
  `isdir` is true, but the final `rmdir` returns `ENOTDIR`. -/
  | trailingDirLink (targetChildren : Nat)
  deriving Repr, DecidableEq

/-- The same branch order as `rm`: link/non-directory first, recursive children
second, and `rmdir` last. -/
def rm (entry : RmEntry) (force recursive : Bool) : Result RmEntry :=
  match entry with
  | .missing => if force then .ok .missing else .error .io .missing
  | .file => .ok .missing
  | .link => .ok .missing
  | .directory children =>
      if recursive || children == 0 then .ok .missing
      else .error .io entry
  | .trailingDirLink targetChildren =>
      if recursive then .error .io (.trailingDirLink 0)
      else .error .io (.trailingDirLink targetChildren)

/-! ## `cp` and `mv`, `base/file.jl:363-390,447-458,505-558` -/

inductive Destination where
  | absent
  | regular
  | directory
  | danglingLink
  deriving Repr, DecidableEq

def Destination.isPath : Destination → Bool
  | .regular | .directory => true
  | .absent | .danglingLink => false

structure CopyState where
  destination : Destination
  targetWritten : Bool := false
  deriving Repr, DecidableEq

/-- `checkfor_mv_cp_cptree` followed by `sendfile`. With a dangling link,
`ispath(dst)` is false; libuv's forced copy follows the link. -/
def cp (state : CopyState) (force : Bool) : Result CopyState :=
  if state.destination.isPath then
    if force then .ok { destination := .regular }
    else .error .argument state
  else
    match state.destination with
    | .absent => .ok { destination := .regular }
    | .danglingLink =>
        if force then .ok { destination := .danglingLink, targetWritten := true }
        else .error .io state
    | _ => .error .io state

/-- Successful rename replaces every distinct destination. The fallback uses
`cp(...; force=true)` and then removes the source. -/
def mv (state : CopyState) (force : Bool) : Result CopyState :=
  if force then .ok { destination := .regular }
  else match state.destination with
    | .absent => .ok { destination := .regular }
    | _ => .error .argument state

/-! ## Temporary names and cleanup, `base/file.jl:765-998` -/

abbrev PathText := List Char

def tempPrefix : PathText := ['j', 'l', '_']

structure TempParent where
  text : PathText
  shape : PathShape
  isDir : Bool
  deriving Repr, DecidableEq

inductive TempKind where
  | name
  | file
  | directory
  deriving Repr, DecidableEq

structure TempObject where
  path : PathText
  kind : TempKind
  present : Bool
  cleanupRegistered : Bool := false
  deriving Repr, DecidableEq

def tempPath (parent namePrefix random suffix : PathText) : PathText :=
  parent ++ namePrefix ++ random ++ suffix

structure TempCandidate where
  random : PathText
  isPath : Bool
  isLink : Bool
  deriving Repr, DecidableEq

/-- The `for _ in 1:max_tries` loop in `_tempname`, returning the first name
that `ispath` reports absent. -/
def chooseTemp : Nat → List TempCandidate → Option PathText
  | 0, _ => none
  | _, [] => none
  | tries + 1, candidate :: candidates =>
      if candidate.isPath then chooseTemp tries candidates else some candidate.random

/-- `_tempname` checks that the parent is a directory, retries existing
candidates, and errors when `max_tries` is exhausted. -/
def tempname (parent : TempParent) (candidates : List TempCandidate) (maxTries : Nat)
    (suffix : PathText) (cleanup : Bool) : Result TempObject :=
  if parent.isDir then
    match chooseTemp maxTries candidates with
    | some random =>
        .ok { path := tempPath parent.text tempPrefix random suffix, kind := .name,
              present := false, cleanupRegistered := cleanup }
    | none => .error .errorException { path := [], kind := .name, present := false }
  else .error .argument { path := [], kind := .name, present := false }

def tempParentUsable (parent : TempParent) : Bool :=
  parent.isDir || parent.shape == .empty

/-- Unix `mkstemp` atomically creates the name. An empty parent constructs a
relative template in the current directory. -/
def mktemp (parent : TempParent) (random : PathText) (cleanup : Bool) : Result TempObject :=
  if tempParentUsable parent then
    .ok { path := tempPath parent.text tempPrefix random [], kind := .file,
          present := true, cleanupRegistered := cleanup }
  else .error .io { path := [], kind := .file, present := false }

/-- `uv_fs_mkdtemp` creates `prefix * random`; the source handles an empty
parent as a relative path in the current directory. -/
def mktempdir (parent : TempParent) (namePrefix random : PathText) (cleanup : Bool) : Result TempObject :=
  if tempParentUsable parent then
    .ok { path := tempPath parent.text namePrefix random [], kind := .directory,
          present := true, cleanupRegistered := cleanup }
  else .error .io { path := [], kind := .directory, present := false }

/-- The function-taking overloads forget the exit hook and remove the object
in `finally`, `base/file.jl:952-998`. -/
def cleanupTemp (object : TempObject) : TempObject :=
  { object with present := false, cleanupRegistered := false }

/-! ## `readdir`, `base/file.jl:1081-1082,1176-1207` -/

def insertName (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertName x ys

def sortNames : List Nat → List Nat
  | [] => []
  | x :: xs => insertName x (sortNames xs)

def renderName (dir : List Nat) (join : Bool) (name : Nat) : List Nat :=
  if join then dir ++ [name] else [name]

def readdir (dir : List Nat) (scan : List Nat) (join sort : Bool) : List (List Nat) :=
  let names := if sort then sortNames scan else scan
  names.map (renderName dir join)

/-! ## `walkdir`, `base/file.jl:1403-1443` -/

mutual
  inductive DirTree where
    | node (name : Nat) (files : List Nat) (children : DirForest)

  inductive DirForest where
    | nil
    | cons (head : DirTree) (tail : DirForest)
end

namespace DirForest

def names : DirForest → List Nat
  | .nil => []
  | .cons (.node name _ _) tail => name :: names tail

end DirForest

structure WalkRow where
  path : List Nat
  dirs : List Nat
  files : List Nat
  deriving Repr, DecidableEq

mutual
  def walkTop (parent : List Nat) : DirTree → List WalkRow
    | .node name files children =>
        let path := parent ++ [name]
        { path, dirs := children.names, files } :: walkTopForest path children

  def walkTopForest (parent : List Nat) : DirForest → List WalkRow
    | .nil => []
    | .cons head tail => walkTop parent head ++ walkTopForest parent tail
end

mutual
  def walkBottom (parent : List Nat) : DirTree → List WalkRow
    | .node name files children =>
        let path := parent ++ [name]
        walkBottomForest path children ++ [{ path, dirs := children.names, files }]

  def walkBottomForest (parent : List Nat) : DirForest → List WalkRow
    | .nil => []
    | .cons head tail => walkBottom parent head ++ walkBottomForest parent tail
end

def walkdir (parent : List Nat) (tree : DirTree) (topdown : Bool) : List WalkRow :=
  if topdown then walkTop parent tree else walkBottom parent tree

/-! ## `touch`, `base/file.jl:586-594` -/

structure TouchState where
  present : Bool
  bytes : List UInt8
  mtime : Nat
  deriving Repr, DecidableEq

def touch (now : Nat) (state : TouchState) : TouchState :=
  { present := true, bytes := if state.present then state.bytes else [], mtime := now }

/-! ## Recursive `chmod`, `base/file.jl:1635-1646` -/

mutual
  inductive ModeTree where
    | directory (mode : Nat) (children : ModeForest)

  inductive ModeEntry where
    | file (mode : Nat)
    | link (mode : Nat)
    | directory (tree : ModeTree)

  inductive ModeForest where
    | nil
    | cons (head : ModeEntry) (tail : ModeForest)
end

mutual
  def chmodChild (mode : Nat) : ModeEntry → ModeEntry
    | .file _ => .file mode
    | .link old => .link old
    | .directory tree => .directory (chmodTree mode true tree)

  def chmodForest (mode : Nat) : ModeForest → ModeForest
    | .nil => .nil
    | .cons head tail => .cons (chmodChild mode head) (chmodForest mode tail)

  def chmodTree (mode : Nat) (recursive : Bool) : ModeTree → ModeTree
    | .directory _ children =>
        .directory mode (if recursive then chmodForest mode children else children)
end

end JuliaLean.Files

namespace JuliaLean.Files.Coverage

open JuliaLean.Files

/-! ## Working directories and directory creation (`base/file.jl:54-194`) -/

inductive BufferReply where
  | noBuffer (required : Nat)
  | success (value : PathText)
  | failure
  deriving Repr, DecidableEq

def bufferPath : List BufferReply → Result PathText
  | [] => .error .io []
  | .noBuffer _ :: replies => bufferPath replies
  | .success value :: _ => .ok value
  | .failure :: _ => .error .io []

def checkMode (mode : Int) : Result Int :=
  if 0 ≤ mode ∧ mode ≤ 511 then .ok mode else .error .argument mode

def mkdirCall (path : PathText) (mode : Int) (returnCode : Int) : Result PathText :=
  match checkMode mode with
  | .error error _ => .error error path
  | .ok _ => if returnCode < 0 then .error .io path else .ok path

def cdCall (returnCode : Int) : Result Unit :=
  if returnCode < 0 then .error .io () else .ok ()

inductive CdEvent where
  | save
  | change (path : PathText)
  | callback
  | restore
  | closeSaved
  deriving Repr, DecidableEq

def cdCallbackEvents (path : PathText) : List CdEvent :=
  [.save, .change path, .callback, .restore, .closeSaved]

def pwdMethod (replies : List BufferReply) : Result PathText := bufferPath replies

def cdDirectoryMethod (returnCode : Int) : Result Unit := cdCall returnCode
def cdHomeMethod (home : PathText) (returnCode : Int) : PathText × Result Unit :=
  (home, cdDirectoryMethod returnCode)
def cdCallbackMethod (path : PathText) : List CdEvent := cdCallbackEvents path
def cdCallbackHomeMethod (home : PathText) : List CdEvent := cdCallbackMethod home

def mkpathMethod (path : PathState) (parentIsSelf alreadyDirectory : Bool) (mode : Int) :
    Result PathState :=
  if parentIsSelf || alreadyDirectory then .ok path
  else match checkMode mode with
    | .error error _ => .error error path
    | .ok _ => mkpath path

def rmMethod (entry : RmEntry) (force recursive : Bool) : Result RmEntry :=
  rm entry force recursive
inductive CopyNode where
  | file (bytes : List UInt8)
  | link (targetText : PathText) (target : CopyNode)
  | directory (children : List (Nat × CopyNode))

def cloneNode : Nat → Bool → CopyNode → CopyNode
  | 0, _, node => node
  | _fuel + 1, _followSymlinks, .file bytes => .file bytes
  | fuel + 1, followSymlinks, .link text target =>
      if followSymlinks then cloneNode fuel true target else .link text target
  | fuel + 1, followSymlinks, .directory children =>
      .directory (children.map fun pair => (pair.1, cloneNode fuel followSymlinks pair.2))

def resolvedPath (absolute pathExists finalLink keepLink parentIsSelf : Bool)
    (path real parentReal base : PathText) : PathText :=
  let normalized := if absolute then path else ['/'] ++ path
  if pathExists then
    if keepLink && finalLink then parentReal ++ base else real
  else if parentIsSelf then normalized else parentReal ++ base

def withinPath (inner outer : List Nat) : Bool :=
  inner == outer || outer.isPrefixOf inner

structure CopyCheckInput where
  sourceDirectory : Bool
  followSymlinks : Bool
  sourceFinalLink : Bool
  destinationInsideSource : Bool
  destinationExists : Bool
  force : Bool
  sameFile : Bool
  sourceInsideDestination : Bool
  deriving Repr, DecidableEq

def checkCopyMethod (input : CopyCheckInput) : Result Bool :=
  if input.sourceDirectory && (input.followSymlinks || !input.sourceFinalLink) &&
      input.destinationInsideSource then .error .argument false
  else if input.destinationExists then
    if input.force then
      if input.sameFile then .error .argument false
      else if input.sourceInsideDestination then .error .argument false
      else .ok true
    else .error .argument false
  else .ok false

def cptreeInternalMethod (fuel : Nat) (source : CopyNode) (followSymlinks : Bool) : CopyNode :=
  cloneNode fuel followSymlinks source

def cptreeStringMethod (sourceIsDirectory : Bool) (check : Result Bool)
    (fuel : Nat) (source : CopyNode) (followSymlinks : Bool) : Result CopyNode :=
  if !sourceIsDirectory then .error .argument source
  else match check with
    | .error error _ => .error error source
    | .ok _ => .ok (cptreeInternalMethod fuel source followSymlinks)

def cptreeAbstractMethod (converted : Result CopyNode) : Result CopyNode := converted

inductive CopySourceKind where | link | directory | file deriving Repr, DecidableEq

def cpMethod (check : Result Bool) (kind : CopySourceKind) (followSymlinks : Bool)
    (fuel : Nat) (source : CopyNode) : Result CopyNode :=
  match check with
  | .error error _ => .error error source
  | .ok _ => match kind with
    | .link => if followSymlinks then .ok (cloneNode fuel true source) else .ok source
    | .directory => .ok (cloneNode fuel followSymlinks source)
    | .file => .ok source

inductive RenameObservation where | success | enoent | ioError | otherError deriving Repr, DecidableEq
inductive MoveEvent where | check (force : Bool) | rename | copy | removeSource deriving Repr, DecidableEq

def mvReplaceMethod (sameFile : Bool) (first second : RenameObservation)
    (guard copyResult : Result Unit) : List MoveEvent × Result Unit :=
  if sameFile then ([], .error .argument ())
  else match first with
    | .success => ([.rename], .ok ())
    | .enoent => ([.rename], .error .io ())
    | .otherError => ([.rename], .error .io ())
    | .ioError => match guard with
      | .error error _ => ([.rename, .check true], .error error ())
      | .ok _ => match second with
        | .success => ([.rename, .check true, .rename], .ok ())
        | .enoent | .ioError => match copyResult with
          | .error error _ => ([.rename, .check true, .rename, .copy], .error error ())
          | .ok _ => ([.rename, .check true, .rename, .copy, .removeSource], .ok ())
        | .otherError => ([.rename, .check true, .rename], .error .io ())

def mvNoreplaceMethod (guard : Result Unit) (renameResult : RenameObservation)
    (copyResult : Result Unit) : List MoveEvent × Result Unit :=
  match guard with
  | .error error _ => ([.check false], .error error ())
  | .ok _ => match renameResult with
    | .success => ([.check false, .rename], .ok ())
    | .enoent => ([.check false, .rename], .error .io ())
    | .otherError => ([.check false, .rename], .error .io ())
    | .ioError => match copyResult with
      | .error error _ => ([.check false, .rename, .copy], .error error ())
      | .ok _ => ([.check false, .rename, .copy, .removeSource], .ok ())

def mvMethod (force sameFile : Bool) (first second : RenameObservation)
    (guard copyResult : Result Unit) : List MoveEvent × Result Unit :=
  JuliaLean.base.file.mvWith
    (fun (_ : Unit) (_ : Unit) => mvReplaceMethod sameFile first second guard copyResult)
    (fun (_ : Unit) (_ : Unit) => mvNoreplaceMethod guard first copyResult) () () force

inductive TouchPathEvent where | open | touch | close deriving Repr, DecidableEq
def touchPathMethod (path : PathText) (openSucceeds touchSucceeds : Bool) :
    List TouchPathEvent × Result PathText :=
  if !openSucceeds then ([.open], .error .io path)
  else if !touchSucceeds then ([.open, .touch, .close], .error .io path)
  else ([.open, .touch, .close], .ok path)
def deletionMode (mode : Nat) : Nat :=
  mode / 512 * 512 + (mode / 256 % 2) * 256 + (mode / 32 % 2) * 32 +
    (mode / 4 % 2) * 4 + 219

def prepareModes (isDirectory : Bool) (rootMode : Nat) (directoryModes : List Nat) : List Nat :=
  if isDirectory then deletionMode rootMode :: directoryModes.map deletionMode else []

def cleanupLater (old : Option Bool) (asap : Bool) : Bool := old.getD true && asap

structure CleanupItem where
  path : PathText
  asap : Bool
  present : Bool
  deletionSucceeds : Bool
  deriving Repr, DecidableEq

def purgeCleanup (force : Bool) (items : List CleanupItem) : List CleanupItem :=
  items.filter fun item =>
    if !item.present then false
    else if force || item.asap then !item.deletionSucceeds
    else true

def randomFilename (length : Nat) (draws : List Nat) : List Nat :=
  (draws.take length).map (· % 62)

inductive TempEvent where
  | forget (path : PathText)
  | closeFile
  | prepare (path : PathText)
  | remove (path : PathText)
  | retryLater (path : PathText)
  | purgeAll
  | collectGarbage
  | spawnCleaner
  | writeCleanupPaths
  | leakPipeDescriptor
  | closePipe
  | registerExitHook
  deriving Repr, DecidableEq

def tempCallbackEvents (kind : TempKind) (path : PathText) (cleanupSucceeds : Bool) : List TempEvent :=
  let events := [.forget path]
  match kind with
  | .name => events
  | .file => events ++ [.closeFile] ++ if cleanupSucceeds then [.remove path] else [.retryLater path]
  | .directory =>
      events ++ [.prepare path] ++ if cleanupSucceeds then [.remove path] else [.retryLater path]

def cleanupPostprocessEvents (hasPaths : Bool) : List TempEvent :=
  if hasPaths then [.spawnCleaner, .writeCleanupPaths, .leakPipeDescriptor, .closePipe] else []

def cleanupAtExitEvents (hasPaths : Bool) : List TempEvent :=
  [.purgeAll] ++ cleanupPostprocessEvents hasPaths

def delayedDeleteRefMethod (tempDirectory : PathText) : PathText :=
  tempDirectory ++ "/julia_delayed_deletes_ref".toList

inductive TempdirProbe where | missing | nondirectory | directory | accessError deriving Repr, DecidableEq
inductive TempdirWarning where | missing | nondirectory | accessError deriving Repr, DecidableEq

def tempdirMethod (replies : List BufferReply) (probe : TempdirProbe) :
    Result (PathText × Option TempdirWarning) :=
  match bufferPath replies with
  | .error error value => .error error (value, none)
  | .ok value => .ok (value, match probe with
      | .missing => some .missing
      | .nondirectory => some .nondirectory
      | .directory => none
      | .accessError => some .accessError)

def prepareForDeletionMethod (isDirectory : Bool) (rootMode : Nat) (directoryModes : List Nat) : List Nat :=
  prepareModes isDirectory rootMode directoryModes

def cleanupLaterMethod (old : Option Bool) (asap : Bool) (size maximum minimum : Nat) :
    Bool × Bool × Nat :=
  let stored := old.getD true && asap
  let purge := decide (size > maximum)
  let newMaximum := if purge then max minimum (2 * size) else maximum
  (stored, purge, newMaximum)

def cleanupForgetMethod (_present : Bool) : Bool := false
def cleanupPurgePrelockedMethod (force : Bool) (items : List CleanupItem) : List CleanupItem :=
  purgeCleanup force items
def cleanupPurgeAllMethod (mayNeedGc : Bool) : List TempEvent :=
  (if mayNeedGc then [.collectGarbage] else []) ++ [.purgeAll]
def cleanupPostprocessMethod (hasPaths : Bool) : List TempEvent := cleanupPostprocessEvents hasPaths
def cleanupAtexitMethod (hasPaths : Bool) : List TempEvent := cleanupAtExitEvents hasPaths
def filePostinitMethod (hooks : List TempEvent) : List TempEvent := hooks ++ [.registerExitHook]
def randFilenameMethod (length : Nat) (draws : List Nat) : List Nat := randomFilename length draws

inductive TempCreateEvent where
  | template (path : PathText)
  | createFile
  | createDirectory
  | registerCleanup (path : PathText)
  | openStream
  deriving Repr, DecidableEq

def mktempUnixMethod (path : PathText) (createSucceeds cleanup : Bool) :
    List TempCreateEvent × Result TempObject :=
  let events := [.template path, .createFile]
  if !createSucceeds then (events, .error .io { path, kind := .file, present := false })
  else
    let object : TempObject := { path, kind := .file, present := true, cleanupRegistered := cleanup }
    (events ++ (if cleanup then [.registerCleanup path] else []) ++ [.openStream], .ok object)

def mktempdirMethod (path : PathText) (createSucceeds cleanup : Bool) :
    List TempCreateEvent × Result TempObject :=
  let events := [.template path, .createDirectory]
  if !createSucceeds then (events, .error .io { path, kind := .directory, present := false })
  else
    let object : TempObject := { path, kind := .directory, present := true, cleanupRegistered := cleanup }
    (events ++ if cleanup then [.registerCleanup path] else [], .ok object)

def mktempCallbackMethod (path : PathText) (cleanupSucceeds : Bool) : List TempEvent :=
  tempCallbackEvents .file path cleanupSucceeds
def mktempdirCallbackMethod (path : PathText) (cleanupSucceeds : Bool) : List TempEvent :=
  tempCallbackEvents .directory path cleanupSucceeds

structure EntryModel where
  dir : List Nat
  name : Nat
  rawtype : Nat
  deriving Repr, DecidableEq

structure EntryProbe where
  link : Bool
  file : Bool
  directory : Bool
  fifo : Bool
  socket : Bool
  charDevice : Bool
  blockDevice : Bool
  deriving Repr, DecidableEq

def entryLess (left right : EntryModel) : Bool :=
  if left.dir == right.dir then decide (right.name < left.name) else decide (left.dir < right.dir)

def entryPath (entry : EntryModel) : List Nat := entry.dir ++ [entry.name]
def entryEqual (left right : EntryModel) : Bool := left == right
def entryUnknown (entry : EntryModel) : Bool := entry.rawtype == 0
def entryHashKey (entry : EntryModel) : List Nat := [entry.name] ++ entry.dir ++ [entry.rawtype]

def entryKind (rawtype expected : Nat) (probe : EntryProbe) : Bool :=
  if rawtype == 0 || rawtype == 3 then
    match expected with
    | 1 => probe.file
    | 2 => probe.directory
    | 3 => probe.link
    | 4 => probe.fifo
    | 5 => probe.socket
    | 6 => probe.charDevice
    | 7 => probe.blockDevice
    | _ => false
  else rawtype == expected

inductive IteratorKind where | string | entry deriving Repr, DecidableEq

structure IteratorState where
  dir : List Nat
  join : Bool
  kind : IteratorKind
  isOpen : Bool
  closed : Bool
  deriving Repr, DecidableEq

inductive IterValue where
  | string (path : List Nat)
  | entry (value : EntryModel)
  deriving Repr, DecidableEq

def openIterator (state : IteratorState) (openSucceeds : Bool) : Result IteratorState :=
  if state.isOpen then .ok state
  else if state.closed then .error .argument state
  else if openSucceeds then .ok { state with isOpen := true }
  else .error .io { state with closed := true }

def closeIterator (state : IteratorState) : IteratorState := { state with isOpen := false, closed := true }
def iteratorDone (state : IteratorState) : Bool := state.closed

def makeIterator (dir : List Nat) (join : Bool) (kind : IteratorKind) : IteratorState :=
  { dir, join, kind, isOpen := false, closed := false }

def iterateEntry (state : IteratorState) (next : Option (Nat × Nat)) : Result (Option IterValue × IteratorState) :=
  match next with
  | none => .ok (none, closeIterator state)
  | some (name, rawtype) =>
      let value := match state.kind with
        | .entry => .entry ⟨state.dir, name, rawtype⟩
        | .string => .string (if state.join then state.dir ++ [name] else [name])
      .ok (some value, state)

def direntryBasenameMethod (entry : EntryModel) : Nat := entry.name
def direntryDirnameMethod (entry : EntryModel) : List Nat := entry.dir
def direntryJoinpathMethod (entry : EntryModel) (parts : List Nat) : List Nat :=
  entry.dir ++ [entry.name] ++ parts
def direntryIslessMethod (left right : EntryModel) : Bool := entryLess left right
def direntryHashMethod (entry : EntryModel) : List Nat := [entry.rawtype, entry.name] ++ entry.dir
def direntryEqMethod (left right : EntryModel) : Bool := left == right
def direntryUnknownMethod (entry : EntryModel) : Bool := entry.rawtype == 0
def direntryLinkMethod (entry : EntryModel) (probe : EntryProbe) : Bool := entryKind entry.rawtype 3 probe
def direntryFileMethod (entry : EntryModel) (probe : EntryProbe) : Bool := entryKind entry.rawtype 1 probe
def direntryDirMethod (entry : EntryModel) (probe : EntryProbe) : Bool := entryKind entry.rawtype 2 probe
def direntryFifoMethod (entry : EntryModel) (probe : EntryProbe) : Bool := entryKind entry.rawtype 4 probe
def direntrySocketMethod (entry : EntryModel) (probe : EntryProbe) : Bool := entryKind entry.rawtype 5 probe
def direntryCharMethod (entry : EntryModel) (probe : EntryProbe) : Bool := entryKind entry.rawtype 6 probe
def direntryBlockMethod (entry : EntryModel) (probe : EntryProbe) : Bool := entryKind entry.rawtype 7 probe
def direntryRealpathMethod (entry : EntryModel) (resolved : List Nat) : List Nat × List Nat :=
  (entryPath entry, resolved)

def readdirDefaultMethod (pwd : List Nat) (join : Bool) (scan : List Nat) (sort : Bool) :
    List (List Nat) := readdir (if join then pwd else []) scan join sort
def readdirAbstractMethod (result : List (List Nat)) : List (List Nat) := result
def readdirObjectsMethod (dir : List Nat) (names rawtypes : List Nat) (sort : Bool) : List EntryModel :=
  let pairs := names.zip rawtypes
  let pairs := if sort then pairs.toArray.qsort (fun a b => a.1 < b.1) |>.toList else pairs
  pairs.map fun pair => ⟨dir, pair.1, pair.2⟩
def readdirObjectDefaultMethod (pwd : List Nat) (names rawtypes : List Nat) (sort : Bool) : List EntryModel :=
  readdirObjectsMethod pwd names rawtypes sort
def readdirObjectEntryMethod (entry : EntryModel) (names rawtypes : List Nat) (sort : Bool) : List EntryModel :=
  readdirObjectsMethod (entryPath entry) names rawtypes sort
def readdirEntryStringMethod (entry : EntryModel) (scan : List Nat) (join sort : Bool) : List (List Nat) :=
  readdir (entryPath entry) scan join sort

def iteratorCtorMethod (dir : List Nat) (join validType : Bool) (kind : IteratorKind) :
    Result IteratorState :=
  if validType then .ok (makeIterator dir join kind)
  else .error .argument (makeIterator dir join kind)
def eachentryOpenMethod (state : IteratorState) (succeeds : Bool) : Result IteratorState :=
  openIterator state succeeds
def iteratorCloseMethod (state : IteratorState) : IteratorState := closeIterator state
def iteratorSizeMethod : Nat := 0
def iteratorEltypeMethod (kind : IteratorKind) : IteratorKind := kind
def iteratorIsdoneMethod (state : IteratorState) : Bool := iteratorDone state
def iteratorIterateMethod (state : IteratorState) (next : Option (Nat × Nat)) := iterateEntry state next

def eachentryStringMethod (dir : List Nat) (join : Bool) : IteratorState :=
  makeIterator dir join .string
def eachentryEntryMethod (dir : List Nat) : IteratorState := makeIterator dir false .entry
def eachentryFromEntryStringMethod (entry : EntryModel) (join : Bool) : IteratorState :=
  eachentryStringMethod (entryPath entry) join
def eachentryFromEntryMethod (entry : EntryModel) : IteratorState := eachentryEntryMethod (entryPath entry)
def eachentryDefaultEntryMethod (pwd : List Nat) : IteratorState := eachentryEntryMethod pwd

inductive EachentryEvent where | create | callback | close deriving Repr, DecidableEq
def eachentryCallbackMethod : List EachentryEvent := [.create, .callback, .close]

inductive TryfResult (α : Type) where | value (value : α) | ioError | otherError

def walkTryfMethod {α : Type} (result : TryfResult α) : Result (Option α) :=
  match result with
  | .value value => .ok (some value)
  | .ioError => .ok none
  | .otherError => .error .io none

def walkdirWrapperMethod (parent : List Nat) (tree : DirTree) (topdown : Bool) : List WalkRow :=
  walkdir parent tree topdown
def walkdirInternalMethod (parent : List Nat) (tree : DirTree) (topdown : Bool) : List WalkRow :=
  if topdown then walkTop parent tree else walkBottom parent tree

def unitCall (returnCode : Int) : Result Unit :=
  if returnCode < 0 then .error .io () else .ok ()

def valueCall {α : Type} (returnCode : Int) (value fallback : α) : Result α :=
  if returnCode < 0 then .error .io fallback else .ok value

def copyFileFlags (force : Bool) : Nat := if force then 2 else 3

def symlinkFlags (windows dirTarget targetIsDirectory : Bool) : Nat :=
  if windows then if dirTarget || targetIsDirectory then 1 else 0 else 0

structure DiskStatModel where
  total : Nat
  available : Nat
  free : Nat
  deriving Repr, DecidableEq

inductive DiskField where | total | available | free deriving Repr, DecidableEq

def diskProperty (stats : DiskStatModel) : DiskField → Nat
  | .total => stats.total
  | .available => stats.available
  | .free => stats.free

def unlinkMethod (returnCode : Int) : Result Unit := unitCall returnCode
def renameMethod (newpath : PathText) (returnCode : Int) : Result PathText :=
  if returnCode < 0 then .error .io newpath else .ok newpath
def sendfilePathMethod (force : Bool) (returnCode : Int) : Nat × Result Unit :=
  (copyFileFlags force, unitCall returnCode)
def hardlinkMethod (returnCode : Int) : Result Unit := unitCall returnCode
def symlinkMethod (windows dirTarget targetIsDirectory : Bool) (returnCode : Int) :
    Nat × Result Unit :=
  (symlinkFlags windows dirTarget targetIsDirectory, unitCall returnCode)
inductive ReadlinkEvent where | allocate | call | cleanup | free deriving Repr, DecidableEq
def readlinkMethod (target fallback : PathText) (returnCode : Int) :
    List ReadlinkEvent × Result PathText :=
  let events := [.allocate, .call, .cleanup, .free]
  if returnCode < 0 then (events, .error .io fallback) else (events, .ok target)
def chmodMethod (path : PathText) (mode : Nat) (returnCode : Int)
    (recursive isDirectory : Bool) (tree : ModeTree) : Result (PathText × ModeTree) :=
  if returnCode < 0 then .error .io (path, tree)
  else .ok (path, if recursive && isDirectory then chmodTree mode true tree else tree)
def chownMethod (path : PathText) (returnCode : Int) : Result PathText :=
  if returnCode < 0 then .error .io path else .ok path
structure DiskStatFull where
  ftype : Nat
  blockSize : Nat
  blocks : Nat
  freeBlocks : Nat
  availableBlocks : Nat
  files : Nat
  freeFiles : Nat
  deriving Repr, DecidableEq

inductive DiskProperty where
  | ftype | blockSize | blocks | freeBlocks | availableBlocks | files | freeFiles
  | available | total | used
  deriving Repr, DecidableEq

def diskstatGetpropertyMethod (stats : DiskStatFull) : DiskProperty → Nat
  | .ftype => stats.ftype
  | .blockSize => stats.blockSize
  | .blocks => stats.blocks
  | .freeBlocks => stats.freeBlocks
  | .availableBlocks => stats.availableBlocks
  | .files => stats.files
  | .freeFiles => stats.freeFiles
  | .available => stats.blockSize * stats.availableBlocks
  | .total => stats.blockSize * stats.blocks
  | .used => stats.blockSize * stats.blocks - stats.blockSize * stats.availableBlocks

def diskstatPropertynamesMethod : List DiskProperty :=
  [.ftype, .blockSize, .blocks, .freeBlocks, .availableBlocks, .files, .freeFiles,
   .available, .total, .used]
def diskstatShowMethod (stats : DiskStatFull) : Nat × Nat × Nat :=
  (diskstatGetpropertyMethod stats .total, diskstatGetpropertyMethod stats .used,
   diskstatGetpropertyMethod stats .available)
def diskstatMethod (returnCode : Int) (loaded fallback : DiskStatFull) : Result DiskStatFull :=
  if returnCode < 0 then .error .io fallback else .ok loaded

end JuliaLean.Files.Coverage

