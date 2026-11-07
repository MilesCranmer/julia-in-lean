import JuliaLean.Registry.Types
import JuliaLean.Core
import JuliaLean.base.io
import JuliaLean.base.int
import JuliaLean.base.float
import JuliaLean.base.c
import JuliaLean.base.filesystem

/-!
# Model of `base/libc.jl`

Typed models of the `Base.Libc` module in Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`: file
descriptors (`RawFD`, `dup`), libc `FILE` handles, sleeping and time (`TimeVal`, `TmStruct`,
`strftime`, `strptime`, `time`), process and host queries, `errno`/`strerror`, the Windows error
helpers, C memory allocation, randomness (`rand`, `srand`, `getrandom!`), `mkfifo`, and the
password and group database lookups.

Every C call, pointer load and string conversion is an operation of `LibcOps`; no laws are assumed
about them. The platform aliases `Clong`, `Culong` and `Cwchar_t` are the installed
`JuliaLean.base.c.cLongTypes`, and `Cmode_t` is the width that `base/c.jl` selected. `TmStruct` is a
mutable Julia struct; a call that lets C write into a caller's `TmStruct` returns its contents
afterwards. Generic `Integer` arguments enter by their exact value and are converted with Julia's
exact `convert`, which raises `InexactError` out of range; generic `Real` arguments go through the
typed `RealOps`.
-/

namespace JuliaLean.base.libc

open JuliaLean
open JuliaLean.base.io (M Error whileLoop)

abbrev I32 := JInt .i32
abbrev I64 := JInt .i64
abbrev U16 := JInt .u16
abbrev U32 := JInt .u32
abbrev U64 := JInt .u64
abbrev Byte := JInt .u8
abbrev F64 := JuliaLean.base.float.FV .f64

def argumentError (message : String) : Error := .jl (.argumentError message)

/-- Julia's exact `convert(T, x)` of an integer value, with `InexactError` out of range. -/
def convertTo {World : Type} (t : IntTy) (value : Int) : M World (JInt t) :=
  JuliaLean.base.io.liftJl (JInt.convert "convert" t value)

/-- `x % T` for an integer value: the value modulo `2^bits(T)`. -/
def remTo (t : IntTy) (value : Int) : JInt t := JInt.wrap t value

/-- Operations on a generic `Real` argument (from `float.jl`, `rounding.jl` and the promotion
rules). -/
structure RealOps (World R : Type) where
  /-- `round(UInt32, s * scale)`, which raises `InexactError` out of range. -/
  roundUInt32Scaled : R → F64 → M World U32
  /-- `floor(t)`. -/
  floor : R → M World R
  /-- `convert(Int, t)` for the `Ref{Int}` argument of a `ccall`. -/
  toInt : R → M World I64

/-- The fields of a `TmStruct`, all `Int32`; `_10` to `_14` pad the C struct. -/
structure TmStruct where
  sec : I32
  min : I32
  hour : I32
  mday : I32
  month : I32
  year : I32
  wday : I32
  yday : I32
  isdst : I32
  pad10 : I32
  pad11 : I32
  pad12 : I32
  pad13 : I32
  pad14 : I32
  deriving DecidableEq

/-- Operations supplied by libc, libuv, the runtime and later-loaded Base files. -/
structure LibcOps (World IO Ptr CStr WStr WChar RefU64 : Type) where
  isWindows : Bool
  isUnix : Bool
  isApple : Bool
  /-- The `Cmode_t` integer type that `base/c.jl` selected (Unix only). -/
  cmodeType : IntTy
  errors : JuliaLean.base.filesystem.ErrorOps World
  nullPtr : Ptr
  isNull : Ptr → Bool
  printString : IO → String → M World Unit
  printInt32 : IO → I32 → M World Unit
  /-- `string(::Int32)`. -/
  int32String : I32 → M World String
  /-- `show(io, ::UInt)`. -/
  showUInt : IO → U64 → M World Unit
  ptrToUInt : Ptr → U64
  /-- `dup`/`_dup` and `dup2`/`_dup2`. -/
  dup : I32 → M World I32
  dup2 : I32 → I32 → M World I32
  getOsfhandle : I32 → M World Ptr
  getCurrentProcess : Unit → M World Ptr
  /-- `DuplicateHandle(process, src, process, new_handle, 0, false, DUPLICATE_SAME_ACCESS)`, with
  the handle it writes. -/
  duplicateHandle : Ptr → Ptr → Ptr → U32 → M World (I32 × Ptr)
  openOsfhandle : Ptr → I32 → M World I32
  closeFd : I32 → M World I32
  getLastErrorCall : Unit → M World U32
  /-- `fd(s)`, `isreadable(s)`, `iswritable(s)` and `position(s)` of an `IO`. -/
  ioFd : IO → M World Int
  ioIsReadable : IO → M World Bool
  ioIsWritable : IO → M World Bool
  ioPosition : IO → M World Int
  /-- `Cstring` and `Cwstring` conversions of a `String`, which reject embedded NULs. -/
  toCString : String → M World CStr
  toCWString : String → M World WStr
  fdopen : I32 → CStr → M World Ptr
  fclose : Ptr → M World I32
  fseek : Ptr → Int → I32 → M World I32
  ftell : Ptr → M World Int
  flushCstdio : Unit → M World Unit
  usleep : U32 → M World I32
  sleepWindows : U32 → M World Unit
  /-- `jl_gettimeofday`, with the `TimeVal` it writes. -/
  gettimeofday : Unit → M World (I32 × I64 × I64)
  /-- `localtime_r(t, tm)`: the `TmStruct` contents afterwards. -/
  localtime : I64 → TmStruct → M World TmStruct
  /-- `wcsftime` into a 128-element `Cwchar_t` buffer: the count and the buffer. -/
  wcsftime : U64 → WStr → TmStruct → M World (U64 × List WChar)
  /-- `transcode(String, ::Vector{Cwchar_t})`. -/
  wcharString : List WChar → M World String
  /-- `strptime(timestr, fmt, tm)`: whether the result is `C_NULL`, and `tm` afterwards. -/
  strptime : CStr → CStr → TmStruct → M World (Bool × TmStruct)
  /-- `mktime(tm)`: its result and `tm` afterwards. -/
  mktime : TmStruct → M World (I64 × TmStruct)
  clockNow : Unit → M World F64
  getpid : Unit → M World I32
  /-- `gethostname` into a 256-byte buffer, with the bytes it writes. -/
  gethostname : U64 → M World (I32 × List Byte)
  /-- `unsafe_string(pointer(hn))`: the bytes up to the first NUL. -/
  bytesString : List Byte → M World String
  jlErrno : Unit → M World I32
  jlSetErrno : I32 → M World Unit
  strerror : I32 → M World String
  /-- `FormatMessageW(...)`: the length and the buffer pointer it writes. -/
  formatMessageW : U32 → U32 → M World (U32 × Ptr)
  /-- `unsafe_copyto!` of `len` `UInt16`s from a pointer into a fresh buffer. -/
  loadUInt16s : Ptr → U32 → M World (List U16)
  localFree : Ptr → M World Ptr
  utf16String : List U16 → M World String
  free : Ptr → M World Unit
  cstringPtr : CStr → Ptr
  cwstringPtr : WStr → Ptr
  malloc : U64 → M World Ptr
  realloc : Ptr → U64 → M World Ptr
  calloc : U64 → U64 → M World Ptr
  /-- `uv_random` filling an array or `RefValue`, and `sizeof` of it. -/
  uvRandom : {A : Type} → A → U64 → M World I32
  sizeOf : {A : Type} → A → M World U64
  newRefU64 : Unit → M World RefU64
  getRefU64 : RefU64 → M World U64
  jlRand : Unit → M World U64
  jlSrand : U64 → M World Unit
  mkfifo : CStr → Int → M World I32
  /-- `uv_os_get_passwd`/`uv_os_get_passwd2` writing a `Cpasswd`: the status and its fields. -/
  getPasswd : Unit → M World (I32 × Ptr × Int × Int × Ptr × Ptr × Ptr)
  getPasswdUid : Int → M World (I32 × Ptr × Int × Int × Ptr × Ptr × Ptr)
  freePasswd : (Ptr × Int × Int × Ptr × Ptr × Ptr) → M World Unit
  /-- `uv_os_get_group` writing a `Cgroup`: the status and its fields. -/
  getGroup : Int → M World (I32 × Ptr × Int × Ptr)
  freeGroup : (Ptr × Int × Ptr) → M World Unit
  unsafeString : Ptr → M World String
  /-- `unsafe_load(p::Ptr{Cstring}, i)`. -/
  loadPtr : Ptr → Nat → M World Ptr
  getuid : Unit → M World Int
  geteuid : Unit → M World Int
  getegid : Unit → M World Int

section
variable {World IO Ptr CStr WStr WChar RefU64 : Type}
variable (ops : LibcOps World IO Ptr CStr WStr WChar RefU64)

def clongTy : IntTy := (JuliaLean.base.c.cLongTypes ops.isWindows).clong
def culongTy : IntTy := (JuliaLean.base.c.cLongTypes ops.isWindows).culong

-- Reason: Module declaration, imports, the export list and the generated `errno_h.jl` include are load-time metadata.
-- UNTRANSLATED
-- Source: base/libc.jl:1-21 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- module Libc
-- @doc """
-- Interface to libc, the C standard library.
-- """ Libc
-- 
-- import Base: transcode, windowserror, show
-- # these need to be defined separately for bootstrapping but belong to Libc
-- import Base: memcmp, memcpy, memmove, memset
-- import Core.Intrinsics: bitcast
-- 
-- export FILE, TmStruct, strftime, strptime, getpid, gethostname, free, malloc, memcpy,
--     memmove, memset, calloc, realloc, errno, strerror, flush_cstdio, systemsleep, time,
--     transcode, mkfifo
-- if Sys.iswindows()
--     export GetLastError, FormatMessage
-- end
-- 
-- include(string(Base.BUILDROOT, "errno_h.jl"))  # include($BUILDROOT/base/errno_h.jl)
-- 
-- /Source

/--
Julia source: base/libc.jl:22-38 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
## RawFD ##

# Wrapper for an OS file descriptor (on both Unix and Windows)
"""
    RawFD

Primitive type which wraps the native OS file descriptor.
`RawFD`s can be passed to methods like [`stat`](@ref) to
discover information about the underlying file, and can
also be used to open streams, with the `RawFD` describing
the OS file backing the stream.
"""
primitive type RawFD 32 end
RawFD(fd::Integer) = bitcast(RawFD, Cint(fd))
RawFD(fd::RawFD) = fd
Base.cconvert(::Type{Cint}, fd::RawFD) = bitcast(Cint, fd)

```
-/
structure RawFD where
  fd : I32
  deriving DecidableEq

def rawFDOfInteger (fd : Int) : M World RawFD := do
  pure ⟨← convertTo .i32 fd⟩

def rawFDOfRawFD (fd : RawFD) : RawFD := fd

def cconvertCint (fd : RawFD) : I32 := fd.fd

/--
Julia source: base/libc.jl:39-50 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    dup(src::RawFD[, target::RawFD])::RawFD

Duplicate the file descriptor `src` so that the duplicate refers to the same OS
resource (e.g. a file or socket). A `target` file descriptor may optionally
be passed to use for the new duplicate.
"""
dup(x::RawFD) = ccall((@static Sys.iswindows() ? :_dup : :dup), RawFD, (RawFD,), x)
dup(src::RawFD, target::RawFD) = systemerror("dup", -1 ==
    ccall((@static Sys.iswindows() ? :_dup2 : :dup2), Int32,
                (RawFD, RawFD), src, target))

```
-/
def dup (x : RawFD) : M World RawFD := do
  pure ⟨← ops.dup x.fd⟩

def dupTo (src target : RawFD) : M World Unit := do
  let r ← ops.dup2 src.fd target.fd
  ops.errors.systemError "dup" (-1 == r.val)

/--
Julia source: base/libc.jl:51-52 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, fd::RawFD) = print(io, "RawFD(", bitcast(Int32, fd), ')')  # avoids invalidation via show_default

```
-/
def showRawFD (io : IO) (fd : RawFD) : M World Unit := do
  ops.printString io "RawFD("
  ops.printInt32 io fd.fd
  ops.printString io ")"

/--
Julia source: base/libc.jl:53-88 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Wrapper for an OS file descriptor (for Windows)
if Sys.iswindows()
    @doc """
        WindowsRawSocket

    Primitive type which wraps the native Windows file `HANDLE`.
    """
    primitive type WindowsRawSocket sizeof(Ptr) * 8 end # On Windows file descriptors are HANDLE's and 64-bit on 64-bit Windows
    WindowsRawSocket(handle::Ptr{Cvoid}) = bitcast(WindowsRawSocket, handle)
    WindowsRawSocket(handle::WindowsRawSocket) = handle

    Base.cconvert(::Type{Ptr{Cvoid}}, fd::WindowsRawSocket) = bitcast(Ptr{Cvoid}, fd)
    show(io::IO, fd::WindowsRawSocket) = (print(io, "WindowsRawSocket("); show(io, bitcast(UInt, fd)); print(io, ')'))  # avoids invalidation via show_default
    _get_osfhandle(fd::RawFD) = ccall(:_get_osfhandle, WindowsRawSocket, (RawFD,), fd)
    _get_osfhandle(fd::WindowsRawSocket) = fd
    function dup(src::WindowsRawSocket)
        new_handle = Ref(WindowsRawSocket(Ptr{Cvoid}(-1)))
        my_process = ccall(:GetCurrentProcess, stdcall, Ptr{Cvoid}, ())
        DUPLICATE_SAME_ACCESS = 0x2
        status = ccall(:DuplicateHandle, stdcall, Int32,
            (Ptr{Cvoid}, WindowsRawSocket, Ptr{Cvoid}, Ptr{WindowsRawSocket}, UInt32, Int32, UInt32),
            my_process, src, my_process, new_handle, 0, false, DUPLICATE_SAME_ACCESS)
        windowserror("dup failed", status == 0)
        return new_handle[]
    end
    function dup(src::WindowsRawSocket, target::RawFD)
        fd = ccall(:_open_osfhandle, RawFD, (WindowsRawSocket, Int32), dup(src), 0)
        dup(fd, target)
        ccall(:_close, Int32, (RawFD,), fd)
        nothing
    end

else
    _get_osfhandle(fd::RawFD) = fd
end

```
-/
structure WindowsRawSocket (P : Type) where
  handle : P

def windowsRawSocketOfPtr (handle : Ptr) : WindowsRawSocket Ptr := ⟨handle⟩

def windowsRawSocketOfSelf (handle : WindowsRawSocket Ptr) : WindowsRawSocket Ptr := handle

def cconvertPtr (fd : WindowsRawSocket Ptr) : Ptr := fd.handle

def showWindowsRawSocket (io : IO) (fd : WindowsRawSocket Ptr) : M World Unit := do
  ops.printString io "WindowsRawSocket("
  ops.showUInt io (ops.ptrToUInt fd.handle)
  ops.printString io ")"

def getOsfhandleWindows (fd : RawFD) : M World (WindowsRawSocket Ptr) := do
  pure ⟨← ops.getOsfhandle fd.fd⟩

def getOsfhandleSocket (fd : WindowsRawSocket Ptr) : WindowsRawSocket Ptr := fd

def dupSocket (src : WindowsRawSocket Ptr) : M World (WindowsRawSocket Ptr) := do
  let myProcess ← ops.getCurrentProcess ()
  let duplicateSameAccess : U32 := JInt.lit .u32 0x2
  let (status, newHandle) ← ops.duplicateHandle myProcess src.handle myProcess duplicateSameAccess
  if status.val == 0 then
    let code ← ops.getLastErrorCall ()
    JuliaLean.base.filesystem.eliminateEmpty (ops.errors.windowsError "dup failed" code)
  pure ⟨newHandle⟩

def dupSocketTo (src : WindowsRawSocket Ptr) (target : RawFD) : M World Unit := do
  let fd ← ops.openOsfhandle (← dupSocket ops src).handle (JInt.lit .i32 0)
  dupTo ops ⟨fd⟩ target
  let _ ← ops.closeFd fd
  pure ()

/-- `_get_osfhandle(fd::RawFD)` on Unix. -/
def getOsfhandleUnix (fd : RawFD) : RawFD := fd

/--
Julia source: base/libc.jl:89-122 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
## FILE (not auto-finalized) ##

"""
    FILE(::Ptr)
    FILE(::IO)

A libc `FILE*`, representing an opened file.

It can be passed as a `Ptr{FILE}` argument to [`ccall`](@ref) and also supports
[`seek`](@ref), [`position`](@ref) and [`close`](@ref).

A `FILE` can be constructed from an ordinary `IO` object, provided it is an open file. It
must be closed afterward.

# Examples
```jldoctest
julia> using Base.Libc

julia> mktemp() do _, io
           # write to the temporary file using `puts(char*, FILE*)` from libc
           file = FILE(io)
           ccall(:fputs, Cint, (Cstring, Ptr{FILE}), "hello world", file)
           close(file)
           # read the file again
           seek(io, 0)
           read(io, String)
       end
"hello world"
```
"""
struct FILE
    ptr::Ptr{Cvoid}
end

````
-/
structure FILE (P : Type) where
  ptr : P

/--
Julia source: base/libc.jl:123-125 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
modestr(s::IO) = modestr(isreadable(s), iswritable(s))
modestr(r::Bool, w::Bool) = r ? (w ? "r+" : "r") : (w ? "w" : throw(ArgumentError("neither readable nor writable")))

```
-/
def modestrBool (r w : Bool) : M World String :=
  if r then pure (if w then "r+" else "r")
  else if w then pure "w"
  else throw (argumentError "neither readable nor writable")

def modestr (s : IO) : M World String := do
  modestrBool (← ops.ioIsReadable s) (← ops.ioIsWritable s)

/--
Julia source: base/libc.jl:126-131 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function FILE(fd::RawFD, mode)
    FILEp = ccall((@static Sys.iswindows() ? :_fdopen : :fdopen), Ptr{Cvoid}, (Cint, Cstring), fd, mode)
    systemerror("fdopen", FILEp == C_NULL)
    FILE(FILEp)
end

```
-/
def fileOfFd (fd : RawFD) (mode : String) : M World (FILE Ptr) := do
  let cmode ← ops.toCString mode
  let filep ← ops.fdopen fd.fd cmode
  ops.errors.systemError "fdopen" (ops.isNull filep)
  pure ⟨filep⟩

/-- `Clong` conversion of an integer argument. -/
def toClong (value : Int) : M World Int := do
  pure (← convertTo (clongTy ops) value).val

/--
Julia source: base/libc.jl:141-146 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.seek(h::FILE, offset::Integer)
    systemerror("fseek", ccall(:fseek, Cint, (Ptr{Cvoid}, Clong, Cint),
                               h.ptr, offset, 0) != 0)
    h
end

```
-/
def seekFile (h : FILE Ptr) (offset : Int) : M World (FILE Ptr) := do
  let coffset ← toClong ops offset
  ops.errors.systemError "fseek" ((← ops.fseek h.ptr coffset (JInt.lit .i32 0)).val != 0)
  pure h

/--
Julia source: base/libc.jl:147-148 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.position(h::FILE) = ccall(:ftell, Clong, (Ptr{Cvoid},), h.ptr)

```
-/
def positionFile (h : FILE Ptr) : M World Int := ops.ftell h.ptr

/--
Julia source: base/libc.jl:132-137 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function FILE(s::IO)
    f = FILE(dup(RawFD(fd(s))),modestr(s))
    seek(f, position(s))
    f
end

```
-/
def fileOfIO (s : IO) : M World (FILE Ptr) := do
  let fd ← rawFDOfInteger (← ops.ioFd s)
  let f ← fileOfFd ops (← dup ops fd) (← modestr ops s)
  let _ ← seekFile ops f (← ops.ioPosition s)
  pure f

/--
Julia source: base/libc.jl:138-140 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.unsafe_convert(T::Union{Type{Ptr{Cvoid}},Type{Ptr{FILE}}}, f::FILE) = convert(T, f.ptr)
Base.close(f::FILE) = systemerror("fclose", ccall(:fclose, Cint, (Ptr{Cvoid},), f.ptr) != 0)

```
-/
def unsafeConvertFile (f : FILE Ptr) : Ptr := f.ptr

def closeFile (f : FILE Ptr) : M World Unit := do
  ops.errors.systemError "fclose" ((← ops.fclose f.ptr).val != 0)

/--
Julia source: base/libc.jl:149-157 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# flush C stdio output from external libraries

"""
    flush_cstdio()

Flushes the C `stdout` and `stderr` streams (which may have been written to by external C code).
"""
flush_cstdio() = ccall(:jl_flush_cstdio, Cvoid, ())

```
-/
def flushCstdio : M World Unit := ops.flushCstdio ()

/--
Julia source: base/libc.jl:158-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
## time-related functions ##

# TODO: check for usleep errors?
if Sys.isunix()
    systemsleep(s::Real) = ccall(:usleep, Int32, (UInt32,), round(UInt32, s*1e6))
elseif Sys.iswindows()
    function systemsleep(s::Real)
        ccall(:Sleep, stdcall, Cvoid, (UInt32,), round(UInt32, s * 1e3))
        return Int32(0)
    end
else
    error("systemsleep undefined for this OS")
end
```
-/
def systemsleepUnix {R : Type} (realOps : RealOps World R) (s : R) : M World I32 := do
  ops.usleep (← realOps.roundUInt32Scaled s (JuliaLean.Promotion.Fl.ofBits 0x412E848000000000))

def systemsleepWindows {R : Type} (realOps : RealOps World R) (s : R) : M World I32 := do
  ops.sleepWindows (← realOps.roundUInt32Scaled s (JuliaLean.Promotion.Fl.ofBits 0x408F400000000000))
  pure (JInt.lit .i32 0)

/-- `systemsleep(s)`: the method defined for the platform; on any other platform loading
`libc.jl` itself raises the error. -/
def systemsleep {R : Type} (realOps : RealOps World R) (s : R) : M World I32 :=
  if ops.isUnix then systemsleepUnix ops realOps s
  else if ops.isWindows then systemsleepWindows ops realOps s
  else throw (.errorException "systemsleep undefined for this OS")

-- Reason: A docstring attached to the `systemsleep` function; it defines no method.
-- UNTRANSLATED
-- Source: base/libc.jl:171-181 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     systemsleep(s::Real)
-- 
-- Suspends execution for `s` seconds.
-- This function does not yield to Julia's scheduler and therefore blocks
-- the Julia thread that it is running on for the duration of the sleep time.
-- 
-- See also [`sleep`](@ref).
-- """
-- systemsleep
-- 
-- /Source

/--
Julia source: base/libc.jl:182-193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct TimeVal
   sec::Int64
   usec::Int64
end

function TimeVal()
    tv = Ref{TimeVal}()
    status = ccall(:jl_gettimeofday, Cint, (Ref{TimeVal},), tv)
    status != 0 && error("unable to determine current time: ", status)
    return tv[]
end

```
-/
structure TimeVal where
  sec : I64
  usec : I64

def timeValNow : M World TimeVal := do
  let (status, sec, usec) ← ops.gettimeofday ()
  if status.val != 0 then
    throw (.errorException ("unable to determine current time: " ++ (← ops.int32String status)))
  pure ⟨sec, usec⟩

/--
Julia source: base/libc.jl:194-228 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    TmStruct([seconds])

Convert a number of seconds since the epoch to broken-down format, with fields `sec`, `min`,
`hour`, `mday`, `month`, `year`, `wday`, `yday`, and `isdst`.
"""
mutable struct TmStruct
    sec::Int32
    min::Int32
    hour::Int32
    mday::Int32
    month::Int32
    year::Int32
    wday::Int32
    yday::Int32
    isdst::Int32
    # on some platforms the struct is 14 words, even though 9 are specified
    _10::Int32
    _11::Int32
    _12::Int32
    _13::Int32
    _14::Int32

    TmStruct(sec, min, hour, mday, month, year, wday, yday, isdst) =
        new(sec, min, hour, mday, month, year, wday, yday, isdst, 0,0,0,0,0)
    TmStruct() = new(0,0,0,0,0,0,0,0,0,0,0,0,0,0)
    function TmStruct(t::Real)
        t = floor(t)
        tm = TmStruct()
        # TODO: add support for UTC via gmtime_r()
        ccall(:localtime_r, Ptr{TmStruct}, (Ref{Int}, Ref{TmStruct}), t, tm)
        return tm
    end
end

```
-/
def TmStruct.ofFields (sec min hour mday month year wday yday isdst : I32) : TmStruct :=
  ⟨sec, min, hour, mday, month, year, wday, yday, isdst, JInt.lit .i32 0, JInt.lit .i32 0,
    JInt.lit .i32 0, JInt.lit .i32 0, JInt.lit .i32 0⟩

def TmStruct.zero : TmStruct :=
  TmStruct.ofFields (JInt.lit .i32 0) (JInt.lit .i32 0) (JInt.lit .i32 0) (JInt.lit .i32 0)
    (JInt.lit .i32 0) (JInt.lit .i32 0) (JInt.lit .i32 0) (JInt.lit .i32 0) (JInt.lit .i32 0)

def tmStructOfReal {R : Type} (realOps : RealOps World R) (t : R) : M World TmStruct := do
  let t ← realOps.floor t
  let tm := TmStruct.zero
  ops.localtime (← realOps.toInt t) tm

/-- The time argument of `strftime`: a number of seconds or a `TmStruct`. -/
inductive TimeArg (R : Type) where
  | seconds (value : R)
  | tm (value : TmStruct)

/--
Julia source: base/libc.jl:229-246 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    strftime([format], time)

Convert time, given as a number of seconds since the epoch or a `TmStruct`, to a formatted
string using the given format. Supported formats are the same as those in the standard C
library.
"""
strftime(t) = strftime("%c", t)
strftime(fmt::AbstractString, t::Real) = strftime(fmt, TmStruct(t))
# Use wcsftime instead of strftime to support different locales
function strftime(fmt::AbstractString, tm::TmStruct)
    wctimestr = Vector{Cwchar_t}(undef, 128)
    n = ccall(:wcsftime, Csize_t, (Ptr{Cwchar_t}, Csize_t, Cwstring, Ref{TmStruct}),
              wctimestr, length(wctimestr), fmt, tm)
    n == 0 && return ""
    return transcode(String, resize!(wctimestr, n))
end

```
-/
def strftimeTm (fmt : String) (tm : TmStruct) : M World String := do
  let wfmt ← ops.toCWString fmt
  let (n, wctimestr) ← ops.wcsftime (JInt.lit .u64 128) wfmt tm
  if n.val == 0 then return ""
  ops.wcharString (wctimestr.take n.val.toNat)

def strftimeReal {R : Type} (realOps : RealOps World R) (fmt : String) (t : R) : M World String := do
  strftimeTm ops fmt (← tmStructOfReal ops realOps t)

def strftimeDefault {R : Type} (realOps : RealOps World R) (t : TimeArg R) : M World String :=
  match t with
  | .seconds value => strftimeReal ops realOps "%c" value
  | .tm value => strftimeTm ops "%c" value

/-- The bytes of `b"aAjw"`. -/
def weekdayYeardayBytes : List Nat := [97, 65, 106, 119]

/-- `shouldcallmktime(s)`, the local function of `strptime` on Apple platforms. -/
def shouldCallMktime (s : String) : M World Bool := do
  let c := s.toUTF8.toList.map (fun b => b.toNat)
  let n := c.length
  let percent := 37
  let byteAt := fun (k : Nat) => c.getD (k - 1) 0
  let findFrom := fun (start : Nat) =>
    ((List.range c.length).find? (fun k => k + 1 ≥ start && byteAt (k + 1) == percent)).map (· + 1)
  whileLoop (fun (i : Option Nat) => do
    match i with
    | none => return Sum.inl true
    | some i =>
      if i ≥ n then return Sum.inl true
      if i == 1 || byteAt (i - 1) != percent then
        if weekdayYeardayBytes.contains (byteAt (i + 1)) then return Sum.inl false
        if i + 2 ≤ n && byteAt (i + 1) == 79 && byteAt (i + 2) == 119 then return Sum.inl false
      return Sum.inr (findFrom (i + 1))) (findFrom 1)

/--
Julia source: base/libc.jl:247-308 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    strptime([format], timestr)

Parse a formatted time string into a `TmStruct` giving the seconds, minute, hour, date, etc.
Supported formats are the same as those in the standard C library. On some platforms,
timezones will not be parsed correctly. If the result of this function will be passed to
`time` to convert it to seconds since the epoch, the `isdst` field should be filled in
manually. Setting it to `-1` will tell the C library to use the current system settings to
determine the timezone.
"""
strptime(timestr::AbstractString) = strptime("%c", timestr)
function strptime(fmt::AbstractString, timestr::AbstractString)
    tm = TmStruct()
    r = ccall(:strptime, Cstring, (Cstring, Cstring, Ref{TmStruct}), timestr, fmt, tm)
    # the following would tell mktime() that this is a local time, and that
    # it should try to guess the timezone. not sure if/how this should be
    # exposed in the API.
    # tm.isdst = -1
    if r == C_NULL
        # TODO: better error message
        throw(ArgumentError("invalid arguments"))
    end
    @static if Sys.isapple()
        function shouldcallmktime(s::AbstractString)
            # Equivalent to !occursin(r"([^%]|^)%(a|A|j|w|Ow)"a, s), but
            # without regex since this is not available yet

            c = Base.utf8units(s)
            N = length(c)
            i = findfirst(==(UInt8('%')), c)

            while true
                isnothing(i) && break
                i >= N && break

                # Ignore % following after another %
                if i == firstindex(c) || c[i-1] != UInt8('%')
                    # Detect %a, %A, %j, %w, %Ow
                    if c[i+1] in b"aAjw"
                        return false
                    end
                    if (checkbounds(Bool, c, i+2) &&
                        c[i+1] == UInt8('O') &&
                        c[i+2] == UInt8('w')
                    )
                        return false
                    end
                end

                i = findnext(==(UInt8('%')), c, i+1)
            end
            return true
        end
        # if we didn't explicitly parse the weekday or year day, use mktime
        # to fill them in automatically.
        if shouldcallmktime(fmt)
            ccall(:mktime, Int, (Ref{TmStruct},), tm)
        end
    end
    return tm
end

```
-/
def strptime (fmt timestr : String) : M World TmStruct := do
  let tm := TmStruct.zero
  let ctimestr ← ops.toCString timestr
  let cfmt ← ops.toCString fmt
  let (isNullResult, tm) ← ops.strptime ctimestr cfmt tm
  if isNullResult then throw (argumentError "invalid arguments")
  if ops.isApple then
    if ← shouldCallMktime fmt then
      let (_, tm) ← ops.mktime tm
      return tm
  pure tm

def strptimeDefault (timestr : String) : M World TmStruct :=
  strptime ops "%c" timestr

/--
Julia source: base/libc.jl:309-317 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# system date in seconds

"""
    time(t::TmStruct)::Float64

Convert a `TmStruct` struct to a number of seconds since the epoch.
"""
time(tm::TmStruct) = Float64(ccall(:mktime, Int, (Ref{TmStruct},), tm))

```
-/
def timeOfTm (tm : TmStruct) : M World (F64 × TmStruct) := do
  let (seconds, tm) ← ops.mktime tm
  pure (JuliaLean.base.float.floatOfInt .f64 seconds, tm)

/--
Julia source: base/libc.jl:318-326 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    time()::Float64

Get the system time in seconds since the epoch, with fairly high (typically, microsecond) resolution.

See also [`time_ns`](@ref).
"""
time() = ccall(:jl_clock_now, Float64, ())

```
-/
def time : M World F64 := ops.clockNow ()

/--
Julia source: base/libc.jl:327-335 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
## process-related functions ##

"""
    getpid()::Int32

Get Julia's process ID.
"""
getpid() = ccall(:uv_os_getpid, Int32, ())

```
-/
def getpid : M World I32 := ops.getpid ()

/--
Julia source: base/libc.jl:336-353 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
## network functions ##

"""
    gethostname()::String

Get the local machine's host name.
"""
function gethostname()
    hn = Vector{UInt8}(undef, 256)
    err = @static if Sys.iswindows()
        ccall(:gethostname, stdcall, Int32, (Ptr{UInt8}, UInt32), hn, length(hn))
    else
        ccall(:gethostname, Int32, (Ptr{UInt8}, UInt), hn, length(hn))
    end
    systemerror("gethostname", err != 0)
    return GC.@preserve hn unsafe_string(pointer(hn))
end

```
-/
def gethostname : M World String := do
  let (err, hn) ← ops.gethostname (JInt.lit .u64 256)
  ops.errors.systemError "gethostname" (err.val != 0)
  ops.bytesString hn

/--
Julia source: base/libc.jl:354-368 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
## system error handling ##

"""
    errno([code])

Get the value of the C library's `errno`. If an argument is specified, it is used to set the
value of `errno`.

The value of `errno` is only valid immediately after a `ccall` to a C library routine that
sets it. Specifically, you cannot call `errno` at the next prompt in a REPL, because lots of
code is executed between prompts.
"""
errno() = ccall(:jl_errno, Cint, ())
errno(e::Integer) = ccall(:jl_set_errno, Cvoid, (Cint,), e)

```
-/
def errno : M World I32 := ops.jlErrno ()

def setErrno (e : Int) : M World Unit := do
  ops.jlSetErrno (← convertTo .i32 e)

/--
Julia source: base/libc.jl:369-376 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    strerror(n=errno())

Convert a system call error code to a descriptive string
"""
strerror(e::Integer) = unsafe_string(ccall(:strerror, Cstring, (Int32,), e))
strerror() = strerror(errno())

```
-/
def strerror (e : Int) : M World String := do
  ops.strerror (← convertTo .i32 e)

def strerrorDefault : M World String := do
  strerror ops (← errno ops).val

-- Reason: `function GetLastError end` and `function FormatMessage end` declare generic functions without methods; the Windows methods are modelled below.
-- UNTRANSLATED
-- Source: base/libc.jl:377-390 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     GetLastError()
-- 
-- Call the Win32 `GetLastError` function [only available on Windows].
-- """
-- function GetLastError end
-- 
-- """
--     FormatMessage(n=GetLastError())
-- 
-- Convert a Win32 system call error code to a descriptive string [only available on Windows].
-- """
-- function FormatMessage end
-- 
-- /Source

/--
Julia source: base/libc.jl:391-413 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
if Sys.iswindows()
    GetLastError() = ccall(:GetLastError, stdcall, UInt32, ())

    FormatMessage(e) = FormatMessage(UInt32(e))
    function FormatMessage(e::UInt32=GetLastError())
        FORMAT_MESSAGE_ALLOCATE_BUFFER = UInt32(0x100)
        FORMAT_MESSAGE_FROM_SYSTEM = UInt32(0x1000)
        FORMAT_MESSAGE_IGNORE_INSERTS = UInt32(0x200)
        FORMAT_MESSAGE_MAX_WIDTH_MASK = UInt32(0xFF)
        lpMsgBuf = Ref{Ptr{UInt16}}()
        lpMsgBuf[] = 0
        len = ccall(:FormatMessageW, stdcall, UInt32, (UInt32, Ptr{Cvoid}, UInt32, UInt32, Ptr{Ptr{UInt16}}, UInt32, Ptr{Cvoid}),
                    FORMAT_MESSAGE_ALLOCATE_BUFFER | FORMAT_MESSAGE_FROM_SYSTEM | FORMAT_MESSAGE_IGNORE_INSERTS | FORMAT_MESSAGE_MAX_WIDTH_MASK,
                    C_NULL, e, 0, lpMsgBuf, 0, C_NULL)
        p = lpMsgBuf[]
        len == 0 && return ""
        buf = Vector{UInt16}(undef, len)
        GC.@preserve buf unsafe_copyto!(pointer(buf), p, len)
        ccall(:LocalFree, stdcall, Ptr{Cvoid}, (Ptr{Cvoid},), p)
        return transcode(String, buf)
    end
end

```
-/
def getLastError : M World U32 := ops.getLastErrorCall ()

def formatMessageU32 (e : U32) : M World String := do
  let formatMessageAllocateBuffer : U32 := JInt.lit .u32 0x100
  let formatMessageFromSystem : U32 := JInt.lit .u32 0x1000
  let formatMessageIgnoreInserts : U32 := JInt.lit .u32 0x200
  let formatMessageMaxWidthMask : U32 := JInt.lit .u32 0xFF
  let flags := JuliaLean.base.int.bor (JuliaLean.base.int.bor (JuliaLean.base.int.bor
    formatMessageAllocateBuffer formatMessageFromSystem) formatMessageIgnoreInserts)
    formatMessageMaxWidthMask
  let (len, p) ← ops.formatMessageW flags e
  if len.val == 0 then return ""
  let buf ← ops.loadUInt16s p len
  let _ ← ops.localFree p
  ops.utf16String buf

def formatMessage (e : Int) : M World String := do
  formatMessageU32 ops (← convertTo .u32 e)

def formatMessageDefault : M World String := do
  formatMessageU32 ops (← getLastError ops)

/--
Julia source: base/libc.jl:414-426 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
## Memory related ##
"""
    free(addr::Ptr)

Call `free` from the C standard library. Only use this on memory obtained from [`malloc`](@ref), not
on pointers retrieved from other C libraries. [`Ptr`](@ref) objects obtained from C libraries should
be freed by the free functions defined in that library, to avoid assertion failures if
multiple `libc` libraries exist on the system.
"""
free(p::Ptr) = ccall(:free, Cvoid, (Ptr{Cvoid},), p)
free(p::Cstring) = free(convert(Ptr{UInt8}, p))
free(p::Cwstring) = free(convert(Ptr{Cwchar_t}, p))

```
-/
def freePtr (p : Ptr) : M World Unit := ops.free p

def freeCString (p : CStr) : M World Unit := freePtr ops (ops.cstringPtr p)

def freeCWString (p : WStr) : M World Unit := freePtr ops (ops.cwstringPtr p)

/--
Julia source: base/libc.jl:427-433 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    malloc(size::Integer)::Ptr{Cvoid}

Call `malloc` from the C standard library.
"""
malloc(size::Integer) = ccall(:malloc, Ptr{Cvoid}, (Csize_t,), size)

```
-/
def malloc (size : Int) : M World Ptr := do
  ops.malloc (← convertTo .u64 size)

/--
Julia source: base/libc.jl:434-443 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    realloc(addr::Ptr, size::Integer)::Ptr{Cvoid}

Call `realloc` from the C standard library.

See warning in the documentation for [`free`](@ref) regarding only using this on memory originally
obtained from [`malloc`](@ref).
"""
realloc(p::Ptr, size::Integer) = ccall(:realloc, Ptr{Cvoid}, (Ptr{Cvoid}, Csize_t), p, size)

```
-/
def realloc (p : Ptr) (size : Int) : M World Ptr := do
  ops.realloc p (← convertTo .u64 size)

/--
Julia source: base/libc.jl:444-452 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    calloc(num::Integer, size::Integer)::Ptr{Cvoid}

Call `calloc` from the C standard library.
"""
calloc(num::Integer, size::Integer) = ccall(:calloc, Ptr{Cvoid}, (Csize_t, Csize_t), num, size)



```
-/
def calloc (num size : Int) : M World Ptr := do
  let cnum ← convertTo .u64 num
  let csize ← convertTo .u64 size
  ops.calloc cnum csize

/--
Julia source: base/libc.jl:453-463 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
## Random numbers ##

# Access to very high quality (kernel) randomness
function getrandom!(A::Union{Array,Base.RefValue})
    ret = ccall(:uv_random, Cint, (Ptr{Cvoid}, Ptr{Cvoid}, Ptr{Cvoid}, Csize_t,   Cuint, Ptr{Cvoid}),
                                   C_NULL,     C_NULL,     A,          sizeof(A), 0,     C_NULL)
    Base.uv_error("getrandom", ret)
    return A
end
_make_uint64_seed() = getrandom!(Base.RefValue{UInt64}())[]

```
-/
def getrandomBang {A : Type} (a : A) : M World A := do
  let ret ← ops.uvRandom a (← ops.sizeOf a)
  ops.errors.uvError "getrandom" ret
  pure a

def makeUInt64Seed : M World U64 := do
  ops.getRefU64 (← getrandomBang ops (← ops.newRefU64 ()))

/-- `2.0^-32`. -/
def twoPowMinus32 : F64 := JuliaLean.Promotion.Fl.ofBits 0x3DF0000000000000

/--
Julia source: base/libc.jl:464-475 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# To limit dependency on rand functionality implemented in the Random module,
# Libc.rand is used in Base (it also is independent from Random.seed, so is
# only affected by `Libc.srand(seed)` calls)
"""
    rand([T::Type]=UInt32)

Generate a random number of type `T`. `T` can be `UInt32` or `Float64`.
"""
rand() = ccall(:jl_rand, UInt64, ()) % UInt32
rand(::Type{UInt32}) = rand()
rand(::Type{Float64}) = rand() * 2.0^-32

```
-/
def rand : M World U32 := do
  pure (remTo .u32 (← ops.jlRand ()).val)

def randUInt32 : M World U32 := rand ops

def randFloat64 : M World F64 := do
  pure (JuliaLean.base.float.mul_float (JuliaLean.base.float.floatOfInt .f64 (← rand ops))
    twoPowMinus32)

/--
Julia source: base/libc.jl:476-484 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    srand([seed])

Set a value for the current global `seed`.
"""
function srand(seed::Integer=_make_uint64_seed())
    ccall(:jl_srand, Cvoid, (UInt64,), seed % UInt64)
end

```
-/
def srand (seed : Int) : M World Unit :=
  ops.jlSrand (remTo .u64 seed)

def srandDefault : M World Unit := do
  srand ops (← makeUInt64Seed ops).val

/-- The default `mode` of `mkfifo`: `S_IRUSR | S_IWUSR | S_IRGRP | S_IWGRP | S_IROTH | S_IWOTH`. -/
def mkfifoDefaultMode : JuliaLean.base.filesystem.U16 :=
  JuliaLean.base.int.bor (JuliaLean.base.int.bor (JuliaLean.base.int.bor
    (JuliaLean.base.int.bor (JuliaLean.base.int.bor JuliaLean.base.filesystem.sIrusr
      JuliaLean.base.filesystem.sIwusr) JuliaLean.base.filesystem.sIrgrp)
    JuliaLean.base.filesystem.sIwgrp) JuliaLean.base.filesystem.sIroth)
    JuliaLean.base.filesystem.sIwoth

/--
Julia source: base/libc.jl:485-511 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    mkfifo(path::AbstractString, [mode::Integer]) -> path

Make a FIFO special file (a named pipe) at `path`.  Return `path` as-is on success.

`mkfifo` is supported only in Unix platforms.

!!! compat "Julia 1.11"
    `mkfifo` requires at least Julia 1.11.
"""
function mkfifo(
    path::AbstractString,
    mode::Integer = Base.S_IRUSR | Base.S_IWUSR | Base.S_IRGRP | Base.S_IWGRP |
                    Base.S_IROTH | Base.S_IWOTH,
)
    @static if Sys.isunix()
        # Default `mode` is compatible with `mkfifo` CLI in coreutils.
        ret = ccall(:mkfifo, Cint, (Cstring, Base.Cmode_t), path, mode)
        systemerror("mkfifo", ret == -1)
        return path
    else
        # Using normal `error` because `systemerror("mkfifo", ENOTSUP)` does not
        # seem to work on Windows.
        error("mkfifo: Operation not supported")
    end
end

```
-/
def mkfifo (path : String) (mode : Int) : M World String := do
  if ops.isUnix then
    let cmode ← convertTo ops.cmodeType mode
    let cpath ← ops.toCString path
    let ret ← ops.mkfifo cpath cmode.val
    ops.errors.systemError "mkfifo" (ret.val == -1)
    return path
  else
    throw (.errorException "mkfifo: Operation not supported")

def mkfifoDefault (path : String) : M World String :=
  mkfifo ops path mkfifoDefaultMode.val

/--
Julia source: base/libc.jl:512-540 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct Cpasswd
   username::Cstring
   uid::Culong
   gid::Culong
   shell::Cstring
   homedir::Cstring
   gecos::Cstring
   Cpasswd() = new(C_NULL, typemax(Culong), typemax(Culong), C_NULL, C_NULL, C_NULL)
end
mutable struct Cgroup
    groupname::Cstring # group name
    gid::Culong        # group ID
    mem::Ptr{Cstring}  # group members
    Cgroup() = new(C_NULL, typemax(Culong), C_NULL)
end
struct Passwd
    username::String
    uid::UInt
    gid::UInt
    shell::String
    homedir::String
    gecos::String
end
struct Group
    groupname::String
    gid::UInt
    mem::Vector{String}
end

```
-/
structure Cpasswd (P : Type) (culong : IntTy) where
  username : P
  uid : JInt culong
  gid : JInt culong
  shell : P
  homedir : P
  gecos : P

def Cpasswd.new : Cpasswd Ptr (culongTy ops) :=
  ⟨ops.nullPtr, JInt.typemax (culongTy ops), JInt.typemax (culongTy ops), ops.nullPtr, ops.nullPtr, ops.nullPtr⟩

structure Cgroup (P : Type) (culong : IntTy) where
  groupname : P
  gid : JInt culong
  mem : P

def Cgroup.new : Cgroup Ptr (culongTy ops) := ⟨ops.nullPtr, JInt.typemax (culongTy ops), ops.nullPtr⟩

structure Passwd where
  username : String
  uid : U64
  gid : U64
  shell : String
  homedir : String
  gecos : String

structure Group where
  groupname : String
  gid : U64
  mem : List String

/-- `p == C_NULL ? "" : unsafe_string(p)`. -/
def stringOrEmpty (p : Ptr) : M World String :=
  if ops.isNull p then pure "" else ops.unsafeString p

/-- The `Passwd` built from a filled `Cpasswd`; `pd.uid` and `pd.gid` convert from `Culong` to
`UInt`. -/
def passwdOfFields (username : Ptr) (uid gid : Int) (shell homedir gecos : Ptr) :
    M World Passwd := do
  let username ← stringOrEmpty ops username
  let uid ← convertTo .u64 (← convertTo (culongTy ops) uid).val
  let gid ← convertTo .u64 (← convertTo (culongTy ops) gid).val
  let shell ← stringOrEmpty ops shell
  let homedir ← stringOrEmpty ops homedir
  let gecos ← stringOrEmpty ops gecos
  pure ⟨username, uid, gid, shell, homedir, gecos⟩

/--
Julia source: base/libc.jl:541-560 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Gets password-file entry for default user, or a subset thereof
# (e.g., uid and guid are set to -1 on Windows)
function getpw()
    ref_pd = Ref(Cpasswd())
    ret = ccall(:uv_os_get_passwd, Cint, (Ref{Cpasswd},), ref_pd)
    Base.uv_error("getpw", ret)

    pd = ref_pd[]
    pd = Passwd(
        pd.username == C_NULL ? "" : unsafe_string(pd.username),
        pd.uid,
        pd.gid,
        pd.shell == C_NULL ? "" : unsafe_string(pd.shell),
        pd.homedir == C_NULL ? "" : unsafe_string(pd.homedir),
        pd.gecos == C_NULL ? "" : unsafe_string(pd.gecos),
    )
    ccall(:uv_os_free_passwd, Cvoid, (Ref{Cpasswd},), ref_pd)
    return pd
end

```
-/
def getpw : M World Passwd := do
  let (ret, username, uid, gid, shell, homedir, gecos) ← ops.getPasswd ()
  ops.errors.uvError "getpw" ret
  let pd ← passwdOfFields ops username uid gid shell homedir gecos
  ops.freePasswd (username, uid, gid, shell, homedir, gecos)
  pure pd

/--
Julia source: base/libc.jl:561-580 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getpwuid(uid::Unsigned, throw_error::Bool=true)
    ref_pd = Ref(Cpasswd())
    ret = ccall(:uv_os_get_passwd2, Cint, (Ref{Cpasswd}, Culong), ref_pd, uid)
    if ret != 0
        throw_error && Base.uv_error("getpwuid", ret)
        return
    end
    pd = ref_pd[]
    pd = Passwd(
        pd.username == C_NULL ? "" : unsafe_string(pd.username),
        pd.uid,
        pd.gid,
        pd.shell == C_NULL ? "" : unsafe_string(pd.shell),
        pd.homedir == C_NULL ? "" : unsafe_string(pd.homedir),
        pd.gecos == C_NULL ? "" : unsafe_string(pd.gecos),
    )
    ccall(:uv_os_free_passwd, Cvoid, (Ref{Cpasswd},), ref_pd)
    return pd
end

```
-/
def getpwuid (uid : Int) (throwErr : Bool) : M World (Option Passwd) := do
  let cuid ← convertTo (culongTy ops) uid
  let (ret, username, uid, gid, shell, homedir, gecos) ← ops.getPasswdUid cuid.val
  if ret.val != 0 then
    if throwErr then ops.errors.uvError "getpwuid" ret
    return none
  let pd ← passwdOfFields ops username uid gid shell homedir gecos
  ops.freePasswd (username, uid, gid, shell, homedir, gecos)
  pure (some pd)

def getpwuidDefault (uid : Int) : M World (Option Passwd) := getpwuid ops uid true

/--
Julia source: base/libc.jl:581-605 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getgrgid(gid::Unsigned, throw_error::Bool=true)
    ref_gp = Ref(Cgroup())
    ret = ccall(:uv_os_get_group, Cint, (Ref{Cgroup}, Culong), ref_gp, gid)
    if ret != 0
        throw_error && Base.uv_error("getgrgid", ret)
        return
    end
    gp = ref_gp[]
    members = String[]
    if gp.mem != C_NULL
        while true
            mem = unsafe_load(gp.mem, length(members) + 1)
            mem == C_NULL && break
            push!(members, unsafe_string(mem))
        end
    end
    gp = Group(
         gp.groupname == C_NULL ? "" : unsafe_string(gp.groupname),
         gp.gid,
         members,
    )
    ccall(:uv_os_free_group, Cvoid, (Ref{Cgroup},), ref_gp)
    return gp
end

```
-/
def getgrgid (gid : Int) (throwErr : Bool) : M World (Option Group) := do
  let cgid ← convertTo (culongTy ops) gid
  let (ret, groupname, gid, mem) ← ops.getGroup cgid.val
  if ret.val != 0 then
    if throwErr then ops.errors.uvError "getgrgid" ret
    return none
  let members ← if ops.isNull mem then pure [] else
    whileLoop (fun (members : List String) => do
      let p ← ops.loadPtr mem (members.length + 1)
      if ops.isNull p then return Sum.inl members
      return Sum.inr (members ++ [← ops.unsafeString p])) []
  let name ← stringOrEmpty ops groupname
  let gidU ← convertTo .u64 (← convertTo (culongTy ops) gid).val
  ops.freeGroup (groupname, gid, mem)
  pure (some ⟨name, gidU, members⟩)

def getgrgidDefault (gid : Int) : M World (Option Group) := getgrgid ops gid true

/--
Julia source: base/libc.jl:606-609 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getuid() = ccall(:jl_getuid, Culong, ())
geteuid() = ccall(:jl_geteuid, Culong, ())
getegid() = Sys.iswindows() ? Culong(-1) : ccall(:getegid, Culong, ())

```
-/
def getuid : M World Int := do
  pure (← convertTo (culongTy ops) (← ops.getuid ())).val

def geteuid : M World Int := do
  pure (← convertTo (culongTy ops) (← ops.geteuid ())).val

def getegid : M World Int := do
  if ops.isWindows then pure (← convertTo (culongTy ops) (-1)).val
  else pure (← convertTo (culongTy ops) (← ops.getegid ())).val

-- Reason: The `libdl.jl` include and the module end are load-time structure; `libdl.jl` has its own model.
-- UNTRANSLATED
-- Source: base/libc.jl:610-613 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # Include dlopen()/dlpath() code
-- include("libdl.jl")
-- 
-- end # module
-- /Source

end

end JuliaLean.base.libc


section

set_option linter.unusedSimpArgs false
namespace JuliaLean.IOCov.Libc

open JuliaLean JuliaLean.IOCov

/-! ## `RawFD`, `dup`, `show`, lines 35-51 -/

/-- `RawFD(fd::Integer) = bitcast(RawFD, Cint(fd))`, `base/libc.jl:35`. -/
def rawFD (fd : Int) : R Int := toInt .i32 fd
/-- `RawFD(fd::RawFD) = fd`, `base/libc.jl:36`. -/
def rawFDId (fd : Int) : Int := fd
/-- `cconvert(::Type{Cint}, fd::RawFD) = bitcast(Cint, fd)`, `base/libc.jl:37`. -/
def cconvertCint (fd : Int) : Int := fd

/-- `dup(x::RawFD)`, `base/libc.jl:46`: the result of C `dup` is returned unchecked. -/
def dup1 (cdup : Int → Int) (x : Int) : R Int := .ok (cdup x)
/-- `dup(src, target)`, `base/libc.jl:47-49`: `systemerror("dup", -1 == dup2(...))`. -/
def dup2 (cdup2 : Int → Int → Int) (src target : Int) : R Unit :=
  systemerror "dup" (-1 == cdup2 src target)

/-- `show(io, fd::RawFD) = print(io, "RawFD(", bitcast(Int32, fd), ')')`, `base/libc.jl:51`. -/
def showRawFD (fd : Int) : String := "RawFD(" ++ toString fd ++ ")"

/-! ## `FILE`, lines 123-147 -/

/-- `modestr(r::Bool, w::Bool)`, `base/libc.jl:124`. -/
def modestr (r w : Bool) : R String :=
  if r then (if w then .ok "r+" else .ok "r")
  else if w then .ok "w" else argErr "neither readable nor writable"

/-- `modestr(s::IO) = modestr(isreadable(s), iswritable(s))`, `base/libc.jl:123`. -/
def modestrIO (isreadable iswritable : Bool) : R String := modestr isreadable iswritable

/-- `FILE(fd::RawFD, mode)`, `base/libc.jl:126-130`; `fdopen` returns a pointer (0 = NULL). -/
def fileOfFd (fdopen : Int → String → Nat) (fd : Int) (mode : String) : R Nat := do
  let p := fdopen fd mode
  systemerror "fdopen" (p == 0)
  pure p

/-- `seek(h::FILE, offset)`, `base/libc.jl:141-145`: `offset` is converted to `Clong`. -/
def seekFILE (fseek : Nat → Int → Int) (h : Nat) (offset : Int) : R Nat := do
  let off ← toInt .i64 offset
  systemerror "fseek" (fseek h off != 0)
  pure h

/-- `FILE(s::IO)`, `base/libc.jl:132-136`: `dup` is unchecked, then `fdopen` and `seek`. -/
def fileOfIO (cdup : Int → Int) (fdopen : Int → String → Nat) (fseek : Nat → Int → Int)
    (fd : Int) (r w : Bool) (pos : Int) : R Nat := do
  let d ← rawFD fd
  let d' ← dup1 cdup d
  let m ← modestrIO r w
  let f ← fileOfFd fdopen d' m
  seekFILE fseek f pos

/-- `unsafe_convert(Ptr, f::FILE) = convert(T, f.ptr)`, `base/libc.jl:138`. -/
def unsafeConvertFILE (ptr : Nat) : Nat := ptr
/-- `close(f::FILE)`, `base/libc.jl:139`. -/
def closeFILE (fclose : Nat → Int) (f : Nat) : R Unit := systemerror "fclose" (fclose f != 0)
/-- `position(h::FILE)`, `base/libc.jl:147`: `ftell`'s result, unchecked. -/
def positionFILE (ftell : Nat → Int) (h : Nat) : Int := ftell h
/-- `flush_cstdio()`, `base/libc.jl:156`: one call to `jl_flush_cstdio`. -/
def flushCstdio (flush : Unit → Unit) : Unit := flush ()

/-! ## `systemsleep`, `TimeVal`, `TmStruct`, lines 162-226 -/

/-- `round(UInt32, x)` of a real `x` given as the exact rational `x`: `InexactError`
outside `0:typemax(UInt32)` (rounding to nearest, ties to even). -/
def roundUInt32 (x : Int) : R Int := toInt .u32 x

/-- `systemsleep(s::Real)` on Unix, `base/libc.jl:162`: `usleep(round(UInt32, s*1e6))`,
with `us = s*1e6` already rounded to an integer. -/
def systemsleep (usleep : Int → Int) (us : Int) : R Int := do
  let n ← roundUInt32 us
  pure (usleep n)

/-- `TimeVal()`, `base/libc.jl:187-192`: `error` when `jl_gettimeofday` fails. -/
def timeVal (gettimeofday : Unit → Int × (Int × Int)) : R (Int × Int) :=
  let (status, tv) := gettimeofday ()
  if status != 0 then .error (.errorException "unable to determine current time: ")
  else .ok tv

/-- The 14 `Int32` fields of `TmStruct`. -/
abbrev Tm := List Int

/-- `TmStruct(sec, ..., isdst)`, `base/libc.jl:217-218`: fields converted to `Int32`,
the 5 padding fields zero. -/
def tmStruct9 (fs : List Int) : R Tm := do
  let cs ← fs.mapM (toInt .i32)
  pure (cs ++ [0, 0, 0, 0, 0])
/-- `TmStruct()`, `base/libc.jl:219`. -/
def tmStruct0 : Tm := List.replicate 14 0
/-- `TmStruct(t::Real)`, `base/libc.jl:220-226`: `floor(t)` converted to `Int` for
`localtime_r`, which fills the struct. `t` is given as `floor(t)` (`none` for
NaN/Inf). -/
def tmStructOfTime (localtime : Int → Tm) (floort : Option Int) : R Tm :=
  match floort with
  | none => .error (.jl (.inexactError "Int64"))
  | some t => do let n ← toInt .i64 t; pure (localtime n)

/-! ## `strftime`, `strptime`, `time`, lines 236-325 -/

/-- `strftime(fmt, tm::TmStruct)`, `base/libc.jl:239-245`: `wcsftime` writes into a
buffer of 128 wide characters and returns 0 when the result (with its NUL) does not
fit, in which case `""` is returned. `wcsftime` is given by the full formatted text. -/
def strftimeTm (format : List Char) : List Char :=
  let n := if format.length + 1 ≤ 128 then format.length else 0
  if n == 0 then [] else format.take n

/-- `strftime(fmt, t::Real) = strftime(fmt, TmStruct(t))`, `base/libc.jl:237`. -/
def strftimeReal (localtime : Int → Tm) (fmtText : Tm → List Char) (t : Int) : R (List Char) := do
  let tm ← tmStructOfTime localtime (some t)
  pure (strftimeTm (fmtText tm))

/-- `strftime(t) = strftime("%c", t)`, `base/libc.jl:236`. -/
def strftime1 (localtime : Int → Tm) (cText : Tm → List Char) (t : Int) : R (List Char) :=
  strftimeReal localtime cText t

/-- `strptime(fmt, timestr)`, `base/libc.jl:258-307` (non-Apple): `strptime` fills a
zeroed `TmStruct`; a NULL return throws. The C call is `cstrptime tm0 = (ok, tm)`. -/
def strptime (cstrptime : Tm → Bool × Tm) : R Tm :=
  let (ok, tm) := cstrptime tmStruct0
  if !ok then argErr "invalid arguments" else .ok tm

/-- `strptime(timestr) = strptime("%c", timestr)`, `base/libc.jl:257`. -/
def strptime1 (cstrptimeC : Tm → Bool × Tm) : R Tm := strptime cstrptimeC

/-- `time(tm::TmStruct) = Float64(mktime(tm))`, `base/libc.jl:316`. -/
def timeTm (mktime : Tm → Int) (tm : Tm) : Int := mktime tm
/-- `time() = jl_clock_now()`, `base/libc.jl:325`. -/
def timeNow (clock : Unit → Float) : Float := clock ()

/-! ## Process and host queries, errno, lines 334-375 -/

/-- `getpid() = uv_os_getpid()`, `base/libc.jl:334`. -/
def getpid (c : Unit → Int) : Int := c ()

/-- `gethostname()`, `base/libc.jl:343-352`: a 256-byte buffer, `systemerror` on a
nonzero return, then the bytes up to the first NUL. -/
def gethostname (c : Nat → Int × List UInt8) : R (List UInt8) := do
  let (err, hn) := c 256
  systemerror "gethostname" (err != 0)
  pure (hn.takeWhile (· != 0))

/-- `errno() = jl_errno()` and `errno(e) = jl_set_errno(Cint(e))`, `base/libc.jl:366-367`. -/
def errnoGet (state : Int) : Int := state
def errnoSet (e : Int) : R Int := toInt .i32 e

/-- `strerror(e::Integer) = unsafe_string(strerror(Int32(e)))`, `base/libc.jl:374`. -/
def strerror (c : Int → List UInt8) (e : Int) : R (List UInt8) := do
  let x ← toInt .i32 e
  pure (c x)
/-- `strerror() = strerror(errno())`, `base/libc.jl:375`. -/
def strerror0 (c : Int → List UInt8) (errno : Int) : R (List UInt8) := strerror c (errnoGet errno)

/-! ## Memory, lines 423-449 -/

/-- `free(p::Ptr)`, `free(p::Cstring)`, `free(p::Cwstring)`, `base/libc.jl:423-425`:
each converts to `Ptr{Cvoid}` and calls C `free` on the same address. -/
def free (cfree : Nat → Unit) (p : Nat) : Unit := cfree p
def freeCstring (cfree : Nat → Unit) (p : Nat) : Unit := free cfree p
def freeCwstring (cfree : Nat → Unit) (p : Nat) : Unit := free cfree p

/-- `malloc(size::Integer)`, `base/libc.jl:432`: `size` converted to `Csize_t`. -/
def malloc (cmalloc : Int → Nat) (size : Int) : R Nat := do
  let n ← toInt .u64 size
  pure (cmalloc n)
/-- `realloc(p, size)`, `base/libc.jl:442`. -/
def realloc (crealloc : Nat → Int → Nat) (p : Nat) (size : Int) : R Nat := do
  let n ← toInt .u64 size
  pure (crealloc p n)
/-- `calloc(num, size)`, `base/libc.jl:449`. -/
def calloc (ccalloc : Int → Int → Nat) (num size : Int) : R Nat := do
  let a ← toInt .u64 num
  let b ← toInt .u64 size
  pure (ccalloc a b)

/-! ## Randomness, lines 456-483 -/

/-- `getrandom!(A)`, `base/libc.jl:456-461`: `uv_random` fills `A`; a negative return
throws, otherwise `A` (filled) is returned. -/
def getrandom (uvRandom : Nat → Int × List UInt8) (len : Nat) : R (List UInt8) := do
  let (ret, bytes) := uvRandom len
  uvError "getrandom" ret
  pure bytes

/-- `_make_uint64_seed()`, `base/libc.jl:462`: eight random bytes read as a `UInt64`
(little-endian). -/
def makeSeed (uvRandom : Nat → Int × List UInt8) : R Nat := do
  let b ← getrandom uvRandom 8
  pure (b.foldr (fun x acc => x.toNat + 256 * acc) 0)

/-- `rand() = jl_rand() % UInt32`, `base/libc.jl:472`. -/
def rand (jlRand : Nat) : Nat := jlRand % 2 ^ 32
/-- `rand(::Type{UInt32}) = rand()`, `base/libc.jl:473`. -/
def randU32 (jlRand : Nat) : Nat := rand jlRand
/-- `rand(::Type{Float64}) = rand() * 2.0^-32`, `base/libc.jl:474`: the product is exact,
so the value is the rational `rand() / 2^32`, given here as numerator and denominator. -/
def randF64 (jlRand : Nat) : Nat × Nat := (rand jlRand, 2 ^ 32)

/-- `srand(seed)`, `base/libc.jl:481-483`: `jl_srand(seed % UInt64)`. -/
def srand (seed : Int) : Int := wrapTo .u64 seed

/-! ## `mkfifo`, passwd and group records, lines 495-608 -/

/-- `mkfifo(path, mode)`, `base/libc.jl:495-510` (Unix): `systemerror` when `mkfifo`
returns -1, else `path`. `mode` is converted to `Cmode_t` (`UInt32`). -/
def mkfifo (cmkfifo : List UInt8 → Int → Int) (path : List UInt8) (mode : Int) : R (List UInt8) := do
  let m ← toInt .u32 mode
  systemerror "mkfifo" (cmkfifo path m == -1)
  pure path

/-- C `passwd` record as read back from libuv. -/
structure Cpasswd where
  username : CStr
  uid : Nat
  gid : Nat
  shell : CStr
  homedir : CStr
  gecos : CStr
  deriving DecidableEq, Repr

/-- `Cpasswd()`, `base/libc.jl:519`. -/
def cpasswd0 : Cpasswd := ⟨none, 2 ^ 64 - 1, 2 ^ 64 - 1, none, none, none⟩

structure Cgroup where
  groupname : CStr
  gid : Nat
  mem : Option (List (List UInt8))
  deriving DecidableEq, Repr

/-- `Cgroup()`, `base/libc.jl:525`. -/
def cgroup0 : Cgroup := ⟨none, 2 ^ 64 - 1, none⟩

structure Passwd where
  username : List UInt8
  uid : Nat
  gid : Nat
  shell : List UInt8
  homedir : List UInt8
  gecos : List UInt8
  deriving DecidableEq, Repr

/-- The `Passwd(...)` conversion shared by `getpw` and `getpwuid`. -/
def passwdOf (pd : Cpasswd) : Passwd :=
  ⟨cstrOrEmpty pd.username, pd.uid, pd.gid, cstrOrEmpty pd.shell, cstrOrEmpty pd.homedir,
    cstrOrEmpty pd.gecos⟩

/-- `getpw()`, `base/libc.jl:543-559`. -/
def getpw (c : Cpasswd → Int × Cpasswd) : R Passwd := do
  let (ret, pd) := c cpasswd0
  uvError "getpw" ret
  pure (passwdOf pd)

/-- `getpwuid(uid, throw_error)`, `base/libc.jl:561-579`; `nothing` is `none`. -/
def getpwuid (c : Cpasswd → Nat → Int × Cpasswd) (uid : Nat) («throwError» : Bool) :
    R (Option Passwd) := do
  let (ret, pd) := c cpasswd0 uid
  if ret != 0 then
    if «throwError» then uvError "getpwuid" ret
    pure none
  else pure (some (passwdOf pd))

structure Group where
  groupname : List UInt8
  gid : Nat
  mem : List (List UInt8)
  deriving DecidableEq, Repr

/-- `getgrgid(gid, throw_error)`, `base/libc.jl:581-604`: members are read until the
NULL entry (`mem` lists them; `none` is a NULL `mem` array). -/
def getgrgid (c : Cgroup → Nat → Int × Cgroup) (gid : Nat) («throwError» : Bool) :
    R (Option Group) := do
  let (ret, gp) := c cgroup0 gid
  if ret != 0 then
    if «throwError» then uvError "getgrgid" ret
    pure none
  else
    let members := match gp.mem with | none => [] | some ms => ms
    pure (some ⟨cstrOrEmpty gp.groupname, gp.gid, members⟩)

/-- `getuid`, `geteuid`, `getegid`, `base/libc.jl:606-608` (Unix): one C call each. -/
def getuid (c : Unit → Nat) : Nat := c ()
def geteuid (c : Unit → Nat) : Nat := c ()
def getegid (c : Unit → Nat) : Nat := c ()
end JuliaLean.IOCov.Libc
end

section
namespace JuliaLean.IOCov.LibcRemaining

open JuliaLean.Registry

/-- Unix `_get_osfhandle(fd::RawFD)`, `base/libc.jl:86`. -/
def getOsfhandle (fd : Int) : Int := fd

/-- `_make_uint64_seed()`, `base/libc.jl:462`.  `getrandom` models filling the
fresh `RefValue{UInt64}` before it is indexed. -/
def makeUint64Seed (getrandom : UInt64 -> UInt64) : UInt64 := getrandom 0
end JuliaLean.IOCov.LibcRemaining
end
