import JuliaLean.base.lock
import JuliaLean.base.gcutils
import JuliaLean.base.error
import JuliaLean.base.libc
import JuliaLean.base.stat
import JuliaLean.base.reduce
import JuliaLean.base.genericmemory
import JuliaLean.base.checked
import JuliaLean.base.range
import JuliaLean.base.libuv
import JuliaLean.base.strings.cstring
import JuliaLean.base.io
import JuliaLean.base.pointer
import JuliaLean.base.int
import JuliaLean.base.float
import JuliaLean.base.iobuffer
import JuliaLean.base.cancellation

/-!
# Model of `base/iostream.jl`

Source-mirrored IOStream methods at Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`
on a 64-bit little-endian POSIX build.
The generic IO world's state preserves file, buffer, lock and errno changes on errors.
Foreign calls are typed runtime parameters, with their observed C return conventions
recorded below. They carry no assumed equations. Strings retain arbitrary bytes.
-/

namespace JuliaLean.base.iostream

open JuliaLean
open JuliaLean.base.io (I U Byte M Error CancelArg Cancellation)

abbrev CInt := JInt .i32
abbrev Handle := JuliaLean.base.pointer.Ptr Unit
abbrev BytePointer := JuliaLean.base.pointer.Ptr Byte
abbrev Text := List UInt8

def i := JuliaLean.base.io.i
def u := JuliaLean.base.io.u
def cint (value : Int) : CInt := JInt.wrap .i32 value
def text (value : String) : Text := value.toUTF8.toList

/-- Runtime-value specialization retaining the expected String type and actual
conversion result in the complete TypeError value. The assertion uses the
installed Core primitive; convert and open remain selected effectful calls.
Julia source: base/iostream.jl:346. -/
-- Source: base/iostream.jl:346-346 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- open(fname::AbstractString; kwargs...) = open(convert(String, fname)::String; kwargs...)
-- /Source
def openAbstractStringRuntime {W L Name Kw Result : Type}
    (ops : JuliaLean.base.boot.CoreOps W L)
    (convert : Name → JuliaLean.base.boot.CoreM W L (JuliaLean.base.expr.Value L))
    (openFile : JuliaLean.base.expr.Value L → Kw → JuliaLean.base.boot.CoreM W L Result)
    (name : Name) (keywords : Kw) : JuliaLean.base.boot.CoreM W L Result := do
  let filename ← JuliaLean.base.boot.typeassert ops (← convert name)
    (JuliaLean.base.boot.coreV ops "String")
  openFile filename keywords

structure Fields (Vector Lock : Type) where
  handle : Handle
  ios : Vector
  name : Text
  mark : I
  mutex : Lock
  dolock : Bool

structure Access (World Stream Vector Lock : Type) where
  get : Stream → M World (Fields Vector Lock)
  set : Stream → Fields Vector Lock → M World Unit
  new : Fields Vector Lock → M World Stream

structure Locks (World Lock : Type) where
  lock : Lock → M World Unit
  unlock : Lock → M World Unit

/-- Typed foreign-call boundary. `ios_*` mutate the pointed-to ios_t in the world.

At the pinned revision, `src/support/ios.c:475-552` defines seek/skip status as
0 on success, -1 with errno, or -2 without errno. `ios_pos` and `ios_filesize`
return signed 64-bit offsets or -1 (`555-586`). Close always invalidates the fd
and frees the buffer, even when returning a flush/close error (`706-720`).
`ios_isopen` tests fd != -1, not EOF (`723-725`). Getc/peekc return -1 at EOF;
getc consumes a byte and updates line count, while peekc does not consume it
(`1119-1141`). Putc returns the accepted byte count, not the byte (`1105-1116`).
`ios_read` performs at most one underlying read, `ios_readall` keeps reading
(`284-361`); both return the actual copied byte count. `ios_write` returns an
accepted byte count, possibly short (`424-472`). Fillbuf returns available
bytes only when it reached the end, otherwise -1 (`396-404`).

`src/sys.c:95-101` gives the ios_t byte size, fd, and signed Int32 narrowing
of size-bpos. Buffer-n returns 1 when refilling cannot reach n, else 0
(`425-434`). Get-nbyte-int consumes n <= 8 bytes in little-endian order
(`437-463`). Readuntil includes the consumed delimiter and uses chomp 0 to
retain it, 1 to remove one delimiter, or 2 to strip LF/CRLF; str selects
vector versus string storage (`324-379`). Take-buffer transfers/copies the
whole buffer and empties it (`307-320`). These are descriptions, not axioms.
-/
structure Runtime (World Vector : Type) where
  sizeofIos : M World CInt
  pointer : Vector → M World Handle
  bytePointer : Vector → M World BytePointer
  cString : Text → M World BytePointer
  fd : Handle → M World I
  isopen : Handle → M World CInt
  close : Handle → M World CInt
  flush : Handle → M World CInt
  writable : Handle → M World CInt
  readable : Handle → M World CInt
  trunc : Handle → U → M World CInt
  seek : Handle → I → M World I
  seekend : Handle → M World I
  skip : Handle → I → M World I
  position : Handle → M World I
  filesize : Handle → M World I
  eof : Handle → M World CInt
  fdio : Handle → I → CInt → CInt → M World Handle
  file : Handle → BytePointer → CInt → CInt → CInt → CInt → M World Handle
  putc : CInt → Handle → M World CInt
  write : Handle → BytePointer → U → M World U
  available : Handle → M World CInt
  fillbuf : Handle → M World I
  readall : Handle → BytePointer → U → M World U
  read : Handle → BytePointer → U → M World U
  getc : Handle → M World CInt
  peekc : Handle → M World CInt
  bufferN : Handle → U → M World CInt
  getNbyteInt : Handle → U → M World U
  takeBuffer : Handle → M World Vector
  readuntilBytes : Handle → Byte → Byte → Byte → M World Vector
  readuntilString : Handle → Byte → Byte → Byte → M World Text
  /-- `src/sys.c:381-424`: consume at most the destination capacity, including a found delimiter. -/
  readuntilBuffer : Handle → Byte → BytePointer → U → M World U
  copyuntil : Handle → Handle → Byte → CInt → M World U

structure OpenKeywords where
  read : Option Bool := none
  write : Option Bool := none
  create : Option Bool := none
  truncate : Option Bool := none
  append : Option Bool := none

def iosPointer {World Stream Vector Lock : Type}
    (access : Access World Stream Vector Lock) (runtime : Runtime World Vector)
    (stream : Stream) : M World Handle := do
  runtime.pointer (← access.get stream).ios

def toInt {World : Type} {t : IntTy} (value : JInt t) : M World I :=
  JuliaLean.base.io.liftJl (JInt.convert (IntTy.i64.name) .i64 value.val)

-- UNTRANSLATED
-- Source: base/iostream.jl:1-4 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- ## IOStream
-- 
-- /Source
-- Reason: Documentation, type declarations, or dispatch metadata; no method body.

/--
Julia source: base/iostream.jl:5-5 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const sizeof_ios_t = Int(ccall(:jl_sizeof_ios_t, Cint, ()))
```
-/
def sizeofIos {World Vector : Type} (runtime : Runtime World Vector) : M World I := do
  toInt (← runtime.sizeofIos)

-- UNTRANSLATED
-- Source: base/iostream.jl:6-20 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     IOStream
-- 
-- A buffered IO stream wrapping an OS file descriptor.
-- Mostly used to represent files returned by [`open`](@ref).
-- """
-- mutable struct IOStream <: IO
--     handle::Ptr{Cvoid}
--     ios::Vector{UInt8}
--     name::String
--     mark::Int64
--     lock::ReentrantLock
--     _dolock::Bool
-- 
-- /Source
-- Reason: Documentation, type declarations, or dispatch metadata; no method body.

/--
Julia source: base/iostream.jl:21-21 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    IOStream(name::AbstractString, buf::Vector{UInt8}) = new(pointer(buf), buf, name, -1, ReentrantLock(), true)
```
-/
def newWithBuffer {World Stream Vector Lock Name : Type}
    (access : Access World Stream Vector Lock) (runtime : Runtime World Vector)
    (convertName : Name → M World Text) (newLock : M World Lock)
    (name : Name) (buffer : Vector) : M World Stream := do
  let pointer ← runtime.pointer buffer
  let name ← convertName name
  let mutex ← newLock
  access.new ⟨pointer, buffer, name, i (-1), mutex, true⟩

-- UNTRANSLATED
-- Source: base/iostream.jl:22-23 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- end
-- 
-- /Source
-- Reason: Documentation, type declarations, or dispatch metadata; no method body.

/--
Julia source: base/iostream.jl:24-31 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function IOStream(name::AbstractString, finalize::Bool)
    buf = zeros(UInt8,sizeof_ios_t)
    x = IOStream(name, buf)
    if finalize
        finalizer(close, x)
    end
    return x
end
```
-/
def newStreamFinalized {World Stream Vector Name : Type}
    (size : I) (zeros : I → M World Vector) (construct : Name → Vector → M World Stream)
    (finalizer : Stream → M World Unit) (name : Name) (finalize : Bool) : M World Stream := do
  let buffer ← zeros size
  let stream ← construct name buffer
  if finalize then finalizer stream
  pure stream

/--
Julia source: base/iostream.jl:32-32 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IOStream(name::AbstractString) = IOStream(name, true)
```
-/
def newStream {World Stream Name : Type}
    (construct : Name → Bool → M World Stream) (name : Name) : M World Stream :=
  construct name true

-- UNTRANSLATED
-- Source: base/iostream.jl:33-33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, type declarations, or dispatch metadata; no method body.

/--
Julia source: base/iostream.jl:34-34 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_convert(T::Type{Ptr{Cvoid}}, s::IOStream) = convert(T, pointer(s.ios))
```
-/
def unsafeConvert {World Stream Vector Lock : Type}
    (access : Access World Stream Vector Lock) (runtime : Runtime World Vector)
    (convert : Handle → M World Handle) (stream : Stream) : M World Handle := do
  convert (← runtime.pointer (← access.get stream).ios)

/--
Julia source: base/iostream.jl:35-35 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, s::IOStream) = print(io, "IOStream(", s.name, ")")
```
-/
def showStream {World Stream Vector Lock Out : Type}
    (access : Access World Stream Vector Lock) (print : Out → List Text → M World Unit)
    (out : Out) (stream : Stream) : M World Unit := do
  print out [text "IOStream(", (← access.get stream).name, text ")"]

-- UNTRANSLATED
-- Source: base/iostream.jl:36-36 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, type declarations, or dispatch metadata; no method body.

/--
Julia source: base/iostream.jl:37-48 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro _lock_ios(s, expr)
    s = esc(s)
    quote
        l = ($s)._dolock
        temp = ($s).lock
        l && lock(temp)
        val = $(esc(expr))
        l && unlock(temp)
        val
    end
end

```
-/
def lockIos {World Stream Vector Lock A : Type}
    (access : Access World Stream Vector Lock) (locks : Locks World Lock)
    (stream : Stream) (expression : M World A) : M World A := do
  let fields ← access.get stream
  let enabled := fields.dolock
  let mutex := fields.mutex
  if enabled then locks.lock mutex
  let value ← expression
  if enabled then locks.unlock mutex
  pure value

-- UNTRANSLATED
-- Source: base/iostream.jl:49-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     fd(x)::RawFD
-- 
-- Return the file descriptor backing the stream, file, or socket.
-- 
-- `RawFD` objects can be passed directly to other languages via the `ccall` interface.
-- 
-- !!! compat "Julia 1.12"
--     Prior to 1.12, this function returned an `Int` instead of a `RawFD`. You may use
--     `RawFD(fd(x))` to produce a `RawFD` in all Julia versions.
-- 
-- !!! compat "Julia 1.12"
--     Getting the file descriptor of sockets are supported as of Julia 1.12.
-- 
-- !!! warning
--     Duplicate the returned file descriptor with [`Libc.dup()`](@ref) before
--     passing it to another system that will take ownership of it (e.g. a C
--     library). Otherwise both the Julia object `x` and the other system may try
--     to close the file descriptor, which will cause errors.
-- 
-- !!! warning
--     The file descriptors for sockets are asynchronous (i.e. `O_NONBLOCK` on
--     POSIX and `OVERLAPPED` on Windows), they may behave differently than regular
--     file descriptors.
-- """
-- /Source
-- Reason: Documentation, type declarations, or dispatch metadata; no method body.

/--
Julia source: base/iostream.jl:74-74 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fd(s::IOStream) = RawFD(ccall(:jl_ios_fd, Clong, (Ptr{Cvoid},), s.ios))
```
-/
def fd {World Stream Vector Lock FD : Type}
    (access : Access World Stream Vector Lock) (runtime : Runtime World Vector)
    (rawFD : I → M World FD) (stream : Stream) : M World FD := do
  rawFD (← runtime.fd (← iosPointer access runtime stream))

-- UNTRANSLATED
-- Source: base/iostream.jl:75-75 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, type declarations, or dispatch metadata; no method body.

/--
Julia source: base/iostream.jl:76-76 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
stat(s::IOStream) = stat(fd(s))
```
-/
def stat {World Stream FD Stat : Type} (fd : Stream → M World FD)
    (stat : FD → M World Stat) (stream : Stream) : M World Stat := do
  stat (← fd stream)

-- UNTRANSLATED
-- Source: base/iostream.jl:77-87 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     isopen(s::IOStream)
-- 
-- Check if the stream is not yet closed.
-- 
-- A closed `IOStream` may still have data to read in its buffer,
-- use [`eof`](@ref) to check for the ability to read data.
-- 
-- Use the `FileWatching` package to be notified when a file might be writable or readable.
-- """
-- /Source
-- Reason: Documentation, type declarations, or dispatch metadata; no method body.

/--
Julia source: base/iostream.jl:88-88 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isopen(s::IOStream) = ccall(:ios_isopen, Cint, (Ptr{Cvoid},), s.ios) != 0
```
-/
def isopen {World Stream Vector Lock : Type}
    (access : Access World Stream Vector Lock) (runtime : Runtime World Vector)
    (stream : Stream) : M World Bool := do
  pure ((← runtime.isopen (← iosPointer access runtime stream)).val != 0)

-- UNTRANSLATED
-- Source: base/iostream.jl:89-89 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, type declarations, or dispatch metadata; no method body.

/--
Julia source: base/iostream.jl:90-93 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function close(s::IOStream)
    bad = @_lock_ios s ccall(:ios_close, Cint, (Ptr{Cvoid},), s.ios) != 0
    systemerror("close", bad)
end
```
-/
def close {World Stream Vector Lock : Type}
    (access : Access World Stream Vector Lock) (locks : Locks World Lock)
    (runtime : Runtime World Vector) (systemerror : String → Bool → M World Unit)
    (stream : Stream) : M World Unit := do
  let status ← lockIos access locks stream (do runtime.close (← iosPointer access runtime stream))
  systemerror "close" (status.val != 0)

-- UNTRANSLATED
-- Source: base/iostream.jl:94-94 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, type declarations, or dispatch metadata; no method body.

/--
Julia source: base/iostream.jl:95-95 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
closewrite(s::IOStream) = nothing
```
-/
def closewrite {World Stream : Type} (_stream : Stream) : M World Unit := pure ()

-- UNTRANSLATED
-- Source: base/iostream.jl:96-96 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, type declarations, or dispatch metadata; no method body.

/--
Julia source: base/iostream.jl:97-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function flush(s::IOStream)
    sigatomic_begin()
    bad = @_lock_ios s ccall(:ios_flush, Cint, (Ptr{Cvoid},), s.ios) != 0
    sigatomic_end()
    systemerror("flush", bad)
end
```
-/
def flush {World Stream Vector Lock : Type}
    (access : Access World Stream Vector Lock) (locks : Locks World Lock)
    (runtime : Runtime World Vector) (beginAtomic endAtomic : M World Unit)
    (systemerror : String → Bool → M World Unit) (stream : Stream) : M World Unit := do
  beginAtomic
  let status ← lockIos access locks stream (do runtime.flush (← iosPointer access runtime stream))
  endAtomic
  systemerror "flush" (status.val != 0)

-- UNTRANSLATED
-- Source: base/iostream.jl:103-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, type declarations, or dispatch metadata; no method body.

/--
Julia source: base/iostream.jl:104-104 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iswritable(s::IOStream) = isopen(s) && ccall(:ios_get_writable, Cint, (Ptr{Cvoid},), s.ios)!=0
```
-/
def iswritable {World Stream Vector Lock : Type}
    (access : Access World Stream Vector Lock) (runtime : Runtime World Vector)
    (stream : Stream) : M World Bool := do
  if ← isopen access runtime stream then
    pure ((← runtime.writable (← iosPointer access runtime stream)).val != 0)
  else pure false

-- UNTRANSLATED
-- Source: base/iostream.jl:105-105 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, type declarations, or dispatch metadata; no method body.

/--
Julia source: base/iostream.jl:106-106 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isreadable(s::IOStream) = isopen(s) && ccall(:ios_get_readable, Cint, (Ptr{Cvoid},), s.ios)!=0
```
-/
def isreadable {World Stream Vector Lock : Type}
    (access : Access World Stream Vector Lock) (runtime : Runtime World Vector)
    (stream : Stream) : M World Bool := do
  if ← isopen access runtime stream then
    pure ((← runtime.readable (← iosPointer access runtime stream)).val != 0)
  else pure false

-- UNTRANSLATED
-- Source: base/iostream.jl:107-136 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     truncate(file, n)
-- 
-- Resize the file or buffer given by the first argument to exactly `n` bytes, filling
-- previously unallocated space with '\\0' if the file or buffer is grown.
-- 
-- # Examples
-- ```jldoctest
-- julia> io = IOBuffer();
-- 
-- julia> write(io, "JuliaLang is a GitHub organization.")
-- 35
-- 
-- julia> truncate(io, 15)
-- IOBuffer(data=UInt8[...], readable=true, writable=true, seekable=true, append=false, size=15, maxsize=Inf, ptr=16, mark=-1)
-- 
-- julia> takestring!(io)
-- "JuliaLang is a "
-- 
-- julia> io = IOBuffer();
-- 
-- julia> write(io, "JuliaLang is a GitHub organization.");
-- 
-- julia> truncate(io, 40);
-- 
-- julia> takestring!(io)
-- "JuliaLang is a GitHub organization.\\0\\0\\0\\0\\0"
-- ```
-- """
-- /Source
-- Reason: Documentation, type declarations, or dispatch metadata; no method body.

/--
Julia source: base/iostream.jl:137-141 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function truncate(s::IOStream, n::Integer)
    err = @_lock_ios s ccall(:ios_trunc, Cint, (Ptr{Cvoid}, Csize_t), s.ios, n) != 0
    systemerror("truncate", err)
    return s
end
```
-/
def truncate {World Stream Vector Lock N : Type}
    (access : Access World Stream Vector Lock) (locks : Locks World Lock)
    (runtime : Runtime World Vector) (toSize : N → M World U)
    (systemerror : String → Bool → M World Unit) (stream : Stream) (size : N) : M World Stream := do
  let status ← lockIos access locks stream (do
    let pointer ← iosPointer access runtime stream
    runtime.trunc pointer (← toSize size))
  systemerror "truncate" (status.val != 0)
  pure stream

-- UNTRANSLATED
-- Source: base/iostream.jl:142-157 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     seek(s, pos)
-- 
-- Seek a stream to the given position.
-- 
-- # Examples
-- ```jldoctest
-- julia> io = IOBuffer("JuliaLang is a GitHub organization.");
-- 
-- julia> seek(io, 5);
-- 
-- julia> read(io, Char)
-- 'L': ASCII/Unicode U+004C (category Lu: Letter, uppercase)
-- ```
-- """
-- /Source
-- Reason: Documentation, type declarations, or dispatch metadata; no method body.

/--
Julia source: base/iostream.jl:158-163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function seek(s::IOStream, n::Integer)
    ret = @_lock_ios s ccall(:ios_seek, Int64, (Ptr{Cvoid}, Int64), s.ios, n)
    systemerror("seek", ret == -1)
    ret < -1 && error("seek failed")
    return s
end
```
-/
def seek {World Stream Vector Lock N : Type}
    (access : Access World Stream Vector Lock) (locks : Locks World Lock)
    (runtime : Runtime World Vector) (toOffset : N → M World I)
    (systemerror : String → Bool → M World Unit) (stream : Stream) (offset : N) : M World Stream := do
  let status ← lockIos access locks stream (do
    let pointer ← iosPointer access runtime stream
    runtime.seek pointer (← toOffset offset))
  systemerror "seek" (status.val = -1)
  if status.val < -1 then throw (.errorException "seek failed")
  pure stream

-- UNTRANSLATED
-- Source: base/iostream.jl:164-184 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     seekstart(s)
-- 
-- Seek a stream to its beginning.
-- 
-- # Examples
-- ```jldoctest
-- julia> io = IOBuffer("JuliaLang is a GitHub organization.");
-- 
-- julia> seek(io, 5);
-- 
-- julia> read(io, Char)
-- 'L': ASCII/Unicode U+004C (category Lu: Letter, uppercase)
-- 
-- julia> seekstart(io);
-- 
-- julia> read(io, Char)
-- 'J': ASCII/Unicode U+004A (category Lu: Letter, uppercase)
-- ```
-- """
-- /Source
-- Reason: Documentation, type declarations, or dispatch metadata; no method body.

/--
Julia source: base/iostream.jl:185-185 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
seekstart(s::IO) = seek(s,0)
```
-/
def seekstart {World Stream : Type} (seek : Stream → I → M World Stream)
    (stream : Stream) : M World Stream := seek stream (i 0)

-- UNTRANSLATED
-- Source: base/iostream.jl:186-191 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     seekend(s)
-- 
-- Seek a stream to its end.
-- """
-- /Source
-- Reason: Documentation, type declarations, or dispatch metadata; no method body.

/--
Julia source: base/iostream.jl:192-196 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function seekend(s::IOStream)
    err = @_lock_ios s ccall(:ios_seek_end, Int64, (Ptr{Cvoid},), s.ios) != 0
    systemerror("seekend", err)
    return s
end
```
-/
def seekend {World Stream Vector Lock : Type}
    (access : Access World Stream Vector Lock) (locks : Locks World Lock)
    (runtime : Runtime World Vector) (systemerror : String → Bool → M World Unit)
    (stream : Stream) : M World Stream := do
  let status ← lockIos access locks stream (do runtime.seekend (← iosPointer access runtime stream))
  systemerror "seekend" (status.val != 0)
  pure stream

-- UNTRANSLATED
-- Source: base/iostream.jl:197-214 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     skip(s, offset)
-- 
-- Seek a stream relative to the current position.
-- 
-- # Examples
-- ```jldoctest
-- julia> io = IOBuffer("JuliaLang is a GitHub organization.");
-- 
-- julia> seek(io, 5);
-- 
-- julia> skip(io, 10);
-- 
-- julia> read(io, Char)
-- 'G': ASCII/Unicode U+0047 (category Lu: Letter, uppercase)
-- ```
-- """
-- /Source
-- Reason: Documentation, type declarations, or dispatch metadata; no method body.

/--
Julia source: base/iostream.jl:215-220 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function skip(s::IOStream, delta::Integer)
    ret = @_lock_ios s ccall(:ios_skip, Int64, (Ptr{Cvoid}, Int64), s.ios, delta)
    systemerror("skip", ret == -1)
    ret < -1 && error("skip failed")
    return s
end
```
-/
def skip {World Stream Vector Lock N : Type}
    (access : Access World Stream Vector Lock) (locks : Locks World Lock)
    (runtime : Runtime World Vector) (toOffset : N → M World I)
    (systemerror : String → Bool → M World Unit) (stream : Stream) (offset : N) : M World Stream := do
  let status ← lockIos access locks stream (do
    let pointer ← iosPointer access runtime stream
    runtime.skip pointer (← toOffset offset))
  systemerror "skip" (status.val = -1)
  if status.val < -1 then throw (.errorException "skip failed")
  pure stream

-- UNTRANSLATED
-- Source: base/iostream.jl:221-246 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     position(s)
-- 
-- Get the current position of a stream.
-- 
-- # Examples
-- ```jldoctest
-- julia> io = IOBuffer("JuliaLang is a GitHub organization.");
-- 
-- julia> seek(io, 5);
-- 
-- julia> position(io)
-- 5
-- 
-- julia> skip(io, 10);
-- 
-- julia> position(io)
-- 15
-- 
-- julia> seekend(io);
-- 
-- julia> position(io)
-- 35
-- ```
-- """
-- /Source
-- Reason: Documentation, type declarations, or dispatch metadata; no method body.

/--
Julia source: base/iostream.jl:247-251 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function position(s::IOStream)
    pos = @_lock_ios s ccall(:ios_pos, Int64, (Ptr{Cvoid},), s.ios)
    systemerror("position", pos == -1)
    return pos
end
```
-/
def position {World Stream Vector Lock : Type}
    (access : Access World Stream Vector Lock) (locks : Locks World Lock)
    (runtime : Runtime World Vector) (systemerror : String → Bool → M World Unit)
    (stream : Stream) : M World I := do
  let position ← lockIos access locks stream (do runtime.position (← iosPointer access runtime stream))
  systemerror "position" (position.val = -1)
  pure position

-- UNTRANSLATED
-- Source: base/iostream.jl:252-252 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, type declarations, or dispatch metadata; no method body.

/--
Julia source: base/iostream.jl:253-260 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function filesize(s::IOStream)
    sz = @_lock_ios s ccall(:ios_filesize, Int64, (Ptr{Cvoid},), s.ios)
    if sz == -1
        # if `s` is not seekable `ios_filesize` can fail, so fall back to slower stat method
        sz = filesize(stat(s))
    end
    return sz
end
```
-/
def filesize {World Stream Vector Lock Stat : Type}
    (access : Access World Stream Vector Lock) (locks : Locks World Lock)
    (runtime : Runtime World Vector) (stat : Stream → M World Stat)
    (statSize : Stat → M World I) (stream : Stream) : M World I := do
  let size ← lockIos access locks stream (do runtime.filesize (← iosPointer access runtime stream))
  if size.val = -1 then statSize (← stat stream) else pure size

-- UNTRANSLATED
-- Source: base/iostream.jl:261-261 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, type declarations, or dispatch metadata; no method body.

/--
Julia source: base/iostream.jl:262-262 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_eof_nolock(s::IOStream) = ccall(:ios_eof_blocking, Cint, (Ptr{Cvoid},), s.ios) != 0
```
-/
def eofNolock {World Stream Vector Lock : Type}
    (access : Access World Stream Vector Lock) (runtime : Runtime World Vector)
    (stream : Stream) : M World Bool := do
  pure ((← runtime.eof (← iosPointer access runtime stream)).val != 0)

/--
Julia source: base/iostream.jl:263-268 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function eof(s::IOStream; cancel::CancelTokenArg=DEFAULT_CANCEL)
    # entry check only: IOStream reads block in C and are not
    # interruptible (likewise for every `check_cancel_arg` below)
    check_cancel_arg(cancel)
    @_lock_ios s _eof_nolock(s)
end
```
-/
def eof {World Stream Vector Lock Token : Type}
    (access : Access World Stream Vector Lock) (locks : Locks World Lock)
    (runtime : Runtime World Vector) (cancellation : Cancellation World Token)
    (stream : Stream) (cancel : CancelArg Token) : M World Bool := do
  let _ ← cancellation.check cancel
  lockIos access locks stream (eofNolock access runtime stream)

-- UNTRANSLATED
-- Source: base/iostream.jl:269-280 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- ## constructing and opening streams ##
-- 
-- # "own" means the descriptor will be closed with the IOStream
-- 
-- """
--     fdio([name::AbstractString, ]fd::Integer[, own::Bool=false])::IOStream
-- 
-- Create an [`IOStream`](@ref) object from an integer file descriptor. If `own` is `true`, closing
-- this object will close the underlying descriptor. By default, an `IOStream` is closed when
-- it is garbage collected. `name` allows you to associate the descriptor with a named file.
-- """
-- /Source
-- Reason: Documentation, type declarations, or dispatch metadata; no method body.

/--
Julia source: base/iostream.jl:281-286 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function fdio(name::AbstractString, fd::Integer, own::Bool=false)
    s = IOStream(name)
    ccall(:ios_fd, Ptr{Cvoid}, (Ptr{Cvoid}, Clong, Cint, Cint),
          s.ios, fd, 0, own)
    return s
end
```
-/
def fdioNamed {World Stream Vector Lock Name N : Type}
    (access : Access World Stream Vector Lock) (runtime : Runtime World Vector)
    (construct : Name → M World Stream) (toLong : N → M World I)
    (name : Name) (descriptor : N) (own : Bool := false) : M World Stream := do
  let stream ← construct name
  let pointer ← iosPointer access runtime stream
  let descriptor ← toLong descriptor
  let _ ← runtime.fdio pointer descriptor (cint 0) (cint (if own then 1 else 0))
  pure stream

/--
Julia source: base/iostream.jl:287-287 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fdio(fd::Integer, own::Bool=false) = fdio(string("<fd ",fd,">"), fd, own)
```
-/
def fdio {World Stream N : Type} (showFD : N → M World Text)
    (string : List Text → M World Text) (fdio : Text → N → Bool → M World Stream)
    (descriptor : N) (own : Bool := false) : M World Stream := do
  let name ← string [text "<fd ", ← showFD descriptor, text ">"]
  fdio name descriptor own

-- UNTRANSLATED
-- Source: base/iostream.jl:288-315 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     open(filename::AbstractString; lock = true, keywords...)::IOStream
-- 
-- Open a file in a mode specified by five boolean keyword arguments:
-- 
-- | Keyword    | Description             | Default                                 |
-- |:-----------|:-----------------------|:----------------------------------------|
-- | `read`     | open for reading       | `!write`                                |
-- | `write`    | open for writing       | `truncate \\| append`                   |
-- | `create`   | create if non-existent | `!read & write \\| truncate \\| append` |
-- | `truncate` | truncate to zero size  | `!read & write`                         |
-- | `append`   | seek to end            | `false`                                 |
-- 
-- The default when no keywords are passed is to open files for reading only.
-- Returns a stream for accessing the opened file.
-- 
-- The stream is closed automatically when it is garbage collected, but since it is not known
-- when that happens, call [`close`](@ref) explicitly (or use the `open(f::Function, filename)` form,
-- which calls `f` on the stream and closes it when `f` returns) to ensure that written data is
-- flushed and the file is released.
-- 
-- The `lock` keyword argument controls whether operations will be locked for
-- safe multi-threaded access.
-- 
-- !!! compat "Julia 1.5"
--     The `lock` argument is available as of Julia 1.5.
-- """
-- /Source
-- Reason: Documentation, type declarations, or dispatch metadata; no method body.

/--
Julia source: base/iostream.jl:316-345 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function open(fname::String; lock = true,
    read     :: Union{Bool,Nothing} = nothing,
    write    :: Union{Bool,Nothing} = nothing,
    create   :: Union{Bool,Nothing} = nothing,
    truncate :: Union{Bool,Nothing} = nothing,
    append   :: Union{Bool,Nothing} = nothing,
)
    flags = open_flags(
        read = read,
        write = write,
        create = create,
        truncate = truncate,
        append = append,
    )
    s = IOStream(string("<file ",fname,">"))
    if !lock
        s._dolock = false
    end
    if ccall(:ios_file, Ptr{Cvoid},
             (Ptr{UInt8}, Cstring, Cint, Cint, Cint, Cint),
             s.ios, fname, flags.read, flags.write, flags.create, flags.truncate) == C_NULL
        systemerror("opening file $(repr(fname))")
    end
    if flags.append
        if ccall(:ios_seek_end, Int64, (Ptr{Cvoid},), s.ios) != 0
            systemerror("seeking to end of file $fname")
        end
    end
    return s
end
```
-/
def openFile {World Stream Vector Lock : Type}
    (access : Access World Stream Vector Lock) (runtime : Runtime World Vector)
    (string : List Text → M World Text) (construct : Text → M World Stream)
    (repr display : Text → M World String) (systemerror : String → M World Unit)
    (filename : Text) (lock : Bool) (keywords : OpenKeywords) : M World Stream := do
  let flags := JuliaLean.base.io.openFlags keywords.read keywords.write keywords.create
    keywords.truncate keywords.append
  let stream ← construct (← string [text "<file ", filename, text ">"])
  if !lock then access.set stream { (← access.get stream) with dolock := false }
  let pointer ← iosPointer access runtime stream
  let filenamePointer ← runtime.cString filename
  let result ← runtime.file pointer filenamePointer
    (cint (if flags.read then 1 else 0)) (cint (if flags.write then 1 else 0))
    (cint (if flags.create then 1 else 0)) (cint (if flags.truncate then 1 else 0))
  if result.address.val = 0 then systemerror ("opening file " ++ (← repr filename))
  if flags.append then
    if (← runtime.seekend (← iosPointer access runtime stream)).val != 0 then
      systemerror ("seeking to end of file " ++ (← display filename))
  pure stream

/--
Julia source: base/iostream.jl:346-346 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
open(fname::AbstractString; kwargs...) = open(convert(String, fname)::String; kwargs...)
```
-/
def openAbstractStringChecked {World Name Kw Result Other : Type}
    (convert : Name → M World
      (JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Text Other))
    (openFile : Text → Kw → M World Result)
    (name : Name) (keywords : Kw) : M World Result := do
  let converted ← convert name
  match (JuliaLean.base.abstractarray.Models1Group1.assertType converted :
      Except JuliaLean.base.abstractarray.ArrayError Text) with
  | .ok filename => openFile filename keywords
  | .error _ => throw (.showError .typeError)

def openAbstractString {World Name Kw Stream : Type}
    (convert : Name → M World Text) (openFile : Text → Kw → M World Stream)
    (name : Name) (keywords : Kw) : M World Stream :=
  openAbstractStringChecked (Other := Empty) (fun name => do
    pure (.accepted (← convert name))) openFile name keywords

-- UNTRANSLATED
-- Source: base/iostream.jl:347-398 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     open(filename::AbstractString, [mode::AbstractString]; lock = true)::IOStream
-- 
-- Alternate syntax for open, where a string-based mode specifier is used instead of the five
-- booleans. The values of `mode` correspond to those from `fopen(3)` or Perl `open`, and are
-- equivalent to setting the following boolean groups:
-- 
-- | Mode | Description                   | Keywords                            |
-- |:-----|:------------------------------|:------------------------------------|
-- | `r`  | read                          | none                                |
-- | `w`  | write, create, truncate       | `write = true`                      |
-- | `a`  | write, create, append         | `append = true`                     |
-- | `r+` | read, write                   | `read = true, write = true`         |
-- | `w+` | read, write, create, truncate | `truncate = true, read = true`      |
-- | `a+` | read, write, create, append   | `append = true, read = true`        |
-- 
-- The `lock` keyword argument controls whether operations will be locked for
-- safe multi-threaded access.
-- 
-- # Examples
-- ```jldoctest
-- julia> io = open("myfile.txt", "w");
-- 
-- julia> write(io, "Hello world!");
-- 
-- julia> close(io);
-- 
-- julia> io = open("myfile.txt", "r");
-- 
-- julia> read(io, String)
-- "Hello world!"
-- 
-- julia> write(io, "This file is read only")
-- ERROR: ArgumentError: write failed, IOStream is not writeable
-- [...]
-- 
-- julia> close(io)
-- 
-- julia> io = open("myfile.txt", "a");
-- 
-- julia> write(io, "This stream is not read only")
-- 28
-- 
-- julia> close(io)
-- 
-- julia> rm("myfile.txt")
-- ```
-- 
-- !!! compat "Julia 1.5"
--     The `lock` argument is available as of Julia 1.5.
-- """
-- /Source
-- Reason: Documentation, type declarations, or dispatch metadata; no method body.

/--
Julia source: base/iostream.jl:399-407 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function open(fname::AbstractString, mode::AbstractString; lock = true)
    mode == "r"  ? open(fname, lock = lock, read = true)                  :
    mode == "r+" ? open(fname, lock = lock, read = true, write = true)    :
    mode == "w"  ? open(fname, lock = lock, truncate = true)              :
    mode == "w+" ? open(fname, lock = lock, truncate = true, read = true) :
    mode == "a"  ? open(fname, lock = lock, append = true)                :
    mode == "a+" ? open(fname, lock = lock, append = true, read = true)   :
    throw(ArgumentError("invalid open mode: $mode"))
end
```
-/
def openMode {World Name Mode Stream : Type}
    (equal : Mode → Text → M World Bool) (display : Mode → M World String)
    (openFile : Name → Bool → OpenKeywords → M World Stream)
    (name : Name) (mode : Mode) (lock : Bool) : M World Stream := do
  if ← equal mode (text "r") then return (← openFile name lock { read := some true })
  if ← equal mode (text "r+") then return (← openFile name lock { read := some true, write := some true })
  if ← equal mode (text "w") then return (← openFile name lock { truncate := some true })
  if ← equal mode (text "w+") then return (← openFile name lock { truncate := some true, read := some true })
  if ← equal mode (text "a") then return (← openFile name lock { append := some true })
  if ← equal mode (text "a+") then return (← openFile name lock { append := some true, read := some true })
  throw (.jl (.argumentError ("invalid open mode: " ++ (← display mode))))

-- UNTRANSLATED
-- Source: base/iostream.jl:408-410 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- ## low-level calls ##
-- 
-- /Source
-- Reason: Documentation, type declarations, or dispatch metadata; no method body.

/--
Julia source: base/iostream.jl:411-414 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function write(s::IOStream, b::UInt8)
    iswritable(s) || throw(ArgumentError("write failed, IOStream is not writeable"))
    Int(@_lock_ios s ccall(:ios_putc, Cint, (Cint, Ptr{Cvoid}), b, s.ios))
end
```
-/
def writeByte {World Stream Vector Lock : Type}
    (access : Access World Stream Vector Lock) (locks : Locks World Lock)
    (runtime : Runtime World Vector) (stream : Stream) (value : Byte) : M World I := do
  if !(← iswritable access runtime stream) then
    throw (.jl (.argumentError "write failed, IOStream is not writeable"))
  toInt (← lockIos access locks stream (do
    runtime.putc (JInt.rem .i32 value) (← iosPointer access runtime stream)))

-- UNTRANSLATED
-- Source: base/iostream.jl:415-415 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, type declarations, or dispatch metadata; no method body.

/--
Julia source: base/iostream.jl:416-426 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_write(s::IOStream, p::Ptr{UInt8}, nb::UInt; cancel::CancelTokenArg=DEFAULT_CANCEL)
    # Explicit tokens gate at entry (which keeps explicit-token writes -
    # e.g. `write(io, ::String; cancel=...)` - working on files); the
    # sentinel deliberately passes without resolving the ambient scope: a
    # plain print to a file is not a cancellation point (unlike the
    # C-side-blocking reads above), so e.g. logging during cancellation
    # cleanup keeps working unshielded.
    precheck_cancel_arg(cancel)
    iswritable(s) || throw(ArgumentError("write failed, IOStream is not writeable"))
    return Int(@_lock_ios s ccall(:ios_write, Csize_t, (Ptr{Cvoid}, Ptr{Cvoid}, Csize_t), s.ios, p, nb))
end
```
-/
def unsafeWrite {World Stream Vector Lock Token : Type}
    (access : Access World Stream Vector Lock) (locks : Locks World Lock)
    (runtime : Runtime World Vector) (precheck : CancelArg Token → M World (CancelArg Token))
    (stream : Stream) (pointer : BytePointer) (count : U) (cancel : CancelArg Token) : M World I := do
  let _ ← precheck cancel
  if !(← iswritable access runtime stream) then
    throw (.jl (.argumentError "write failed, IOStream is not writeable"))
  toInt (← lockIos access locks stream (do
    runtime.write (← iosPointer access runtime stream) pointer count))

-- UNTRANSLATED
-- Source: base/iostream.jl:427-428 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # num bytes available without blocking
-- /Source
-- Reason: Documentation, type declarations, or dispatch metadata; no method body.

/--
Julia source: base/iostream.jl:429-429 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
bytesavailable(s::IOStream) = @_lock_ios s ccall(:jl_nb_available, Int32, (Ptr{Cvoid},), s.ios)
```
-/
def bytesavailable {World Stream Vector Lock : Type}
    (access : Access World Stream Vector Lock) (locks : Locks World Lock)
    (runtime : Runtime World Vector) (stream : Stream) : M World CInt :=
  lockIos access locks stream (do runtime.available (← iosPointer access runtime stream))

-- UNTRANSLATED
-- Source: base/iostream.jl:430-430 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, type declarations, or dispatch metadata; no method body.

/--
Julia source: base/iostream.jl:431-447 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function readavailable(s::IOStream; cancel::CancelTokenArg=DEFAULT_CANCEL)
    check_cancel_arg(cancel)
    lock(s.lock)
    nb = ccall(:jl_nb_available, Int32, (Ptr{Cvoid},), s.ios)
    if nb == 0
        ccall(:ios_fillbuf, Cssize_t, (Ptr{Cvoid},), s.ios)
        nb = ccall(:jl_nb_available, Int32, (Ptr{Cvoid},), s.ios)
    end
    a = Vector{UInt8}(undef, nb)
    nr = ccall(:ios_readall, Csize_t, (Ptr{Cvoid}, Ptr{Cvoid}, Csize_t), s, a, nb)
    if nr != nb
        unlock(s.lock)
        throw(EOFError())
    end
    unlock(s.lock)
    return a
end
```
-/
def readavailable {World Stream Vector Lock Token : Type}
    (access : Access World Stream Vector Lock) (locks : Locks World Lock)
    (runtime : Runtime World Vector) (cancellation : Cancellation World Token)
    (allocate : CInt → M World Vector) (stream : Stream) (cancel : CancelArg Token) : M World Vector := do
  let _ ← cancellation.check cancel
  locks.lock (← access.get stream).mutex
  let count ← runtime.available (← iosPointer access runtime stream)
  let count ← if count.val = 0 then do
    let _ ← runtime.fillbuf (← iosPointer access runtime stream)
    runtime.available (← iosPointer access runtime stream)
    else pure count
  let array ← allocate count
  let pointer ← iosPointer access runtime stream
  let destination ← runtime.bytePointer array
  let requested ← JuliaLean.base.io.liftJl (JInt.convert (IntTy.u64.name) .u64 count.val)
  let readCount ← runtime.readall pointer destination requested
  if readCount.val != count.val then
    locks.unlock (← access.get stream).mutex
    throw .eofError
  locks.unlock (← access.get stream).mutex
  pure array

-- UNTRANSLATED
-- Source: base/iostream.jl:448-448 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, type declarations, or dispatch metadata; no method body.

/--
Julia source: base/iostream.jl:449-455 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function read(s::IOStream, ::Type{UInt8})
    b = @_lock_ios s ccall(:ios_getc, Cint, (Ptr{Cvoid},), s.ios)
    if b == -1
        throw(EOFError())
    end
    return b % UInt8
end
```
-/
def readByte {World Stream Vector Lock : Type}
    (access : Access World Stream Vector Lock) (locks : Locks World Lock)
    (runtime : Runtime World Vector) (stream : Stream) : M World Byte := do
  let value ← lockIos access locks stream (do runtime.getc (← iosPointer access runtime stream))
  if value.val = -1 then throw .eofError
  pure (JInt.rem .u8 value)

-- UNTRANSLATED
-- Source: base/iostream.jl:456-457 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- if ENDIAN_BOM == 0x04030201
-- /Source
-- Reason: Documentation, type declarations, or dispatch metadata; no method body.

/--
Julia source: base/iostream.jl:458-470 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function read(s::IOStream, T::Union{Type{Int16},Type{UInt16},Type{Int32},Type{UInt32},Type{Int64},Type{UInt64}})
    n = sizeof(T)
    l = s._dolock
    _lock = s.lock
    l && lock(_lock)
    if ccall(:jl_ios_buffer_n, Cint, (Ptr{Cvoid}, Csize_t), s.ios, n) != 0
        l && unlock(_lock)
        throw(EOFError())
    end
    x = ccall(:jl_ios_get_nbyte_int, UInt64, (Ptr{Cvoid}, Csize_t), s.ios, n) % T
    l && unlock(_lock)
    return x
end
```
-/
def readInteger {World Stream Vector Lock : Type}
    (access : Access World Stream Vector Lock) (locks : Locks World Lock)
    (runtime : Runtime World Vector) (stream : Stream) (type : IntTy)
    (_supported : type = .i16 ∨ type = .u16 ∨ type = .i32 ∨ type = .u32 ∨ type = .i64 ∨ type = .u64) :
    M World (JInt type) := do
  let count := u (type.bits / 8)
  let fields ← access.get stream
  if fields.dolock then locks.lock fields.mutex
  if (← runtime.bufferN (← iosPointer access runtime stream) count).val != 0 then
    if fields.dolock then locks.unlock fields.mutex
    throw .eofError
  let value ← runtime.getNbyteInt (← iosPointer access runtime stream) count
  let value := JInt.rem type value
  if fields.dolock then locks.unlock fields.mutex
  pure value

-- UNTRANSLATED
-- Source: base/iostream.jl:471-471 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, type declarations, or dispatch metadata; no method body.

/--
Julia source: base/iostream.jl:472-472 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
read(s::IOStream, ::Type{Float16}) = reinterpret(Float16, read(s, Int16))
```
-/
def readFloat16 {World Stream : Type}
    (read : Stream → M World (JInt .i16)) (stream : Stream) :
    M World (JuliaLean.base.float.FV .f16) := do
  pure (JuliaLean.base.float.reinterpret_Float_Int .f16 (← read stream))

/--
Julia source: base/iostream.jl:473-473 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
read(s::IOStream, ::Type{Float32}) = reinterpret(Float32, read(s, Int32))
```
-/
def readFloat32 {World Stream : Type}
    (read : Stream → M World (JInt .i32)) (stream : Stream) :
    M World (JuliaLean.base.float.FV .f32) := do
  pure (JuliaLean.base.float.reinterpret_Float_Int .f32 (← read stream))

/--
Julia source: base/iostream.jl:474-474 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
read(s::IOStream, ::Type{Float64}) = reinterpret(Float64, read(s, Int64))
```
-/
def readFloat64 {World Stream : Type}
    (read : Stream → M World (JInt .i64)) (stream : Stream) :
    M World (JuliaLean.base.float.FV .f64) := do
  pure (JuliaLean.base.float.reinterpret_Float_Int .f64 (← read stream))

-- UNTRANSLATED
-- Source: base/iostream.jl:475-476 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- end
-- 
-- /Source
-- Reason: Documentation, type declarations, or dispatch metadata; no method body.

/--
Julia source: base/iostream.jl:477-483 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_read(s::IOStream, p::Ptr{UInt8}, nb::UInt)
    nr = @_lock_ios s ccall(:ios_readall, Csize_t, (Ptr{Cvoid}, Ptr{Cvoid}, Csize_t), s, p, nb)
    if nr != nb
        throw(EOFError())
    end
    nothing
end
```
-/
def unsafeRead {World Stream Vector Lock : Type}
    (access : Access World Stream Vector Lock) (locks : Locks World Lock)
    (runtime : Runtime World Vector) (stream : Stream) (pointer : BytePointer) (count : U) : M World Unit := do
  let readCount ← lockIos access locks stream (do
    runtime.readall (← iosPointer access runtime stream) pointer count)
  if readCount.val != count.val then throw .eofError

-- UNTRANSLATED
-- Source: base/iostream.jl:484-486 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- ## text I/O ##
-- 
-- /Source
-- Reason: Documentation, type declarations, or dispatch metadata; no method body.

/--
Julia source: base/iostream.jl:487-488 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
take!(s::IOStream) =
    @_lock_ios s ccall(:jl_take_buffer, Vector{UInt8}, (Ptr{Cvoid},), s.ios)
```
-/
def take {World Stream Vector Lock : Type}
    (access : Access World Stream Vector Lock) (locks : Locks World Lock)
    (runtime : Runtime World Vector) (stream : Stream) : M World Vector :=
  lockIos access locks stream (do runtime.takeBuffer (← iosPointer access runtime stream))

-- UNTRANSLATED
-- Source: base/iostream.jl:489-489 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, type declarations, or dispatch metadata; no method body.

/--
Julia source: base/iostream.jl:490-493 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function readuntil(s::IOStream, delim::UInt8; keep::Bool=false, cancel::CancelTokenArg=DEFAULT_CANCEL)
    check_cancel_arg(cancel)
    @_lock_ios s ccall(:jl_readuntil, Vector{UInt8}, (Ptr{Cvoid}, UInt8, UInt8, UInt8), s.ios, delim, 0, !keep)
end
```
-/
def readuntilByte {World Stream Vector Lock Token : Type}
    (access : Access World Stream Vector Lock) (locks : Locks World Lock)
    (runtime : Runtime World Vector) (cancellation : Cancellation World Token)
    (stream : Stream) (delim : Byte) (keep : Bool) (cancel : CancelArg Token) : M World Vector := do
  let _ ← cancellation.check cancel
  lockIos access locks stream (do
    runtime.readuntilBytes (← iosPointer access runtime stream)
      delim (JuliaLean.base.io.byte 0) (JuliaLean.base.io.byte (if keep then 0 else 1)))

-- UNTRANSLATED
-- Source: base/iostream.jl:494-495 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # like readuntil, above, but returns a String without requiring a copy
-- /Source
-- Reason: Documentation, type declarations, or dispatch metadata; no method body.

/--
Julia source: base/iostream.jl:496-498 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function readuntil_string(s::IOStream, delim::UInt8, keep::Bool)
    @_lock_ios s ccall(:jl_readuntil, Ref{String}, (Ptr{Cvoid}, UInt8, UInt8, UInt8), s.ios, delim, 1, !keep)
end
```
-/
def readuntilString {World Stream Vector Lock : Type}
    (access : Access World Stream Vector Lock) (locks : Locks World Lock)
    (runtime : Runtime World Vector) (stream : Stream) (delim : Byte) (keep : Bool) : M World Text :=
  lockIos access locks stream (do
    runtime.readuntilString (← iosPointer access runtime stream)
      delim (JuliaLean.base.io.byte 1) (JuliaLean.base.io.byte (if keep then 0 else 1)))

/--
Julia source: base/iostream.jl:499-503 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function readuntil(s::IOStream, delim::AbstractChar; keep::Bool=false, cancel::CancelTokenArg=DEFAULT_CANCEL)
    tok = check_cancel_arg(cancel)
    return isascii(delim) ? readuntil_string(s, delim % UInt8, keep) :
        takestring!(copyuntil(IOBuffer(sizehint=70), s, delim; keep, cancel=tok))
end
```
-/
def readuntilChar {World Stream Vector Lock Char Buffer Token : Type}
    (access : Access World Stream Vector Lock) (locks : Locks World Lock)
    (runtime : Runtime World Vector) (cancellation : Cancellation World Token)
    (isAscii : Char → M World Bool) (toByte : Char → M World Byte)
    (newBuffer : I → M World Buffer)
    (copyuntil : Buffer → Stream → Char → Bool → CancelArg Token → M World Buffer)
    (takestring : Buffer → M World Text) (stream : Stream) (delim : Char) (keep : Bool)
    (cancel : CancelArg Token) : M World Text := do
  let token ← cancellation.check cancel
  if ← isAscii delim then readuntilString access locks runtime stream (← toByte delim) keep
  else takestring (← copyuntil (← newBuffer (i 70)) stream delim keep token)

-- UNTRANSLATED
-- Source: base/iostream.jl:504-504 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, type declarations, or dispatch metadata; no method body.

/--
Julia source: base/iostream.jl:505-508 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function readline(s::IOStream; keep::Bool=false, cancel::CancelTokenArg=DEFAULT_CANCEL)
    check_cancel_arg(cancel)
    @_lock_ios s ccall(:jl_readuntil, Ref{String}, (Ptr{Cvoid}, UInt8, UInt8, UInt8), s.ios, '\n', 1, keep ? 0 : 2)
end
```
-/
def readline {World Stream Vector Lock Token : Type}
    (access : Access World Stream Vector Lock) (locks : Locks World Lock)
    (runtime : Runtime World Vector) (cancellation : Cancellation World Token)
    (stream : Stream) (keep : Bool) (cancel : CancelArg Token) : M World Text := do
  let _ ← cancellation.check cancel
  lockIos access locks stream (do
    runtime.readuntilString (← iosPointer access runtime stream)
      (JuliaLean.base.io.byte 10) (JuliaLean.base.io.byte 1) (JuliaLean.base.io.byte (if keep then 0 else 2)))

-- UNTRANSLATED
-- Source: base/iostream.jl:509-509 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, type declarations, or dispatch metadata; no method body.

/--
Julia source: base/iostream.jl:510-533 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copyuntil(out::IOBuffer, s::IOStream, delim::UInt8; keep::Bool=false, cancel::CancelTokenArg=DEFAULT_CANCEL)
    check_cancel_arg(cancel)
    ensureroom(out, 1) # make sure we can read at least 1 byte, for iszero(n) check below
    while true
        d = out.data
        len = length(d)
        ptr = (out.append ? out.size+1 : out.ptr)
        GC.@preserve d @_lock_ios s n=
            Int(ccall(:jl_readuntil_buf, Csize_t, (Ptr{Cvoid}, UInt8, Ptr{UInt8}, Csize_t),
                s.ios, delim, pointer(d, ptr), (len - ptr + 1) % Csize_t))
        iszero(n) && break
        ptr += n
        found = (d[ptr - 1] == delim)
        found && !keep && (ptr -= 1)
        out.size = max(out.size, ptr - 1)
        out.append || (out.ptr = ptr)
        found && break
        (eof(s) || len == out.maxsize) && break
        len = min(2len + 64, out.maxsize)
        ensureroom(out, len)
        @assert length(out.data) >= len "length(out.data) < len"
    end
    return out
end
```
-/
def copyuntilBufferPreserved {World Stream Vector Lock Out Data Token : Type}
    (access : Access World Stream Vector Lock) (locks : Locks World Lock)
    (runtime : Runtime World Vector) (cancellation : Cancellation World Token)
    (buffer : JuliaLean.base.iobuffer.Access (M World) Out Data)
    (ensure : Out → I → M World Unit) (lengthData : Data → M World I)
    (pointer : Data → I → M World BytePointer) (get : Data → I → M World Byte)
    (preserve : {A : Type} → Data → M World A → M World A)
    (eof : Stream → M World Bool) (out : Out) (stream : Stream) (delim : Byte)
    (keep : Bool) (cancel : CancelArg Token) : M World Out := do
  let _ ← cancellation.check cancel
  ensure out (i 1)
  JuliaLean.base.io.whileLoop (fun _ : Unit => do
    let fields ← buffer.get out
    let data := fields.data
    let length ← lengthData data
    let position := if fields.append then fields.size + i 1 else fields.ptr
    let count ← preserve data (lockIos access locks stream (do
      let source ← iosPointer access runtime stream
      let destination ← pointer data position
      toInt (← runtime.readuntilBuffer source delim destination
        (JInt.rem .u64 (length - position + i 1)))))
    if count.val = 0 then return .inl out
    let position := position + count
    let found := (← get data (position - i 1)).val == delim.val
    let position := if found && !keep then position - i 1 else position
    let current ← buffer.get out
    let size := if current.size.val < (position - i 1).val then position - i 1 else current.size
    buffer.set out { current with size }
    let current ← buffer.get out
    if !current.append then buffer.set out { current with ptr := position }
    if found then return .inl out
    if ← eof stream then return .inl out
    let current ← buffer.get out
    if length.val = current.maxsize.val then return .inl out
    let next := i 2 * length + i 64
    let next := if next.val < current.maxsize.val then next else current.maxsize
    ensure out next
    let newLength ← lengthData (← buffer.get out).data
    if newLength.val < next.val then
      throw (.foreignError "AssertionError" "length(out.data) < len")
    return .inr ()) ()

/-- Compatibility specialization without observable GC-root bookkeeping.
Source: base/iostream.jl:510-533 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def copyuntilBuffer {World Stream Vector Lock Out Data Token : Type}
    (access : Access World Stream Vector Lock) (locks : Locks World Lock)
    (runtime : Runtime World Vector) (cancellation : Cancellation World Token)
    (buffer : JuliaLean.base.iobuffer.Access (M World) Out Data)
    (ensure : Out → I → M World Unit) (lengthData : Data → M World I)
    (pointer : Data → I → M World BytePointer) (get : Data → I → M World Byte)
    (eof : Stream → M World Bool) (out : Out) (stream : Stream) (delim : Byte)
    (keep : Bool) (cancel : CancelArg Token) : M World Out :=
  copyuntilBufferPreserved access locks runtime cancellation buffer ensure lengthData
    pointer get (fun _ body => body) eof out stream delim keep cancel

-- UNTRANSLATED
-- Source: base/iostream.jl:534-534 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, type declarations, or dispatch metadata; no method body.

/--
Julia source: base/iostream.jl:535-540 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copyuntil(out::IOStream, s::IOStream, delim::UInt8; keep::Bool=false, cancel::CancelTokenArg=DEFAULT_CANCEL)
    check_cancel_arg(cancel)
    @_lock_ios out @_lock_ios s ccall(:ios_copyuntil, Csize_t,
        (Ptr{Cvoid}, Ptr{Cvoid}, UInt8, Cint), out.ios, s.ios, delim, keep)
    return out
end
```
-/
def copyuntilStream {World Stream Vector Lock Token : Type}
    (access : Access World Stream Vector Lock) (locks : Locks World Lock)
    (runtime : Runtime World Vector) (cancellation : Cancellation World Token)
    (out stream : Stream) (delim : Byte) (keep : Bool) (cancel : CancelArg Token) : M World Stream := do
  let _ ← cancellation.check cancel
  let _ ← lockIos access locks out (lockIos access locks stream (do
    let destination ← iosPointer access runtime out
    let source ← iosPointer access runtime stream
    runtime.copyuntil destination source delim (cint (if keep then 1 else 0))))
  pure out

-- UNTRANSLATED
-- Source: base/iostream.jl:541-541 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, type declarations, or dispatch metadata; no method body.

/--
Julia source: base/iostream.jl:542-568 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function readbytes_all!(s::IOStream, b::MutableDenseArrayType{UInt8}, nb::Integer)
    olb = lb = length(b)
    nr = 0
    let l = s._dolock, slock = s.lock
        l && lock(slock)
        GC.@preserve b while nr < nb
            if lb < nr+1
                try
                    lb = max(65536, (nr+1) * 2)
                    resize!(b, lb)
                catch
                    l && unlock(slock)
                    rethrow()
                end
            end
            thisr = Int(ccall(:ios_readall, Csize_t, (Ptr{Cvoid}, Ptr{Cvoid}, Csize_t),
                            s.ios, pointer(b, nr+1), min(lb-nr, nb-nr)))
            nr += thisr
            (nr == nb || thisr == 0 || _eof_nolock(s)) && break
        end
        l && unlock(slock)
    end
    if lb > olb && lb > nr
        resize!(b, max(olb, nr)) # shrink to just contain input data if was resized
    end
    return nr
end
```
-/
def readbytesAllPreserved {World Stream Vector Lock Array N Difference Count : Type}
    (access : Access World Stream Vector Lock) (locks : Locks World Lock)
    (runtime : Runtime World Vector) (length : Array → M World I)
    (less equal : I → N → M World Bool) (subtract : N → I → M World Difference)
    (minimum : I → Difference → M World Count) (toSize : Count → M World U)
    (resize : Array → I → M World Unit) (pointerAt : Array → I → M World BytePointer)
    (preserve : {A : Type} → Array → M World A → M World A)
    (stream : Stream) (array : Array) (count : N) : M World I := do
  let original ← length array
  let fields ← access.get stream
  if fields.dolock then locks.lock fields.mutex
  let (readCount, bufferLength) ← preserve array (JuliaLean.base.io.whileLoop
    (fun ((readCount, bufferLength) : I × I) => do
      if !(← less readCount count) then return .inl (readCount, bufferLength)
      let bufferLength ← if bufferLength.val < (readCount + i 1).val then do
        let next := (readCount + i 1) * i 2
        let next := if next.val < 65536 then i 65536 else next
        tryCatch (resize array next) (fun error => do
          if fields.dolock then locks.unlock fields.mutex
          throw error)
        pure next
        else pure bufferLength
      let ios := (← access.get stream).ios
      let destination ← pointerAt array (readCount + i 1)
      let available := bufferLength - readCount
      let remaining ← subtract count readCount
      let requested ← toSize (← minimum available remaining)
      let source ← runtime.pointer ios
      let chunk ← toInt (← runtime.readall source destination requested)
      let readCount := readCount + chunk
      if ← equal readCount count then return .inl (readCount, bufferLength)
      if chunk.val = 0 then return .inl (readCount, bufferLength)
      if ← eofNolock access runtime stream then return .inl (readCount, bufferLength)
      return .inr (readCount, bufferLength)) (i 0, original))
  if fields.dolock then locks.unlock fields.mutex
  if bufferLength.val > original.val && bufferLength.val > readCount.val then
    resize array (if original.val < readCount.val then readCount else original)
  pure readCount

/-- Compatibility specialization without observable GC-root bookkeeping.
Source: base/iostream.jl:542-568 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def readbytesAll {World Stream Vector Lock N Difference Count : Type}
    (access : Access World Stream Vector Lock) (locks : Locks World Lock)
    (runtime : Runtime World Vector) (length : Vector → M World I)
    (less equal : I → N → M World Bool) (subtract : N → I → M World Difference)
    (minimum : I → Difference → M World Count) (toSize : Count → M World U)
    (resize : Vector → I → M World Unit) (pointerAt : Vector → I → M World BytePointer)
    (stream : Stream) (array : Vector) (count : N) : M World I :=
  readbytesAllPreserved access locks runtime length less equal subtract minimum toSize
    resize pointerAt (fun _ body => body) stream array count

-- UNTRANSLATED
-- Source: base/iostream.jl:569-569 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, type declarations, or dispatch metadata; no method body.

/--
Julia source: base/iostream.jl:570-585 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function readbytes_some!(s::IOStream, b::MutableDenseArrayType{UInt8}, nb::Integer)
    olb = length(b)
    if nb > olb
        resize!(b, nb)
    end
    local nr
    @_lock_ios s begin
    nr = GC.@preserve b Int(ccall(:ios_read, Csize_t, (Ptr{Cvoid}, Ptr{Cvoid}, Csize_t),
                                  s.ios, pointer(b), nb))
    end
    lb = length(b)
    if lb > olb && lb > nr
        resize!(b, max(olb, nr)) # shrink to just contain input data if was resized
    end
    return nr
end
```
-/
def readbytesSomePreserved {World Stream Vector Lock Array N : Type}
    (access : Access World Stream Vector Lock) (locks : Locks World Lock)
    (runtime : Runtime World Vector) (length : Array → M World I)
    (greater : N → I → M World Bool) (resizeCount : Array → N → M World Unit)
    (toSize : N → M World U) (resize : Array → I → M World Unit)
    (pointer : Array → M World BytePointer)
    (preserve : {A : Type} → Array → M World A → M World A)
    (stream : Stream) (array : Array) (count : N) : M World I := do
  let original ← length array
  if ← greater count original then resizeCount array count
  let readCount ← lockIos access locks stream (preserve array (do
    let ios := (← access.get stream).ios
    let destination ← pointer array
    let requested ← toSize count
    let source ← runtime.pointer ios
    toInt (← runtime.read source destination requested)))
  let length ← length array
  if length.val > original.val && length.val > readCount.val then
    resize array (if original.val < readCount.val then readCount else original)
  pure readCount

/-- Compatibility specialization without observable GC-root bookkeeping.
Source: base/iostream.jl:570-585 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def readbytesSome {World Stream Vector Lock N : Type}
    (access : Access World Stream Vector Lock) (locks : Locks World Lock)
    (runtime : Runtime World Vector) (length : Vector → M World I)
    (greater : N → I → M World Bool) (resizeCount : Vector → N → M World Unit)
    (toSize : N → M World U) (resize : Vector → I → M World Unit)
    (stream : Stream) (array : Vector) (count : N) : M World I :=
  readbytesSomePreserved access locks runtime length greater resizeCount toSize resize
    runtime.bytePointer (fun _ body => body) stream array count

-- UNTRANSLATED
-- Source: base/iostream.jl:586-598 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     readbytes!(stream::IOStream, b::AbstractVector{UInt8}, nb=length(b); all::Bool=true)
-- 
-- Read at most `nb` bytes from `stream` into `b`, returning the number of bytes read.
-- The size of `b` will be increased if needed (i.e. if `nb` is greater than `length(b)`
-- and enough bytes could be read), but it will never be decreased.
-- 
-- If `all` is `true` (the default), this function will block repeatedly trying to read all
-- requested bytes, until an error or end-of-file occurs. If `all` is `false`, at most one
-- `read` call is performed, and the amount of data returned is device-dependent. Note that not
-- all stream types support the `all` option.
-- """
-- /Source
-- Reason: Documentation, type declarations, or dispatch metadata; no method body.

/--
Julia source: base/iostream.jl:599-603 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function readbytes!(s::IOStream, b::MutableDenseArrayType{UInt8}, nb=length(b); all::Bool=true,
                    cancel::CancelTokenArg=DEFAULT_CANCEL)
    check_cancel_arg(cancel)
    return all ? readbytes_all!(s, b, nb) : readbytes_some!(s, b, nb)
end
```
-/
def readbytes {World Stream Vector N Token : Type} (cancellation : Cancellation World Token)
    (readAll readSome : Stream → Vector → N → M World I)
    (stream : Stream) (array : Vector) (count : N) (all : Bool) (cancel : CancelArg Token) : M World I := do
  let _ ← cancellation.check cancel
  if all then readAll stream array count else readSome stream array count

-- UNTRANSLATED
-- Source: base/iostream.jl:604-604 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, type declarations, or dispatch metadata; no method body.

/--
Julia source: base/iostream.jl:605-634 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function read(s::IOStream)
    # First we try to fill the buffer. If that gives us the whole file,
    # copy it out and return. Otherwise look at the file size and use it
    # to prealloate space. Determining the size requires extra syscalls,
    # which we want to avoid for small files.
    @_lock_ios s begin
        nb = ccall(:ios_fillbuf, Cssize_t, (Ptr{Cvoid},), s.ios)
        if nb != -1
            b = StringVector(nb)
            readbytes_all!(s, b, nb)
        else
            sz = try # filesize is just a hint, so ignore if it fails
                filesize(s)
            catch ex
                ex isa IOError || rethrow()
                Int64(-1)
            end
            if sz > 0
                pos = position(s)
                if pos > 0
                    sz -= pos
                end
            end
            b = StringVector(sz < 0 ? 1024 : sz)
            nr = readbytes_all!(s, b, sz < 0 ? typemax(Int) : sz)
            resize!(b, nr)
        end
    end
    return b
end
```
-/
def readAll {World Stream Vector Lock : Type}
    (access : Access World Stream Vector Lock) (locks : Locks World Lock)
    (runtime : Runtime World Vector) (filesize position : Stream → M World I)
    (isIOError : Error → Bool) (allocate : I → M World Vector)
    (readAll : Stream → Vector → I → M World I) (resize : Vector → I → M World Vector)
    (stream : Stream) : M World Vector :=
  lockIos access locks stream (do
    let count ← runtime.fillbuf (← iosPointer access runtime stream)
    if count.val != -1 then
      let array ← allocate count
      let _ ← readAll stream array count
      pure array
    else
      let mut size ← tryCatch (filesize stream) (fun error =>
        if isIOError error then pure (i (-1)) else throw error)
      if size.val > 0 then
        let position ← position stream
        if position.val > 0 then size := size - position
      let array ← allocate (if size.val < 0 then i 1024 else size)
      let count ← readAll stream array (if size.val < 0 then JInt.typemax .i64 else size)
      let _ ← resize array count
      pure array)

-- UNTRANSLATED
-- Source: base/iostream.jl:635-645 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     read(s::IOStream, nb::Integer; all=true)
-- 
-- Read at most `nb` bytes from `s`, returning a `Vector{UInt8}` of the bytes read.
-- 
-- If `all` is `true` (the default), this function will block repeatedly trying to read all
-- requested bytes, until an error or end-of-file occurs. If `all` is `false`, at most one
-- `read` call is performed, and the amount of data returned is device-dependent. Note that not
-- all stream types support the `all` option.
-- """
-- /Source
-- Reason: Documentation, type declarations, or dispatch metadata; no method body.

/--
Julia source: base/iostream.jl:646-654 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function read(s::IOStream, nb::Integer; all::Bool=true, cancel::CancelTokenArg=DEFAULT_CANCEL)
    check_cancel_arg(cancel)
    # When all=false we have to allocate a buffer of the requested size upfront
    # since a single call will be made
    b = Vector{UInt8}(undef, all && nb == typemax(Int) ? 1024 : nb)
    nr = readbytes!(s, b, nb, all=all)
    resize!(b, nr)
    return b
end
```
-/
def readCount {World Stream Vector N Token : Type}
    (cancellation : Cancellation World Token) (isTypemax : N → M World Bool)
    (allocate : Sum I N → M World Vector)
    (readbytes : Stream → Vector → N → Bool → M World I)
    (resize : Vector → I → M World Unit) (stream : Stream) (count : N)
    (all : Bool) (cancel : CancelArg Token) : M World Vector := do
  let _ ← cancellation.check cancel
  let useDefault ← if all then isTypemax count else pure false
  let array ← allocate (if useDefault then .inl (i 1024) else .inr count)
  let count ← readbytes stream array count all
  resize array count
  pure array

-- UNTRANSLATED
-- Source: base/iostream.jl:655-657 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- ## peek ##
-- 
-- /Source
-- Reason: Documentation, type declarations, or dispatch metadata; no method body.

/--
Julia source: base/iostream.jl:658-664 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function peek(s::IOStream, ::Type{UInt8})
    b = @_lock_ios s ccall(:ios_peekc, Cint, (Ptr{Cvoid},), s.ios)
    if b == -1
        throw(EOFError())
    end
    return b % UInt8
end
```
-/
def peekByte {World Stream Vector Lock : Type}
    (access : Access World Stream Vector Lock) (locks : Locks World Lock)
    (runtime : Runtime World Vector) (stream : Stream) : M World Byte := do
  let value ← lockIos access locks stream (do runtime.peekc (← iosPointer access runtime stream))
  if value.val = -1 then throw .eofError
  pure (JInt.rem .u8 value)

/-- IOStream supplies the generic IO operations; Int32 availability widens to Julia Int. -/
def genericIOOps {World Stream Vector Lock Token : Type}
    (access : Access World Stream Vector Lock) (locks : Locks World Lock)
    (runtime : Runtime World Vector) (cancellation : Cancellation World Token)
    (systemerror : String → Bool → M World Unit) : JuliaLean.base.io.Ops World Stream where
  readByte := readByte access locks runtime
  writeByte := writeByte access locks runtime
  eof := fun stream => eof access locks runtime cancellation stream .default
  bytesavailable := fun stream => do toInt (← bytesavailable access locks runtime stream)
  position := position access locks runtime systemerror
  seek := fun stream offset => do
    let _ ← seek access locks runtime pure systemerror stream offset
    pure ()
  seekend := fun stream => do
    let _ ← seekend access locks runtime systemerror stream
    pure ()
  getMark := fun stream => do pure (← access.get stream).mark
  setMark := fun stream marked => do
    let fields ← access.get stream
    access.set stream { fields with mark := marked }
  isopen := isopen access runtime
  close := close access locks runtime systemerror
  isreadable := isreadable access runtime
  iswritable := iswritable access runtime

end JuliaLean.base.iostream



namespace JuliaLean.base.iostream.Models2Group18


open JuliaLean
open JuliaLean.base.io (M Error I U Byte)
open JuliaLean.base.pointer (PointerMemoryRef)

/-- Only the primitive read of a mutable vector's `ref` field is abstract.
The vector handle is retained, so reallocating a shared vector changes the
pointer observed by all streams that refer to it. 
Source context: base/iostream.jl:34-35. -/
-- Source: base/iostream.jl:34-35 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unsafe_convert(T::Type{Ptr{Cvoid}}, s::IOStream) = convert(T, pointer(s.ios))
-- show(io::IO, s::IOStream) = print(io, "IOStream(", s.name, ")")
-- /Source
structure VectorRefOps (World Vector : Type) where
  getRef : Vector → M World (PointerMemoryRef Byte)

/-- Concrete `Vector{UInt8}` specialization of `pointer`, using the installed
array cconvert and memory-reference unsafe conversion. Julia source:
`base/abstractarray.jl:1279`, `base/pointer.jl:63,75-88`. -/
-- Source: base/abstractarray.jl:1279-1279 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- pointer(x::AbstractArray{T}) where {T} = unsafe_convert(Ptr{T}, cconvert(Ptr{T}, x))
-- /Source
def vectorPointer {World Vector : Type} (ops : VectorRefOps World Vector)
    (buffer : Vector) : M World BytePointer := do
  let reference ← ops.getRef buffer
  let converted := JuliaLean.base.pointer.cconvertArray (fun (_ : Vector) => reference) buffer
  pure (JuliaLean.base.pointer.unsafeConvertMemoryRef converted)

/-- The corresponding concrete Cvoid pointer conversion used by ccall.
Source reference: `base/pointer.jl:64,88`. -/
-- Source: base/pointer.jl:64-64 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unsafe_convert(::Type{Ptr{S}}, a::AbstractArray{T}) where {S,T} = convert(Ptr{S}, unsafe_convert(Ptr{T}, a))
-- /Source
def vectorCvoidPointer {World Vector : Type} (ops : VectorRefOps World Vector)
    (buffer : Vector) : M World Handle := do
  pure (JuliaLean.base.pointer.convertPtrType (← vectorPointer ops buffer))

/-- Close the two concrete vector-pointer operations in the installed foreign
runtime interface. All remaining fields are the installed typed C boundaries. 
Source context: base/iostream.jl:34-35. -/
-- Source: base/iostream.jl:34-35 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unsafe_convert(T::Type{Ptr{Cvoid}}, s::IOStream) = convert(T, pointer(s.ios))
-- show(io::IO, s::IOStream) = print(io, "IOStream(", s.name, ")")
-- /Source
def withVectorPointers {World Vector : Type} (ops : VectorRefOps World Vector)
    (runtime : Runtime World Vector) : Runtime World Vector :=
  { runtime with pointer := vectorCvoidPointer ops, bytePointer := vectorPointer ops }



end JuliaLean.base.iostream.Models2Group18

namespace JuliaLean.base.iostream.Models2Group18

open JuliaLean
open JuliaLean.base.io (I U Byte M)

/-- Representation adapter for the installed array allocation checks. The base
IO monad preserves every world change before an exception. `ExceptT` adds the
array model's checked exceptions without changing that state discipline. 
Source context: base/boot.jl:821-824. -/
-- Source: base/boot.jl:821-824 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eval(Core, :(function (self::Type{Array{T,1}})(::UndefInitializer, m::Int) where {T}
--     mem = fieldtype(fieldtype(self, :ref), :mem)(undef, m)
--     return $(Expr(:new, :self, :(memoryref(mem)), :((m,))))
-- end))
-- /Source
abbrev ByteAllocationM (World : Type) := ExceptT JuliaLean.base.array.Error (M World)

/-- Raw allocation, field access, memoryrefnew, compiler GC roots and the C
memset boundary required by Vector{UInt8}. No field represents zeros, fill!,
Vector(undef, n), checked memory allocation, pointer conversion or resize!.

The memory and array types are references into `World`; the same reference is
passed to the raw header constructor and later field reads, and the pointer
passed to memset comes from that reference. Memory lengths are checked by the
installed `array.arrayUndef1` before `allocateMemoryUnchecked` is reached.
The raw allocator receives a Nat only after the installed native Int/size_t
conversion and address-width checks. Its argument is both byte and element
count because the fixed UInt8 layout has size one.

Source reference: base/boot.jl:762,767,821-824; base/array.jl:473-480;
base/cmem.jl:40-43 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/boot.jl:762-762 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (self::Type{GenericMemory{kind,T,addrspace}})(::UndefInitializer, m::Int) where {T,addrspace,kind} = memorynew(self, m)
-- /Source
structure ByteAllocationRuntime (World Vector Memory RootToken : Type) where
  emptyMemory : M World Memory
  allocateMemoryUnchecked : Nat → M World Memory
  memoryrefNew : Memory → M World (JuliaLean.base.pointer.PointerMemoryRef Byte)
  newVectorHeader : JuliaLean.base.pointer.PointerMemoryRef Byte → I → M World Vector
  arrayRef : Vector → M World (JuliaLean.base.pointer.PointerMemoryRef Byte)
  length : Vector → M World I
  preserveBegin : JuliaLean.base.pointer.PointerMemoryRef Byte → M World RootToken
  preserveEnd : RootToken → M World Unit
  memsetCall : Handle → CInt → U → M World Handle

/-- UInt8 is one byte, unboxed and not a union. This is fixed concrete type
metadata supplied to the installed memory constructor, not an allocation law.
Source reference: base/boot.jl:762,821-824; src/genericmemory.c:75-102
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/boot.jl:762-762 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (self::Type{GenericMemory{kind,T,addrspace}})(::UndefInitializer, m::Int) where {T,addrspace,kind} = memorynew(self, m)
-- /Source
def byteAllocationLayout : JuliaLean.base.array.MemoryLayout :=
  { size := 1, isboxed := false, isunion := false }

/-- Inject a raw primitive computation without losing its state or IO error. 
Source context: base/boot.jl:821-824. -/
-- Source: base/boot.jl:821-824 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eval(Core, :(function (self::Type{Array{T,1}})(::UndefInitializer, m::Int) where {T}
--     mem = fieldtype(fieldtype(self, :ref), :mem)(undef, m)
--     return $(Expr(:new, :self, :(memoryref(mem)), :((m,))))
-- end))
-- /Source
def byteAllocationLift {World A : Type} (action : M World A) : ByteAllocationM World A :=
  ExceptT.lift action

/-- Representation-only exception bridge. The installed checked UInt8 allocator
can introduce only `argument`; raw primitive failures stay in the underlying IO
monad. Remaining cases retain their exception class if this adapter is reused.
`Nothing` denotes the non-exception value thrown by `throw(nothing)`.
Source reference: base/boot.jl:762; src/genericmemory.c:55-73
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/boot.jl:762-762 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (self::Type{GenericMemory{kind,T,addrspace}})(::UndefInitializer, m::Int) where {T,addrspace,kind} = memorynew(self, m)
-- /Source
def byteAllocationError : JuliaLean.base.array.Error → JuliaLean.base.io.Error
  | .argument message => .jl (.argumentError message)
  | .bounds => .jl .boundsError
  | .inexact => .jl (.inexactError "convert")
  | .overflow => .jl (.overflowError "")
  | .divide => .jl .divideError
  | .typeError context => .foreignError "TypeError" context
  | .dimensionMismatch message => .foreignError "DimensionMismatch" message
  | .method name => .jl (.methodError name)
  | .assertion message => .foreignError "AssertionError" message
  | .concurrency message => .foreignError "ConcurrencyViolationError" message
  | .thrownNothing => .foreignError "Nothing" ""
  | .undefinedReference => .foreignError "UndefRefError" ""
  | .showError error => .showError error

/-- Remove only the array-error representation layer. Mutations preceding an
array exception are retained because the exception is thrown after running the
ExceptT action in the existing state-preserving IO monad. 
Source context: base/boot.jl:821-824. -/
-- Source: base/boot.jl:821-824 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eval(Core, :(function (self::Type{Array{T,1}})(::UndefInitializer, m::Int) where {T}
--     mem = fieldtype(fieldtype(self, :ref), :mem)(undef, m)
--     return $(Expr(:new, :self, :(memoryref(mem)), :((m,))))
-- end))
-- /Source
def runByteAllocation {World A : Type} (action : ByteAllocationM World A) : M World A := do
  match ← action.run with
  | .ok value => pure value
  | .error error => throw (byteAllocationError error)

/-- Vector{UInt8}(undef,n::Int), including Memory's zero-length singleton and
native signed-to-size_t conversion before its negative/too-large checks.
The header callback below implements the concrete Core.new composition: it
calls only raw memoryrefnew and raw header allocation. The dimension list is
statically `(n,)` for this rank-one constructor, so the raw header receives n.
Source reference: base/boot.jl:821-824
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/boot.jl:821-824 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eval(Core, :(function (self::Type{Array{T,1}})(::UndefInitializer, m::Int) where {T}
--     mem = fieldtype(fieldtype(self, :ref), :mem)(undef, m)
--     return $(Expr(:new, :self, :(memoryref(mem)), :((m,))))
-- end))
-- /Source
def byteVectorUndef {World Vector Memory RootToken : Type}
    (runtime : ByteAllocationRuntime World Vector Memory RootToken)
    (n : I) : M World Vector :=
  runByteAllocation <|
    JuliaLean.base.array.arrayUndef1 (some byteAllocationLayout)
      (byteAllocationLift runtime.emptyMemory)
      (fun count => byteAllocationLift (runtime.allocateMemoryUnchecked count))
      (fun memory _dimensions => do
        let reference ← byteAllocationLift (runtime.memoryrefNew memory)
        byteAllocationLift (runtime.newVectorHeader reference n)) n

/-- The concrete UInt8/Csize_t specialization of Base.memset used by fill!.
The installed checked integer conversion supplies Cint; pointer and count are
already exactly the Cvoid pointer and Csize_t ABI types. The returned pointer
is retained here and is ignored only by the caller, as in Julia.

The existing `base.cmem.memset` is a pure ByteHeap wrapper whose CMemoryOps
argument carries MemcpyLaw, MemmoveLaw, MemsetLaw and MemcmpLaw proofs. That
interface cannot represent this adapter's arbitrary IO-world changes, errors
and divergence without adding C-library correctness assumptions. This is the
same concrete wrapper specialized to the existing effectful IO runtime, with
the raw C call left at its established boundary and no law assumed.
Source reference: base/cmem.jl:40-43
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/cmem.jl:40-43 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function memset(p::Ptr, val, n::Integer)
--     @_terminates_globally_meta
--     ccall(:memset, Ptr{Cvoid}, (Ptr{Cvoid}, Cint, Csize_t), p, val, n)
-- end
-- /Source
def byteMemset {World Vector Memory RootToken : Type}
    (runtime : ByteAllocationRuntime World Vector Memory RootToken)
    (pointer : Handle) (value : Byte) (count : U) : M World Handle := do
  let cvalue ← JuliaLean.base.io.liftJl
    (JInt.convert (IntTy.i32.name) .i32 value.val)
  runtime.memsetCall pointer cvalue count

/-- Fill the existing UInt8 vector in place, using the installed full fill!
body. Since the element is already UInt8, the source isa test selects its
identity branch. GC root operations and mutations occur at their source
positions; no cleanup is invented after an exception. Pointer conversion is
the installed GenericMemoryRef implementation, so offset and aliasing are
retained rather than delegated to a pointer callback.
Source reference: base/array.jl:473-480
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/array.jl:473-480 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function fill!(a::Union{Array{UInt8}, Array{Int8}}, x::Integer)
--     ref = a.ref
--     t = @_gc_preserve_begin ref
--     p = unsafe_convert(Ptr{Cvoid}, ref)
--     memset(p, x isa eltype(a) ? x : convert(eltype(a), x), length(a) % UInt)
--     @_gc_preserve_end t
--     return a
-- end
-- /Source
def byteFill {World Vector Memory RootToken : Type}
    (runtime : ByteAllocationRuntime World Vector Memory RootToken)
    (vector : Vector) (value : Byte) : M World Vector :=
  JuliaLean.base.array.fillBytes runtime.arrayRef runtime.preserveBegin
    (fun reference => pure (JuliaLean.base.pointer.unsafeConvertMemoryRefCvoid reference))
    (fun (_ : Byte) => true) id pure runtime.length
    (fun pointer byte count => do
      let _ ← byteMemset runtime pointer byte count
      pure ()) runtime.preserveEnd vector value

/-- zeros(UInt8,n::Int), through the generated typed varargs/tuple method.
The installed constant637 body allocates first, then computes zero(UInt8),
then fills the allocated vector and returns that same vector. The allocation
closure projects the statically known one-tuple `(n,)`; it is not an external
callee or an implementation supplied by the caller. All complete native Int
dimensions are accepted as inputs, including failures at the true Memory check.
Source reference: base/array.jl:631-653; base/number.jl:364
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/array.jl:631-653 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for (fname, felt) in ((:zeros, :zero), (:ones, :one))
--     @eval begin
--         $fname(dims::DimOrInd...) = $fname(dims)
--         $fname(::Type{T}, dims::DimOrInd...) where {T} = $fname(T, dims)
--         $fname(dims::Tuple{Vararg{DimOrInd}}) = $fname(Float64, dims)
--         $fname(::Type{T}, dims::NTuple{N, Union{Integer, OneTo}}) where {T,N} = $fname(T, map(to_dim, dims))
--         function $fname(::Type{T}, dims::NTuple{N, Integer}) where {T,N}
--             a = Array{T,N}(undef, dims)
--             fill!(a, $felt(T))
--             return a
--         end
--         function $fname(::Type{T}, dims::Tuple{}) where {T}
--             a = Array{T}(undef)
--             fill!(a, $felt(T))
--             return a
--         end
--         function $fname(::Type{T}, dims::NTuple{N, DimOrInd}) where {T,N}
--             a = similar(Array{T,N}, dims)
--             fill!(a, $felt(T))
--             return a
--         end
--     end
-- end
-- /Source
def byteZeros {World Vector Memory RootToken : Type}
    (runtime : ByteAllocationRuntime World Vector Memory RootToken)
    (n : I) : M World Vector :=
  JuliaLean.base.array.constant637
    (fun (_dimensions : List I) => byteVectorUndef runtime n)
    (JuliaLean.base.io.liftJl
      (JuliaLean.base.number.zeroType
        (fun (_ : Unit) n => JInt.convert (IntTy.u8.name) .u8 n) ()))
    (byteFill runtime) [n]

end JuliaLean.base.iostream.Models2Group18

namespace JuliaLean.base.iostream.Models2Group18

open JuliaLean
open JuliaLean.base.io (I M Error)

/-- The fixed generic function object registered by IOStream is Base.close.
Registering it does not execute close. 
Source context: base/iostream.jl:24-32. -/
-- Source: base/iostream.jl:24-32 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function IOStream(name::AbstractString, finalize::Bool)
--     buf = zeros(UInt8,sizeof_ios_t)
--     x = IOStream(name, buf)
--     if finalize
--         finalizer(close, x)
--     end
--     return x
-- end
-- IOStream(name::AbstractString) = IOStream(name, true)
-- /Source
inductive CloseFunction where
  | close
  deriving DecidableEq

/-- The constructor call dispatches on the unspecified AbstractString subtype.
The selected method may return any Julia value, fail, mutate state, or diverge.
Its result is deliberately not restricted to an IOStream handle. 
Source context: base/iostream.jl:24-32. -/
-- Source: base/iostream.jl:24-32 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function IOStream(name::AbstractString, finalize::Bool)
--     buf = zeros(UInt8,sizeof_ios_t)
--     x = IOStream(name, buf)
--     if finalize
--         finalizer(close, x)
--     end
--     return x
-- end
-- IOStream(name::AbstractString) = IOStream(name, true)
-- /Source
structure ConstructorOps (World Name Vector Result : Type) where
  withBuffer : Name → Vector → M World Result

/-- Dispatch at base/iostream.jl:28 also depends on the value returned by the
open name/buffer constructor. The Base fallback runs the installed finalizer
body; a genuinely selected custom method may have any result type or effects.
The package's higher universe permits arbitrary runtime representation types
and custom return types without requiring them all to be the same type.
This selection does not execute the finalizer or assert its correctness. -/
-- Source: base/iostream.jl:28-28 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         finalizer(close, x)
-- /Source
inductive FinalizerSelection (World Result : Type) : Type 1 where
  | base {ThreadState Pointer Task Order : Type}
      (runtime : JuliaLean.base.gcutils.GcOps (M World) Result CloseFunction
        ThreadState Pointer Task Order Error)
  | custom {Returned : Type}
      (invoke : CloseFunction → Result → M World Returned)

/-- Perform the selected finalizer call at base/iostream.jl:28, ignoring only
its returned value. In the Base branch, the installed mutability check and
Core.finalizer registration remain concrete. The custom branch is solely the
method selected by dispatch on the unfixed result type. Exceptions, mutations,
and divergence from either branch remain observable in the surrounding IO
monad. The function argument remains the fixed Base.close object.
Base fallback source: base/gcutils.jl:87-91. -/
-- Source: base/gcutils.jl:87-91 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function finalizer(@nospecialize(f), @nospecialize(o))
--     _check_mutable(o)
--     Core.finalizer(f, o)
--     return o
-- end
-- /Source
def runSelectedFinalizer {World Result : Type}
    (selection : FinalizerSelection World Result) (function : CloseFunction)
    (result : Result) : M World Unit :=
  match selection with
  | .base gc => do
      let _ ← JuliaLean.base.gcutils.finalizer
        { gc with errorException := Error.errorException } function result
      pure ()
  | .custom invoke => do
      let _ ← invoke function result
      pure ()

/-- The name/finalize constructor closes its fixed UInt8 allocation dependency
and the installed Base finalizer fallback. Constructor dispatch on Name and
finalizer dispatch on its unrestricted returned value remain explicit.
`finalizerFor` selects on the actual result, including constructors whose
different calls return different Julia types; selection itself has no effects.
The source constant sizeof_ios_t is passed as its already-initialized native
Int value; it is not recomputed per call.
Source reference: `base/iostream.jl:24-31`. -/
-- Source: base/iostream.jl:24-31 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function IOStream(name::AbstractString, finalize::Bool)
--     buf = zeros(UInt8,sizeof_ios_t)
--     x = IOStream(name, buf)
--     if finalize
--         finalizer(close, x)
--     end
--     return x
-- end
-- /Source
def newStreamFinalized
    {World Name Vector Memory RootToken Result : Type}
    (bytes : ByteAllocationRuntime World Vector Memory RootToken)
    (ops : ConstructorOps World Name Vector Result)
    (finalizerFor : Result → FinalizerSelection World Result)
    (sizeofIos : I) (name : Name) (finalize : Bool) : M World Result := do
  let buffer ← byteZeros bytes sizeofIos
  let result ← ops.withBuffer name buffer
  if finalize then
    runSelectedFinalizer (finalizerFor result) CloseFunction.close result
  pure result

end JuliaLean.base.iostream.Models2Group18

namespace JuliaLean.base.iostream.Models2Group18

open JuliaLean
open JuliaLean.base.io (M Error I U Byte)
/-- The complete stream conversion uses the current backing vector, including
its current reference after resize, and the installed pointer bit conversion.
It does not read the cached `handle` field. Julia source: `base/iostream.jl:34`. -/
-- Source: base/iostream.jl:34-34 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unsafe_convert(T::Type{Ptr{Cvoid}}, s::IOStream) = convert(T, pointer(s.ios))
-- /Source
def unsafeConvert {World Stream Vector Lock : Type}
    (access : Access World Stream Vector Lock) (vectors : VectorRefOps World Vector)
    (stream : Stream) : M World Handle := do
  let pointer ← vectorPointer vectors (← access.get stream).ios
  pure (JuliaLean.base.pointer.convertPtrType pointer)

/-- The selected `print` method is open dispatch on the unspecified IO subtype;
its result, errors and state changes are forwarded without a Unit restriction.
Source reference: `base/iostream.jl:35`. -/
-- Source: base/iostream.jl:35-35 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- show(io::IO, s::IOStream) = print(io, "IOStream(", s.name, ")")
-- /Source
structure DisplayOps (World Out Result : Type) where
  print : Out → Text → Text → Text → M World Result

/-- Show an IOStream through the selected custom IO printing method.
Source reference: `base/iostream.jl:35`. -/
-- Source: base/iostream.jl:35-35 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- show(io::IO, s::IOStream) = print(io, "IOStream(", s.name, ")")
-- /Source
def showStream {World Stream Vector Lock Out Result : Type}
    (access : Access World Stream Vector Lock) (ops : DisplayOps World Out Result)
    (out : Out) (stream : Stream) : M World Result := do
  ops.print out (text "IOStream(") (← access.get stream).name (text ")")



end JuliaLean.base.iostream.Models2Group18

namespace JuliaLean.base.iostream.Models2Group18

open JuliaLean
open JuliaLean.base.essentials.Models1Group18

/-- Non-Expr syntax values used by the quotation at base/iostream.jl:39-46.
`original` retains arbitrary original Julia objects and their identities. The
other two constructors represent only the immutable values introduced by this
quotation: QuoteNode(Symbol) and LineNumberNode(Int, Union{Symbol,Nothing}).
Expr objects themselves use the installed SyntaxValue.exprRef representation,
so input cycles, sharing, undefined args slots, and mutation through aliases are
not converted into trees. See base/boot.jl:128-137,702,710-714 and
doc/src/devdocs/ast.md (Quotes and Line numbers). -/
-- Source: base/iostream.jl:39-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     quote
--         l = ($s)._dolock
--         temp = ($s).lock
--         l && lock(temp)
--         val = $(esc(expr))
--         l && unlock(temp)
--         val
--     end
-- /Source
inductive LockMacroAtom (Atom : Type) where
  | original (value : Atom)
  | quotedSymbol (name : String)
  | lineNumber (line : JInt .i64) (file : Option String)

/-- The source macro at base/iostream.jl:37-47, before Julia's standard hygiene
pass. `definitionFile` is the definition's source filename, represented as its
interned Symbol name (or nothing); it is not the macro call site's filename.
The two property reads share the *same* freshly allocated escape Expr. Both
escape payloads are the original syntax values, with no read, traversal, copy,
or evaluation of either input. All quotation Expr nodes are explicitly built
using the installed shallow syntaxExpr allocator. In particular no try/finally
node is added: the generated program follows the source's ordinary unlock.

The fixed esc body at base/essentials.jl:903 is Expr(:escape,e). Its pure JVal
model cannot retain Expr identity; this representation adapter uses the same
installed heap allocator as essentials.Models1Group18.labelHeap. Allocation,
including the fresh Expr.args vector, follows that existing logical primitive
boundary: it can allocate without resource exhaustion or GC observations. No
new runtime callback, callee-correctness premise, or error convention is added.
All allocation effects remain in the installed SyntaxM monad. -/
-- Source: base/iostream.jl:37-47 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro _lock_ios(s, expr)
--     s = esc(s)
--     quote
--         l = ($s)._dolock
--         temp = ($s).lock
--         l && lock(temp)
--         val = $(esc(expr))
--         l && unlock(temp)
--         val
--     end
-- end
-- /Source
def lockIosMacro {Atom : Type} (definitionFile : Option String)
    (stream expression : SyntaxValue (LockMacroAtom Atom)) :
    SyntaxM (LockMacroAtom Atom) (SyntaxValue (LockMacroAtom Atom)) := do
  let escapedStream ← syntaxExpr "escape" [stream]
  let flagRead ← syntaxExpr "." [escapedStream, .atom (.quotedSymbol "_dolock")]
  let flagAssignment ← syntaxExpr "=" [.symbol "l", flagRead]
  let mutexRead ← syntaxExpr "." [escapedStream, .atom (.quotedSymbol "lock")]
  let mutexAssignment ← syntaxExpr "=" [.symbol "temp", mutexRead]
  let lockCall ← syntaxExpr "call" [.symbol "lock", .symbol "temp"]
  let lockGuard ← syntaxExpr "&&" [.symbol "l", lockCall]
  let escapedExpression ← syntaxExpr "escape" [expression]
  let valueAssignment ← syntaxExpr "=" [.symbol "val", escapedExpression]
  let unlockCall ← syntaxExpr "call" [.symbol "unlock", .symbol "temp"]
  let unlockGuard ← syntaxExpr "&&" [.symbol "l", unlockCall]
  syntaxExpr "block" [
    .atom (.lineNumber (JInt.wrap .i64 40) definitionFile), flagAssignment,
    .atom (.lineNumber (JInt.wrap .i64 41) definitionFile), mutexAssignment,
    .atom (.lineNumber (JInt.wrap .i64 42) definitionFile), lockGuard,
    .atom (.lineNumber (JInt.wrap .i64 43) definitionFile), valueAssignment,
    .atom (.lineNumber (JInt.wrap .i64 44) definitionFile), unlockGuard,
    .atom (.lineNumber (JInt.wrap .i64 45) definitionFile), .symbol "val"]

end JuliaLean.base.iostream.Models2Group18

namespace JuliaLean.base.iostream.Models2Group18

open JuliaLean
open JuliaLean.base.io (M Error I)

/-- Close the concrete RawFD conversion in the installed IOStream method.
All Clong bit patterns are accepted at the foreign boundary; the installed
constructor performs checked Cint narrowing, including InexactError.
Source reference: `base/iostream.jl:74`; dependency `base/libc.jl:35`. -/
-- Source: base/iostream.jl:74-74 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- fd(s::IOStream) = RawFD(ccall(:jl_ios_fd, Clong, (Ptr{Cvoid},), s.ios))
-- /Source
def fd {World Stream Vector Lock : Type}
    (access : Access World Stream Vector Lock) (vectors : VectorRefOps World Vector)
    (runtime : Runtime World Vector)
    (stream : Stream) : M World JuliaLean.base.libc.RawFD :=
  JuliaLean.base.iostream.fd access (withVectorPointers vectors runtime)
    (fun value => JuliaLean.base.libc.rawFDOfInteger value.val) stream


end JuliaLean.base.iostream.Models2Group18

namespace JuliaLean.base.iostream.Models2Group18

open JuliaLean.base.io (M)

/-- Reuse the installed query with concrete current-vector pointer conversion.
Source reference: `base/iostream.jl:88`. The C operation remains the installed
typed foreign boundary, and its state/error effects are retained. -/
-- Source: base/iostream.jl:88-88 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isopen(s::IOStream) = ccall(:ios_isopen, Cint, (Ptr{Cvoid},), s.ios) != 0
-- /Source
def isopen {World Stream Vector Lock : Type}
    (access : Access World Stream Vector Lock) (vectors : VectorRefOps World Vector)
    (runtime : Runtime World Vector) (stream : Stream) : M World Bool :=
  JuliaLean.base.iostream.isopen access (withVectorPointers vectors runtime) stream

/-- Reuse the installed capability query, including its isopen call and
short circuit. Julia source: `base/iostream.jl:104`. -/
-- Source: base/iostream.jl:104-104 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- iswritable(s::IOStream) = isopen(s) && ccall(:ios_get_writable, Cint, (Ptr{Cvoid},), s.ios)!=0
-- /Source
def iswritable {World Stream Vector Lock : Type}
    (access : Access World Stream Vector Lock) (vectors : VectorRefOps World Vector)
    (runtime : Runtime World Vector) (stream : Stream) : M World Bool :=
  JuliaLean.base.iostream.iswritable access (withVectorPointers vectors runtime) stream

/-- Reuse the installed capability query, including its isopen call and
short circuit. Julia source: `base/iostream.jl:106`. -/
-- Source: base/iostream.jl:106-106 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isreadable(s::IOStream) = isopen(s) && ccall(:ios_get_readable, Cint, (Ptr{Cvoid},), s.ios)!=0
-- /Source
def isreadable {World Stream Vector Lock : Type}
    (access : Access World Stream Vector Lock) (vectors : VectorRefOps World Vector)
    (runtime : Runtime World Vector) (stream : Stream) : M World Bool :=
  JuliaLean.base.iostream.isreadable access (withVectorPointers vectors runtime) stream

end JuliaLean.base.iostream.Models2Group18

namespace JuliaLean.base.iostream.Models2Group18

open JuliaLean
open JuliaLean.base.io (M Error)

/-- The constructor-only runtime needed by IOStream's inner constructor.
Task, queue, SpinLock and entry types represent concrete runtime identities;
they are not Julia dispatch parameters. `allocateQueue` is Core.new with
explicit head and tail fields. The installed SpinLock constructor receives
its raw allocator from `spin.newSpinLock`.

Only `primitive.allocate`, `primitive.task.condition.newIdentity`, and
`spin.newSpinLock` can be reached by the constructor assembled below. All
other fields in those pre-existing compatibility records are unused. In
particular this package supplies no model of lock acquisition or release.
This narrow adapter avoids importing cancellation, park, task-queue or
scheduler-cache additions that construction never invokes.
Source reference: base/lock.jl:3,85; base/condition.jl:79;
base/linked_list.jl:7; base/locks-mt.jl:46. -/
-- Source: base/lock.jl:3-3 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- const ThreadSynchronizer = GenericCondition{Threads.SpinLock}
-- /Source
-- Source: base/lock.jl:85-85 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     ReentrantLock() = new(nothing, 0x0000_0000, 0x00, ThreadSynchronizer())
-- /Source
-- Source: base/condition.jl:74-79 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mutable struct GenericCondition{L<:AbstractLock}
--     # mutable for identity only
--     const waitq::IntrusiveLinkedList{WaitEntry}
--     const lock::L
-- 
--     GenericCondition{L}() where {L<:AbstractLock} = new{L}(IntrusiveLinkedList{WaitEntry}(), L())
-- /Source
-- Source: base/linked_list.jl:3-7 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mutable struct IntrusiveLinkedList{T}
--     # Invasive list requires that T have a field `.next >: U{T, Nothing}` and `.queue::Any`
--     head::Union{T, Nothing}
--     tail::Union{T, Nothing}
--     IntrusiveLinkedList{T}() where {T} = new{T}(nothing, nothing)
-- /Source
-- Source: base/locks-mt.jl:44-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mutable struct SpinLock <: AbstractSpinLock
--     @atomic owned::Int
--     SpinLock() = new(0)
-- /Source
structure ReentrantRuntime (World ReentrantLock : Type) where
  Task : Type
  Queue : Type
  SpinLock : Type
  Entry : Type
  Slot : Type
  Source : Type
  Token : Type
  LockState : Type
  Value : Type
  primitive : JuliaLean.base.lock.Runtime Error World ReentrantLock Task Queue
    SpinLock Entry Slot Source Token LockState Value
  allocateQueue : Option Entry → Option Entry → M World Queue
  spin : JuliaLean.base.locks_mt.Runtime Error World SpinLock

/-- Close every concrete constructor reached by the installed ReentrantLock
constructor: allocate an empty intrusive queue, execute the installed
SpinLock constructor, allocate the GenericCondition identity, then allocate
the outer ReentrantLock. The installed `newGenericCondition` and
`newReentrantLock` bodies retain this order and the complete exception world.
The linked-list model has a separate closed heap, so its one-line Core.new
constructor is adapted here to the caller's mutable world with both actual
initial field arguments. No list operation is called by this constructor.
The unused compatibility runtime slots remain arbitrary and unobserved.
Source reference: base/lock.jl:85; base/condition.jl:79;
base/linked_list.jl:7; base/locks-mt.jl:46. -/
-- Source: base/lock.jl:3-3 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- const ThreadSynchronizer = GenericCondition{Threads.SpinLock}
-- /Source
-- Source: base/lock.jl:85-85 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     ReentrantLock() = new(nothing, 0x0000_0000, 0x00, ThreadSynchronizer())
-- /Source
-- Source: base/condition.jl:74-79 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mutable struct GenericCondition{L<:AbstractLock}
--     # mutable for identity only
--     const waitq::IntrusiveLinkedList{WaitEntry}
--     const lock::L
-- 
--     GenericCondition{L}() where {L<:AbstractLock} = new{L}(IntrusiveLinkedList{WaitEntry}(), L())
-- /Source
-- Source: base/linked_list.jl:3-7 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mutable struct IntrusiveLinkedList{T}
--     # Invasive list requires that T have a field `.next >: U{T, Nothing}` and `.queue::Any`
--     head::Union{T, Nothing}
--     tail::Union{T, Nothing}
--     IntrusiveLinkedList{T}() where {T} = new{T}(nothing, nothing)
-- /Source
-- Source: base/locks-mt.jl:44-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mutable struct SpinLock <: AbstractSpinLock
--     @atomic owned::Int
--     SpinLock() = new(0)
-- /Source
def concreteReentrantRuntime {World Lock : Type} (runtime : ReentrantRuntime World Lock) :
    JuliaLean.base.lock.Runtime Error World Lock runtime.Task runtime.Queue
      runtime.SpinLock runtime.Entry runtime.Slot runtime.Source runtime.Token
      runtime.LockState runtime.Value :=
  { runtime.primitive with
    task := { runtime.primitive.task with
      condition := { runtime.primitive.task.condition with
        newQueue := runtime.allocateQueue none none
        newLock := JuliaLean.base.locks_mt.SpinLock runtime.spin } } }

end JuliaLean.base.iostream.Models2Group18

namespace JuliaLean.base.iostream.Models2Group18

open JuliaLean
open JuliaLean.base.io (M Error I U)

/-- seek is selected on the unspecified IO subtype. Its result need not have
the same type as the stream, and its full effects/errors remain observable. 
Source context: base/iostream.jl:185-185. -/
-- Source: base/iostream.jl:185-185 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- seekstart(s::IO) = seek(s,0)
-- /Source
structure SeekOps (World Stream Result : Type) where
  seek : Stream → I → M World Result

/-- Generic IO seekstart preserving arbitrary selected seek results.
Source reference: `base/iostream.jl:185`. -/
-- Source: base/iostream.jl:185-185 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- seekstart(s::IO) = seek(s,0)
-- /Source
def seekstart {World Stream Result : Type} (ops : SeekOps World Stream Result)
    (stream : Stream) : M World Result :=
  ops.seek stream (JuliaLean.base.io.i 0)


end JuliaLean.base.iostream.Models2Group18

namespace JuliaLean.base.iostream.Models2Group18

open JuliaLean
open JuliaLean.base.io (M CancelArg)

/-- The installed no-lock EOF body with its concrete Vector{UInt8} pointer
conversion closed. The remaining eof operation is the typed C boundary, not
an implementation supplied for this Julia method.
Source reference: base/iostream.jl:262
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/iostream.jl:262-262 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _eof_nolock(s::IOStream) = ccall(:ios_eof_blocking, Cint, (Ptr{Cvoid},), s.ios) != 0
-- /Source
def eofNolock {World Stream Vector Lock : Type}
    (access : Access World Stream Vector Lock) (vectors : VectorRefOps World Vector)
    (runtime : Runtime World Vector) (stream : Stream) : M World Bool :=
  JuliaLean.base.iostream.eofNolock access (withVectorPointers vectors runtime) stream


end JuliaLean.base.iostream.Models2Group18

namespace JuliaLean.base.iostream.Models2Group18

open JuliaLean
open JuliaLean.base.io (M I U Error)

/-- The four converted values that the foreign-call lowering preserves.
They retain each selected conversion's result, including custom temporary
objects. Julia source: base/iostream.jl:283-284; manual
`calling-c-and-fortran-code.md:248-275`; cached primary compiler source
src/julia-syntax.scm:1069-1106. The compiler emits its root list in reverse
argument order and explicitly says that GC-root ordering is arbitrary. -/
-- Source: base/iostream.jl:283-284 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     ccall(:ios_fd, Ptr{Cvoid}, (Ptr{Cvoid}, Clong, Cint, Cint),
--           s.ios, fd, 0, own)
-- /Source
inductive FdioCallRoot (PointerRoot LongRoot : Type) where
  | pointer (root : PointerRoot)
  | descriptor (root : LongRoot)
  | flag (root : CInt)

/-- Existing compiler root-preservation runtime, packaged without imposing
laws on its effects, exceptions or divergence. No Julia fdio, conversion or
constructor body is supplied here. Julia source: base/iostream.jl:283-284;
base/gcutils.jl:237-243 and manual calling-c-and-fortran-code.md:248-275. -/
-- Source: base/iostream.jl:283-284 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     ccall(:ios_fd, Ptr{Cvoid}, (Ptr{Cvoid}, Clong, Cint, Cint),
--           s.ios, fd, 0, own)
-- /Source
structure FdioPreservationRuntime (World PointerRoot LongRoot : Type) where
  Finalizer : Type
  ThreadState : Type
  Pointer : Type
  Task : Type
  MemoryOrder : Type
  primitive : JuliaLean.base.gcutils.GcOps (M World) (FdioCallRoot PointerRoot LongRoot)
    Finalizer ThreadState Pointer Task MemoryOrder Error

/-- Open dispatch selected by the arbitrary AbstractString constructor result,
its :ios property, and the arbitrary Integer subtype. cconvert may return an
object of any type; unsafe_convert records actual runtime type membership and
can fail the explicit ABI assertion. None of these fields replaces fdio's body.
The result carrier can include values of different Julia types; it is not
restricted to IOStream. Julia source: base/iostream.jl:281-286 and manual
calling-c-and-fortran-code.md:248-275. -/
-- Source: base/iostream.jl:281-286 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function fdio(name::AbstractString, fd::Integer, own::Bool=false)
--     s = IOStream(name)
--     ccall(:ios_fd, Ptr{Cvoid}, (Ptr{Cvoid}, Clong, Cint, Cint),
--           s.ios, fd, 0, own)
--     return s
-- end
-- /Source
structure FdioNamedOps (World Name Descriptor Result : Type) where
  IosArgument : Type
  PointerRoot : Type
  LongRoot : Type
  NotPointer : Type
  NotLong : Type
  construct : Name → M World Result
  getproperty : Result → JuliaLean.base.io.SymbolName → M World IosArgument
  cconvertPointer : IosArgument → M World PointerRoot
  cconvertLong : Descriptor → M World LongRoot
  unsafePointer : PointerRoot → M World
    (JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Handle NotPointer)
  unsafeLong : LongRoot → M World
    (JuliaLean.base.abstractarray.Models1Group1.TypeAssertion I NotLong)
  preservation : FdioPreservationRuntime World PointerRoot LongRoot

/-- Exception-representation bridge for the installed type-assertion primitive.
The primitive can produce only the TypeError case, while the total bridge
retains the class and all available payloads of every baseline ArrayError.
Source reference: base/abstractarray.jl:17-18; manual
calling-c-and-fortran-code.md:259-265 (foreign-call argument conversion). -/
-- Source: base/abstractarray.jl:17-18 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- convert(::Type{AbstractArray{T}}, a::AbstractArray) where {T} = AbstractArray{T}(a)::AbstractArray{T}
-- convert(::Type{AbstractArray{T,N}}, a::AbstractArray{<:Any,N}) where {T,N} = AbstractArray{T,N}(a)::AbstractArray{T,N}
-- /Source
def fdioAssertionError : JuliaLean.base.abstractarray.ArrayError → Error
  | .julia error => .jl error
  | .dimensionMismatch message => .foreignError "DimensionMismatch" message
  | .canonicalIndex functionName typeName =>
      .foreignError "CanonicalIndexError" (reprStr (functionName, typeName))
  | .errorException message => .errorException message
  | .assertionError message => .foreignError "AssertionError" message
  | .showError error => .showError error

/-- Call the installed type-assertion primitive at the foreign-call ABI
boundary, after every unsafe_convert argument expression has been evaluated.
TypeError retains the world at that precise point. Julia source:
base/abstractarray.jl:17-18; manual calling-c-and-fortran-code.md:259-265;
cached primary src/julia-syntax.scm:1069-1106,4861-4897,4973-4982. -/
-- Source: base/abstractarray.jl:17-18 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- convert(::Type{AbstractArray{T}}, a::AbstractArray) where {T} = AbstractArray{T}(a)::AbstractArray{T}
-- convert(::Type{AbstractArray{T,N}}, a::AbstractArray{<:Any,N}) where {T,N} = AbstractArray{T,N}(a)::AbstractArray{T,N}
-- /Source
def fdioAssertABI {World Expected Other : Type}
    (observed : JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Expected Other) :
    M World Expected :=
  match (JuliaLean.base.abstractarray.Models1Group1.assertType observed :
      Except JuliaLean.base.abstractarray.ArrayError Expected) with
  | .ok value => pure value
  | .error error => throw (fdioAssertionError error)

/-- Full named fdio body over arbitrary constructor results and Integer types.
Each argument expression is evaluated immediately before its cconvert stage;
all four cconvert stages precede preservation and unsafe_convert. All unsafe
conversions are evaluated before ABI validation at the foreign call. Only :ios
has a nontrivial argument expression. Fixed Cint zero/Bool conversions use
installed concrete integer models. The ios_fd parameter is precisely the typed C primitive.
No lock, validation of its return pointer, or forced IOStream return is added.
Staging follows manual calling-c-and-fortran-code.md:248-265 and cached primary
src/julia-syntax.scm:1069-1106,4861-4897,4973-4982. The source cache provenance
and its exact digest are recorded in Fdio-NOTES.md.
Source reference: base/iostream.jl:281-286
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/iostream.jl:281-286 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function fdio(name::AbstractString, fd::Integer, own::Bool=false)
--     s = IOStream(name)
--     ccall(:ios_fd, Ptr{Cvoid}, (Ptr{Cvoid}, Clong, Cint, Cint),
--           s.ios, fd, 0, own)
--     return s
-- end
-- /Source
def fdioNamed {World Name Descriptor Result : Type}
    (ops : FdioNamedOps World Name Descriptor Result)
    (iosFd : Handle → I → CInt → CInt → M World Handle)
    (name : Name) (descriptor : Descriptor) (own : Bool := false) : M World Result := do
  let stream ← ops.construct name
  let ios ← ops.getproperty stream ⟨"ios"⟩
  let pointerRoot ← ops.cconvertPointer ios
  let longRoot ← ops.cconvertLong descriptor
  let zero ← JuliaLean.base.io.liftJl (JInt.convert (IntTy.i32.name) .i32 0)
  let ownership := JuliaLean.base.int.ofBool .i32 own
  let _ ← JuliaLean.base.gcutils.withPreservedRoots ops.preservation.primitive
    [.flag ownership, .flag zero, .descriptor longRoot, .pointer pointerRoot] do
      let observedPointer ← ops.unsafePointer pointerRoot
      let observedLong ← ops.unsafeLong longRoot
      let convertedZero := JuliaLean.base.essentials.unsafeConvertIdentity zero
      let convertedOwnership := JuliaLean.base.essentials.unsafeConvertIdentity ownership
      let pointer ← fdioAssertABI observedPointer
      let fd ← fdioAssertABI observedLong
      iosFd pointer fd convertedZero convertedOwnership
  pure stream

/-- Both selected targets are open: generic Integer string formatting may
return an arbitrary object, and the subsequent fdio dispatch is selected on
that actual result. The original descriptor and own flag remain separate
arguments. Julia source: base/iostream.jl:287. -/
-- Source: base/iostream.jl:287-287 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- fdio(fd::Integer, own::Bool=false) = fdio(string("<fd ",fd,">"), fd, own)
-- /Source
structure FdioDefaultOps (World Descriptor Name Result : Type) where
  string : Text → Descriptor → Text → M World Name
  fdio : Name → Descriptor → Bool → M World Result

/-- Evaluate the complete three-argument string call, then dispatch fdio on
its actual result. Neither a built-in String nor an IOStream result is assumed.
Source reference: base/iostream.jl:287
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/iostream.jl:287-287 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- fdio(fd::Integer, own::Bool=false) = fdio(string("<fd ",fd,">"), fd, own)
-- /Source
def fdio {World Descriptor Name Result : Type}
    (ops : FdioDefaultOps World Descriptor Name Result)
    (descriptor : Descriptor) (own : Bool := false) : M World Result := do
  let name ← ops.string (text "<fd ") descriptor (text ">")
  ops.fdio name descriptor own

end JuliaLean.base.iostream.Models2Group18

namespace JuliaLean.base.iostream.Models2Group18

open JuliaLean
open JuliaLean.base.io (M Error)

/-- An ordered keyword call preserves both keyword presence and NamedTuple
order for a selected custom open method. Native Bool values are distinguished
from arbitrary other lock values; the untyped keyword does not impose a Bool
restriction. The source constructs at most three entries, all machine-sized.
Source reference: base/iostream.jl:399-405. -/
-- Source: base/iostream.jl:399-405 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function open(fname::AbstractString, mode::AbstractString; lock = true)
--     mode == "r"  ? open(fname, lock = lock, read = true)                  :
--     mode == "r+" ? open(fname, lock = lock, read = true, write = true)    :
--     mode == "w"  ? open(fname, lock = lock, truncate = true)              :
--     mode == "w+" ? open(fname, lock = lock, truncate = true, read = true) :
--     mode == "a"  ? open(fname, lock = lock, append = true)                :
--     mode == "a+" ? open(fname, lock = lock, append = true, read = true)   :
-- /Source
abbrev OpenModeKeywordList (OtherLock : Type) := List (String × (Bool ⊕ OtherLock))

/-- Calls whose selected method depends on a type not fixed by the mode-open
method. `equals` retains non-Bool results. `openFile` receives the exact ordered
keyword tuple and may return any value. Interpolation calls string(prefix,mode)
and may itself be specialized; its unrestricted result selects ArgumentError's
constructor. `argumentError` returns the existing thrown-value representation
of that constructor's result. The caller performs throw separately, so a
constructor exception and the outer throw have their correct distinct points.
None of these dispatch operations has a supplied correctness law.
Source reference: base/iostream.jl:399-407. -/
-- Source: base/iostream.jl:399-407 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function open(fname::AbstractString, mode::AbstractString; lock = true)
--     mode == "r"  ? open(fname, lock = lock, read = true)                  :
--     mode == "r+" ? open(fname, lock = lock, read = true, write = true)    :
--     mode == "w"  ? open(fname, lock = lock, truncate = true)              :
--     mode == "w+" ? open(fname, lock = lock, truncate = true, read = true) :
--     mode == "a"  ? open(fname, lock = lock, append = true)                :
--     mode == "a+" ? open(fname, lock = lock, append = true, read = true)   :
--     throw(ArgumentError("invalid open mode: $mode"))
-- end
-- /Source
structure OpenModeOps (World Name Mode OtherLock NotBool Message Result : Type) where
  equals : Mode → Text → M World (Bool ⊕ NotBool)
  openFile : Name → OpenModeKeywordList OtherLock → M World Result
  interpolate : Text → Mode → M World Message
  argumentError : Message → M World Error

/-- A Julia ternary condition accepts only Bool. Reuse the installed assertion
over Bool plus arbitrary non-Bool values, retaining its class-only TypeError
representation and throwing in the existing state-preserving IO monad.
Source reference: base/iostream.jl:400-405. -/
-- Source: base/iostream.jl:400-405 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     mode == "r"  ? open(fname, lock = lock, read = true)                  :
--     mode == "r+" ? open(fname, lock = lock, read = true, write = true)    :
--     mode == "w"  ? open(fname, lock = lock, truncate = true)              :
--     mode == "w+" ? open(fname, lock = lock, truncate = true, read = true) :
--     mode == "a"  ? open(fname, lock = lock, append = true)                :
--     mode == "a+" ? open(fname, lock = lock, append = true, read = true)   :
-- /Source
def openModeCondition {World NotBool : Type} (value : Bool ⊕ NotBool) : M World Bool :=
  match JuliaLean.base.reduce.assertBool value with
  | .ok value => pure value
  | .error .typeError => throw (.foreignError "TypeError" "")

/-- Mode-open for the full AbstractString domain, including custom equality,
interpolation, filename-selected opening and arbitrary lock keyword values.
The six tests occur in source order and short-circuit at the first true result.
Keyword order is observable by custom methods, so w+ and a+ keep read after
truncate/append instead of canonicalizing to a fixed-order flag record.
No mode, name or lock value is coerced, and the selected open result is returned
unchanged. The default keyword is the actual Bool true, represented explicitly.
Source reference: base/iostream.jl:399-407. -/
-- Source: base/iostream.jl:399-407 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function open(fname::AbstractString, mode::AbstractString; lock = true)
--     mode == "r"  ? open(fname, lock = lock, read = true)                  :
--     mode == "r+" ? open(fname, lock = lock, read = true, write = true)    :
--     mode == "w"  ? open(fname, lock = lock, truncate = true)              :
--     mode == "w+" ? open(fname, lock = lock, truncate = true, read = true) :
--     mode == "a"  ? open(fname, lock = lock, append = true)                :
--     mode == "a+" ? open(fname, lock = lock, append = true, read = true)   :
--     throw(ArgumentError("invalid open mode: $mode"))
-- end
-- /Source
def openMode {World Name Mode OtherLock NotBool Message Result : Type}
    (ops : OpenModeOps World Name Mode OtherLock NotBool Message Result)
    (name : Name) (mode : Mode) (lock : Bool ⊕ OtherLock := .inl true) : M World Result := do
  if ← openModeCondition (← ops.equals mode (text "r")) then
    return ← ops.openFile name [("lock", lock), ("read", .inl true)]
  if ← openModeCondition (← ops.equals mode (text "r+")) then
    return ← ops.openFile name [("lock", lock), ("read", .inl true), ("write", .inl true)]
  if ← openModeCondition (← ops.equals mode (text "w")) then
    return ← ops.openFile name [("lock", lock), ("truncate", .inl true)]
  if ← openModeCondition (← ops.equals mode (text "w+")) then
    return ← ops.openFile name [("lock", lock), ("truncate", .inl true), ("read", .inl true)]
  if ← openModeCondition (← ops.equals mode (text "a")) then
    return ← ops.openFile name [("lock", lock), ("append", .inl true)]
  if ← openModeCondition (← ops.equals mode (text "a+")) then
    return ← ops.openFile name [("lock", lock), ("append", .inl true), ("read", .inl true)]
  let message ← ops.interpolate (text "invalid open mode: ") mode
  throw (← ops.argumentError message)

end JuliaLean.base.iostream.Models2Group18

namespace JuliaLean.base.iostream.Models2Group18

open JuliaLean
open JuliaLean.base.io (M Error)
open JuliaLean.base.abstractarray.Models1Group1 (TypeAssertion)

/-- The selected `convert(String, name)` call on a non-String AbstractString
at `base/iostream.jl:21`. `Name` carries every non-String subtype admitted by
the method; `NotString` carries every possible result outside String. The
runtime type tag is representation data, not a law imposed on conversion.
An already-String input uses the other arm of the constructor's argument sum
and never calls this operation. Conversion may mutate, throw, or diverge.
-/
-- Source: base/iostream.jl:13-22 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mutable struct IOStream <: IO
--     handle::Ptr{Cvoid}
--     ios::Vector{UInt8}
--     name::String
--     mark::Int64
--     lock::ReentrantLock
--     _dolock::Bool
-- 
--     IOStream(name::AbstractString, buf::Vector{UInt8}) = new(pointer(buf), buf, name, -1, ReentrantLock(), true)
-- end
-- /Source
structure InnerNameOps (World Name NotString : Type) where
  convertString : Name → M World (TypeAssertion JuliaLean.Strings.JStr NotString)

/-- The complete inner IOStream constructor at `base/iostream.jl:21`.
The input sum records the actual Core `isa String` result: its left arm is a
String and its right arm is any other AbstractString. String bytes need not
form valid UTF-8. The supplied buffer is retained by identity.

Each field expression and its implicit conversion executes from left to
right. Thus name conversion precedes ReentrantLock construction. A conversion
that returns a non-String value is not rejected until final `new`, after the
lock expression has run. The cached primary compiler source establishes this
through `new-call` (src/julia-syntax.scm:795-806,826-830),
`convert-for-type-decl` with assert=false (3870-3893), and `compile-args`
(4872-4897). The final field check is src/datatype.c:1707-1723. Provenance and
the cached files' hashes are recorded in the accompanying notes.

The raw allocation and rejected-name exception use explicit result-carrier
adapters after all field expressions have run. Pointer conversion and
ReentrantLock construction call the installed models.
-/
-- Source: base/iostream.jl:21-21 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     IOStream(name::AbstractString, buf::Vector{UInt8}) = new(pointer(buf), buf, name, -1, ReentrantLock(), true)
-- /Source
def sourceNewStreamWithBuffer {World Name NotString Vector Lock Result : Type}
    (vectors : VectorRefOps World Vector)
    (locks : ReentrantRuntime World Lock)
    (names : InnerNameOps World Name NotString)
    (allocate : Fields Vector Lock → M World Result)
    (rejectName : NotString → M World Result)
    (name : JuliaLean.Strings.JStr ⊕ Name) (buffer : Vector) : M World Result := do
  let handle : Handle := JuliaLean.base.pointer.convertPtrType (← vectorPointer vectors buffer)
  let converted ← match name with
    | .inl value => pure (TypeAssertion.accepted value)
    | .inr value => names.convertString value
  let mutex ← JuliaLean.base.lock.newReentrantLock (concreteReentrantRuntime locks)
  match converted with
  | .accepted value =>
      allocate {
        handle := handle
        ios := buffer
        name := value.bytes
        mark := JuliaLean.base.io.i (-1)
        mutex := mutex
        dolock := true }
  | .rejected value => rejectName value

/-- Compatibility view of the constructor's exception through the IO error carrier.
Source: base/iostream.jl:21 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def newStreamWithBuffer {World Name NotString Stream Vector Lock : Type}
    (access : Access World Stream Vector Lock)
    (vectors : VectorRefOps World Vector)
    (locks : ReentrantRuntime World Lock)
    (names : InnerNameOps World Name NotString)
    (name : JuliaLean.Strings.JStr ⊕ Name) (buffer : Vector) : M World Stream :=
  sourceNewStreamWithBuffer vectors locks names access.new
    (fun _ => throw (.foreignError "TypeError" "new")) name buffer

/-- The constructor's own TypeError uses a separate exception channel so its
complete runtime value survives. Errors from the supplied IO primitives retain
their existing carrier and world. The actual rejected conversion result is
stored only after the fixed ReentrantLock construction has completed.
Source: base/iostream.jl:21; src/datatype.c:1707-1723
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def newStreamWithBufferExact {World L Name Stream Vector Lock : Type}
    (encoding : JuliaLean.base.boot.CoreOps World L)
    (access : Access World Stream Vector Lock)
    (vectors : VectorRefOps World Vector)
    (locks : ReentrantRuntime World Lock)
    (names : InnerNameOps World Name (JuliaLean.base.expr.Value L))
    (name : JuliaLean.Strings.JStr ⊕ Name) (buffer : Vector) :
    ExceptT (JuliaLean.base.boot.Obj L) (M World) Stream :=
  ExceptT.mk <| sourceNewStreamWithBuffer vectors locks names
    (fun fields => do pure (.ok (← access.new fields)))
    (fun value => pure (.error (.typeError (.symbol "new")
      (JuliaLean.base.boot.strV encoding "")
      (JuliaLean.base.boot.coreV encoding "String") value))) name buffer

end JuliaLean.base.iostream.Models2Group18

namespace JuliaLean.base.iostream

open JuliaLean
open JuliaLean.base.io (I U Byte M Error CancelArg Cancellation)

/-- Bind the fixed Int16 read to its installed IOStream implementation.
Source: base/iostream.jl:472 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def readFloat16Stream {World Stream Vector Lock : Type}
    (access : Access World Stream Vector Lock) (locks : Locks World Lock)
    (runtime : Runtime World Vector) (vectors : Models2Group18.VectorRefOps World Vector)
    (stream : Stream) :
    M World (JuliaLean.base.float.FV .f16) :=
  readFloat16 (fun s => readInteger access locks
    (Models2Group18.withVectorPointers vectors runtime) s .i16 (by simp)) stream

/-- Bind the fixed Int32 read to its installed IOStream implementation.
Source: base/iostream.jl:473 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def readFloat32Stream {World Stream Vector Lock : Type}
    (access : Access World Stream Vector Lock) (locks : Locks World Lock)
    (runtime : Runtime World Vector) (vectors : Models2Group18.VectorRefOps World Vector)
    (stream : Stream) :
    M World (JuliaLean.base.float.FV .f32) :=
  readFloat32 (fun s => readInteger access locks
    (Models2Group18.withVectorPointers vectors runtime) s .i32 (by simp)) stream

/-- Bind the fixed Int64 read to its installed IOStream implementation.
Source: base/iostream.jl:474 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def readFloat64Stream {World Stream Vector Lock : Type}
    (access : Access World Stream Vector Lock) (locks : Locks World Lock)
    (runtime : Runtime World Vector) (vectors : Models2Group18.VectorRefOps World Vector)
    (stream : Stream) :
    M World (JuliaLean.base.float.FV .f64) :=
  readFloat64 (fun s => readInteger access locks
    (Models2Group18.withVectorPointers vectors runtime) s .i64 (by simp)) stream

end JuliaLean.base.iostream

namespace JuliaLean.base.iostream

open JuliaLean
open JuliaLean.base.io (I U Byte M Error CancelArg Cancellation)

open Models2Group18

/-- Native vector resizing closes resize!, growth and deletion through the
installed Array bodies; the storage record exposes their memory primitives.
Source: base/array.jl:1559-1574 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def resizeByteVector {World Vector Memory Ref : Type}
    (storage : JuliaLean.base.array.Storage (ByteAllocationM World) Vector Memory Ref)
    (vector : Vector) (count : I) : M World Vector :=
  runByteAllocation <| JuliaLean.base.array.resize pure storage.length
    JuliaLean.base.int.and_int
    (JuliaLean.base.array.growbeg storage pure
      (JuliaLean.base.array.growbegInternal storage))
    (JuliaLean.base.array.growend storage pure
      (JuliaLean.base.array.growendInternal storage))
    (JuliaLean.base.array.deletebeg storage pure)
    (JuliaLean.base.array.deleteend storage pure) vector count

/-- UInt8 vector specialization of the installed indexed pointer method.
Native Int subtraction and pointer addition retain their wrapping semantics.
Source: base/abstractarray.jl:1279-1286; base/pointer.jl:315
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def byteVectorPointerAt {World Vector : Type} (vectors : VectorRefOps World Vector)
    (vector : Vector) (index : I) : M World BytePointer := do
  pure (JuliaLean.base.pointer.ptrAddI64 (← vectorPointer vectors vector) (index - i 1))

/-- The fixed Vector/Int call made by read(s), with native arithmetic and the
installed resize! and pointer bodies. Generic readbytesAllPreserved retains
the full MutableDenseArrayType/Integer domain for selected dispatch.
Source: base/iostream.jl:542-568 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def readbytesAllVector {World Stream Vector Lock Memory Ref : Type}
    (access : Access World Stream Vector Lock) (locks : Locks World Lock)
    (runtime : Runtime World Vector) (vectors : VectorRefOps World Vector)
    (storage : JuliaLean.base.array.Storage (ByteAllocationM World) Vector Memory Ref)
    (preserve : {A : Type} → Vector → M World A → M World A)
    (stream : Stream) (vector : Vector) (count : I) : M World I :=
  readbytesAllPreserved access locks (withVectorPointers vectors runtime)
    (fun vector => runByteAllocation (storage.length vector))
    (fun a b => pure (JuliaLean.base.int.lt a b))
    (fun a b => pure (JuliaLean.base.int.eq_int a b))
    (fun a b => pure (a - b))
    (fun a b => pure (JuliaLean.base.int.jmin a b))
    (fun n => JuliaLean.base.io.liftJl (JInt.convert (IntTy.u64.name) .u64 n.val))
    (fun vector n => do let _ ← resizeByteVector storage vector n; pure ())
    (byteVectorPointerAt vectors) preserve stream vector count

/-- Fixed Vector allocation for the Int32 byte count returned by C.
Source: base/iostream.jl:431-447 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def readavailableVector {World Stream Vector Lock Token Memory RootToken : Type}
    (access : Access World Stream Vector Lock) (locks : Locks World Lock)
    (runtime : Runtime World Vector) (vectors : VectorRefOps World Vector)
    (bytes : ByteAllocationRuntime World Vector Memory RootToken)
    (cancellation : Cancellation World Token)
    (stream : Stream) (cancel : CancelArg Token) : M World Vector :=
  readavailable access locks (withVectorPointers vectors runtime) cancellation
    (fun n => do byteVectorUndef bytes (← toInt n)) stream cancel

/-- Close read(s)'s StringVector, filesize, position, readbytes_all! and resize!
calls. The raw string allocator, memory/header primitives and descriptor-stat
boundary retain their full effects. Only actual IOError values are swallowed.
Source: base/iostream.jl:605-634; base/iobuffer.jl:167-168
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def readAllVector {World Stream Vector Lock Memory Ref StringRef Stat : Type}
    (access : Access World Stream Vector Lock) (locks : Locks World Lock)
    (runtime : Runtime World Vector) (vectors : VectorRefOps World Vector)
    (storage : JuliaLean.base.array.Storage (ByteAllocationM World) Vector Memory Ref)
    (preserve : {A : Type} → Vector → M World A → M World A)
    (allocateString : U → M World StringRef) (stringMemory : StringRef → M World Memory)
    (memoryref : Memory → M World Ref) (memoryLength : Memory → I)
    (newArray : Ref → List I → M World Vector)
    (statFD : JuliaLean.base.libc.RawFD → M World Stat)
    (statSize : Stat → M World I) (systemerror : String → Bool → M World Unit)
    (stream : Stream) : M World Vector :=
  let nativeRuntime := withVectorPointers vectors runtime
  readAll access locks nativeRuntime
    (filesize access locks nativeRuntime
      (stat (Models2Group18.fd access vectors runtime) statFD) statSize)
    (position access locks nativeRuntime systemerror)
    (fun error => match error with
      | .foreignError kind _ => kind == "IOError"
      | _ => false)
    (JuliaLean.base.iobuffer.source_StringVector
      (fun n => JuliaLean.base.io.liftJl (JInt.convert (IntTy.u64.name) .u64 n.val))
      allocateString stringMemory memoryref memoryLength newArray)
    (readbytesAllVector access locks runtime vectors storage preserve)
    (resizeByteVector storage) stream

/-- read(s,nb) selects custom Integer constructors/reading normally; the fixed
1024-byte allocation uses the installed native UInt8 vector constructor.
Source: base/iostream.jl:646-654 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def readCountVector {World Stream Vector N Token Memory RootToken Ref : Type}
    (cancellation : Cancellation World Token) (isTypemax : N → M World Bool)
    (bytes : ByteAllocationRuntime World Vector Memory RootToken)
    (allocateSelected : N → M World Vector)
    (readSelected : Stream → Vector → N → Bool → M World I)
    (storage : JuliaLean.base.array.Storage (ByteAllocationM World) Vector Memory Ref)
    (stream : Stream) (count : N) (all : Bool) (cancel : CancelArg Token) : M World Vector :=
  readCount cancellation isTypemax
    (fun dimension => match dimension with
      | .inl n => byteVectorUndef bytes n
      | .inr n => allocateSelected n)
    readSelected (fun vector n => do let _ ← resizeByteVector storage vector n; pure ())
    stream count all cancel

end JuliaLean.base.iostream


namespace JuliaLean.base.iostream

open JuliaLean
open JuliaLean.base.io (I U Byte M Error CancelArg Cancellation)

/-- The generated default-count wrapper evaluates length before entering the
cancellation-checking method, exactly as positional defaults do in Julia.
Source: base/iostream.jl:599-603 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def readbytesDefault {World Stream Vector N Token : Type}
    (cancellation : Cancellation World Token)
    (length : Vector → M World N)
    (readAll readSome : Stream → Vector → N → M World I)
    (stream : Stream) (array : Vector) (all : Bool) (cancel : CancelArg Token) : M World I := do
  let count ← length array
  readbytes cancellation readAll readSome stream array count all cancel

end JuliaLean.base.iostream

namespace JuliaLean.base.iostream

open JuliaLean
open JuliaLean.base.io (I U Byte M Error CancelArg Cancellation)

open scoped JuliaLean.base.iobuffer.IOHeap

abbrev SharedBufferWorld (Other : Type) :=
  JuliaLean.base.iobuffer.BufferHeap Nat JuliaLean.base.iobuffer.ByteMemory Other

/-- Buffer fields live in the shared heap; the only supplied object operation
is the Core.new allocator. Reference equality is concrete logical identity.
Source context: base/iobuffer.jl:96-107,246-270
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def sharedBufferAccess {Other : Type}
    (allocateObject : JuliaLean.base.iobuffer.Fields JuliaLean.base.iobuffer.ByteMemory →
      M (SharedBufferWorld Other) Nat) :
    JuliaLean.base.iobuffer.Access (M (SharedBufferWorld Other)) Nat
      JuliaLean.base.iobuffer.ByteMemory :=
  JuliaLean.base.iobuffer.bindHeapAccess JuliaLean.base.io.getWorld
    JuliaLean.base.io.setWorld
    (fun operation => throwThe Error (.foreignError "UB" operation))
    { sameRef := fun a b => decide (a = b), allocateObject }

def sharedBufferByteHeap {Other : Type} :
    JuliaLean.base.iobuffer.HeapAccess (M (SharedBufferWorld Other)) :=
  JuliaLean.base.iobuffer.bindHeapPointerHeap JuliaLean.base.io.getWorld JuliaLean.base.io.setWorld

/-- A C write and the following Memory getindex observe the same ByteHeap.
The captured Memory identity/address survives buffer replacement and aliasing.
Source: base/iostream.jl:510-533 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def copyuntilSharedIOBuffer {Other Stream Vector Lock Token : Type}
    (access : Access (SharedBufferWorld Other) Stream Vector Lock)
    (locks : Locks (SharedBufferWorld Other) Lock)
    (runtime : Runtime (SharedBufferWorld Other) Vector)
    (vectors : Models2Group18.VectorRefOps (SharedBufferWorld Other) Vector)
    (cancellation : Cancellation (SharedBufferWorld Other) Token)
    (allocateObject : JuliaLean.base.iobuffer.Fields JuliaLean.base.iobuffer.ByteMemory →
      M (SharedBufferWorld Other) Nat)
    (jlAllocString : U → M (SharedBufferWorld Other) Text)
    (jlStringToGenericMemory : Text →
      M (SharedBufferWorld Other) JuliaLean.base.iobuffer.ByteMemory)
    (preserve : {A : Type} → JuliaLean.base.iobuffer.ByteMemory →
      M (SharedBufferWorld Other) A → M (SharedBufferWorld Other) A)
    (out : Nat) (stream : Stream) (delim : Byte) (keep : Bool)
    (cancel : CancelArg Token) : M (SharedBufferWorld Other) Nat :=
  let buffer := sharedBufferAccess allocateObject
  let heap := sharedBufferByteHeap
  let nativeRuntime := Models2Group18.withVectorPointers vectors runtime
  copyuntilBufferPreserved access locks nativeRuntime cancellation buffer
    (fun out n => do
      let _ ← JuliaLean.base.iobuffer.byteMemoryEnsureRoomInt buffer heap
        jlAllocString jlStringToGenericMemory out n
      pure ())
    (fun memory => pure memory.length)
    (fun memory index => pure (JuliaLean.base.iobuffer.byteMemoryPointer memory index))
    (JuliaLean.base.iobuffer.byteMemoryGetindex heap)
    preserve (fun s => eof access locks nativeRuntime cancellation s .default)
    out stream delim keep cancel

/-- Close the fixed IOBuffer construction and takestring! calls over shared
fields and bytes. Only character-selected dispatch and typed C string operations
remain supplied; they cannot replace buffer field or storage operations.
Source: base/iostream.jl:499-503 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def readuntilCharSharedIOBuffer {Other Stream Vector Lock Char Token : Type}
    (access : Access (SharedBufferWorld Other) Stream Vector Lock)
    (locks : Locks (SharedBufferWorld Other) Lock)
    (runtime : Runtime (SharedBufferWorld Other) Vector)
    (vectors : Models2Group18.VectorRefOps (SharedBufferWorld Other) Vector)
    (cancellation : Cancellation (SharedBufferWorld Other) Token)
    (isAscii : Char → M (SharedBufferWorld Other) Bool)
    (toByte : Char → M (SharedBufferWorld Other) Byte)
    (allocateObject : JuliaLean.base.iobuffer.Fields JuliaLean.base.iobuffer.ByteMemory →
      M (SharedBufferWorld Other) Nat)
    (jlAllocString : U → M (SharedBufferWorld Other) Text)
    (jlStringToGenericMemory : Text →
      M (SharedBufferWorld Other) JuliaLean.base.iobuffer.ByteMemory)
    (jlGenericMemoryToString : JuliaLean.base.iobuffer.ByteMemory → I →
      M (SharedBufferWorld Other) Text)
    (copySelected : Nat → Stream → Char → Bool → CancelArg Token →
      M (SharedBufferWorld Other) Nat)
    (stream : Stream) (delim : Char) (keep : Bool) (cancel : CancelArg Token) :
    M (SharedBufferWorld Other) Text :=
  let buffer := sharedBufferAccess allocateObject
  let heap := sharedBufferByteHeap
  readuntilChar access locks (Models2Group18.withVectorPointers vectors runtime) cancellation
    isAscii toByte
    (fun hint => JuliaLean.base.iobuffer.byteMemoryEmptyIOBuffer buffer
      (JuliaLean.base.iobuffer.bitsConversions .i64)
      (JuliaLean.base.iobuffer.bitsConversions .i64) jlAllocString jlStringToGenericMemory
      (some true) (some true) none (some true) (JInt.typemax .i64) (some hint))
    copySelected
    (JuliaLean.base.iobuffer.byteMemoryTakeString buffer heap (pure [])
      jlGenericMemoryToString jlAllocString jlStringToGenericMemory)
    stream delim keep cancel

end JuliaLean.base.iostream

namespace JuliaLean.base.iostream

open JuliaLean
open JuliaLean.base.io (I U Byte M Error CancelArg Cancellation)

/-- Representation bridge preserving the cancellation exception's available
payload. CancellationRequest's payload is its request byte, rather than a
source message string. Source context: base/cancellation.jl:944,1113-1129. -/
def cancellationIOError : JuliaLean.base.cancellation.CancelError → Error
  | .argumentError message => .jl (.argumentError message)
  | .concurrencyViolationError message => .foreignError "ConcurrencyViolationError" message
  | .fieldError typeName fieldName => .foreignError "FieldError" (reprStr (typeName, fieldName))
  | .cancellationRequest request => .foreignError "CancellationRequest" (toString request.val)
  | .other message => .errorException message

def liftCancellation {World A : Type}
    (action : JuliaLean.base.cancellation.M World A) : M World A := fun world =>
  match action world with
  | none => none
  | some (.ok result) => some (.ok result)
  | some (.error (error, after)) => some (.error (cancellationIOError error, after))

def nativeCancelArg {Source : Type}
    (cancel : CancelArg (JuliaLean.base.cancellation.CancellationToken Source)) :
    JuliaLean.base.cancellation.CancelTokenArg Source :=
  match cancel with
  | .default => .useDefault
  | .explicit none => .none
  | .explicit (some token) => .token token

/-- The shared IO cancellation interface calls the installed resolver and
entry check. A resolved token is returned explicitly, including nothing.
Source: base/cancellation.jl:1106-1120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def nativeCancellation {World Source Task Scope : Type}
    (scopeOps : JuliaLean.base.cancellation.ScopeOps World Source Task Scope)
    (tokenOps : JuliaLean.base.cancellation.TokenOps World Source)
    (slow : Task → JuliaLean.base.cancellation.M World
      (Option (JuliaLean.base.cancellation.CancellationToken Source)))
    (handleCancellation : Option Source → JuliaLean.base.cancellation.U8 →
      JuliaLean.base.cancellation.M World Unit) :
    Cancellation World (JuliaLean.base.cancellation.CancellationToken Source) where
  check cancel := do
    pure (.explicit (← liftCancellation <| JuliaLean.base.cancellation.checkCancelArg
      scopeOps tokenOps slow handleCancellation (nativeCancelArg cancel)))
  resolve cancel :=
    match cancel with
    | .default => liftCancellation <|
        JuliaLean.base.cancellation.resolveCancelTokenDefault scopeOps slow
    | .explicit token => pure (JuliaLean.base.cancellation.resolveCancelTokenExplicit token)

/-- The installed precheck leaves the default sentinel unresolved while
checking explicit tokens. Source: base/cancellation.jl:1122-1129
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def nativePrecheck {World Source Task Scope : Type}
    (scopeOps : JuliaLean.base.cancellation.ScopeOps World Source Task Scope)
    (tokenOps : JuliaLean.base.cancellation.TokenOps World Source)
    (slow : Task → JuliaLean.base.cancellation.M World
      (Option (JuliaLean.base.cancellation.CancellationToken Source)))
    (handleCancellation : Option Source → JuliaLean.base.cancellation.U8 →
      JuliaLean.base.cancellation.M World Unit)
    (cancel : CancelArg (JuliaLean.base.cancellation.CancellationToken Source)) :
    M World (CancelArg (JuliaLean.base.cancellation.CancellationToken Source)) := do
  match ← liftCancellation <| JuliaLean.base.cancellation.precheckCancelArg
      scopeOps tokenOps slow handleCancellation (nativeCancelArg cancel) with
  | .useDefault => pure .default
  | .none => pure (.explicit none)
  | .token token => pure (.explicit (some token))

end JuliaLean.base.iostream

namespace JuliaLean.Streams

/-- `isopen`, `base/iostream.jl:88`, `base/stream.jl:377-382,2219`. -/
def isOpen (s : StreamM) : Bool := s.status != .closed

/-- `iswritable` checks that an IOStream is open and has a writable access mode
(`base/iostream.jl:104`). -/
def isWritable (s : StreamM) : Bool :=
  match s.kind with
  | .ioStream => isOpen s && s.writable
  | .libuvStream | .bufferStream => isOpen s && s.status != .closing && s.writable

end JuliaLean.Streams

namespace JuliaLean.Streams

/-! ## `base/iostream.jl` -/

structure IOFileM where
  data : List UInt8
  position : Nat
  isopen : Bool
  readable : Bool
  writable : Bool
  deriving Repr, DecidableEq

def ioCtor (readable writable : Bool) : IOFileM :=
  { data := [], position := 0, isopen := true, readable, writable }

def ioPointerModel (address : Nat) : Nat := address
def ioFdModel (fd : Int) : Int := fd
def ioStatModel (fd : Int) : Int := fd
def ioFlushModel (s : IOFileM) : Except StreamErr IOFileM :=
  if s.isopen then .ok s else .error .ioError
def ioBytesAvailable (s : IOFileM) : Nat := s.data.length - s.position
def ioEof (s : IOFileM) : Bool := ioBytesAvailable s = 0

def ioClose (s : IOFileM) : IOFileM := { s with isopen := false }

def ioTruncate (s : IOFileM) (n : Nat) : IOFileM :=
  let data := if n ≤ s.data.length then s.data.take n
    else s.data ++ List.replicate (n - s.data.length) 0
  { s with data, position := min s.position n }

def ioSeek (s : IOFileM) (n : Nat) : IOFileM := { s with position := n }
def ioSeekEnd (s : IOFileM) : IOFileM := { s with position := s.data.length }
def ioSkip (s : IOFileM) (delta : Int) : IOFileM :=
  { s with position := (max 0 ((s.position : Int) + delta)).toNat }

inductive OpenMode where | r | rplus | w | wplus | a | aplus
  deriving Repr, DecidableEq

def parseOpenMode : String → Option OpenMode
  | "r" => some .r | "r+" => some .rplus | "w" => some .w
  | "w+" => some .wplus | "a" => some .a | "a+" => some .aplus
  | _ => none

def modeFlags : OpenMode → Bool × Bool × Bool × Bool
  | .r => (true, false, false, false)
  | .rplus => (true, true, false, false)
  | .w => (false, true, true, false)
  | .wplus => (true, true, true, false)
  | .a => (false, true, false, true)
  | .aplus => (true, true, false, true)

def ioWrite (s : IOFileM) (bytes : List UInt8) : Except StreamErr (Nat × IOFileM) :=
  if !s.isopen || !s.writable then .error .argumentError
  else
    let prefixData := s.data.take s.position
    let suffix := s.data.drop (s.position + bytes.length)
    let nextData := prefixData ++ bytes ++ suffix
    let nextPosition := s.position + bytes.length
    .ok (bytes.length,
      ⟨nextData, nextPosition, s.isopen, s.readable, s.writable⟩)

def ioReadN (s : IOFileM) (n : Nat) : List UInt8 × IOFileM :=
  let bytes := (s.data.drop s.position).take n
  (bytes, { s with position := s.position + bytes.length })

def ioReadExact (s : IOFileM) (n : Nat) : Except StreamErr (List UInt8 × IOFileM) :=
  let r := ioReadN s n
  if r.1.length = n then .ok r else .error .eofError

def ioReadAvailable (s : IOFileM) : List UInt8 × IOFileM :=
  ioReadN s (s.data.length - s.position)

def ioReadUntil (s : IOFileM) (d : UInt8) (keep : Bool) : List UInt8 × IOFileM :=
  let unread := s.data.drop s.position
  let r := splitUntil d unread
  let bytes := if r.found && keep then r.before ++ [d] else r.before
  let consumed := r.before.length + if r.found then 1 else 0
  (bytes, { s with position := s.position + consumed })

def ioReadline (s : IOFileM) (keep : Bool) : List UInt8 × IOFileM :=
  let r := ioReadUntil s 10 keep
  if keep then r else (stripTrailingCR r.1, r.2)

def ioTake (s : IOFileM) : List UInt8 × IOFileM :=
  (s.data, { s with data := [], position := 0 })

def ioPeek (s : IOFileM) : Except StreamErr UInt8 :=
  match s.data[s.position]? with | some b => .ok b | none => .error .eofError


end JuliaLean.Streams

namespace JuliaLean.Streams.Methods.IOStream

open JuliaLean.Streams

structure NamedIO where
  name : String
  file : IOFileM
  finalize : Bool
  locking : Bool
  deriving Repr, DecidableEq

structure OpenFlagsM where
  read : Bool
  write : Bool
  create : Bool
  truncate : Bool
  append : Bool
  deriving Repr, DecidableEq

def resolveFlags (read write create truncate append : Option Bool) : OpenFlagsM :=
  let append' := append.getD false
  let provisionalWrite := write.getD (truncate.getD false || append')
  let read' := read.getD (!provisionalWrite)
  let write' := write.getD ((truncate.getD (!read' && provisionalWrite)) || append')
  let truncate' := truncate.getD (!read' && write')
  let create' := create.getD ((!read' && write') || truncate' || append')
  ⟨read', write', create', truncate', append'⟩

/-- Inner `IOStream(name, buf)`, `base/iostream.jl:21`. -/
def m21 (name : String) (buffer : List UInt8) : NamedIO :=
  ⟨name, ⟨buffer, 0, true, true, true⟩, false, true⟩

/-- `IOStream(name, finalize)`, `base/iostream.jl:24-31`. -/
def m24 (name : String) (finalize : Bool) : NamedIO :=
  { m21 name [] with finalize }

/-- `IOStream(name)`, `base/iostream.jl:32`. -/
def m32 (name : String) : NamedIO := m24 name true

/-- Pointer conversion, `base/iostream.jl:34`. -/
def m34 (pointer : Nat) : Nat := pointer

/-- IOStream display, `base/iostream.jl:35`. -/
def m35 (stream : NamedIO) : String := "IOStream(" ++ stream.name ++ ")"

/-- `_lock_ios`, `base/iostream.jl:37-47`. -/
def m37 (_locking : Bool) (value : α) : α := value

/-- `fd(s::IOStream)`, `base/iostream.jl:74`. -/
def m74 (foreignFd : Int) : Int := foreignFd

/-- `stat(s::IOStream)`, `base/iostream.jl:76`. -/
def m76 (fdStat : α) : α := fdStat

/-- `isopen(s::IOStream)`, `base/iostream.jl:88`. -/
def m88 (stream : NamedIO) : Bool := stream.file.isopen

/-- `close(s::IOStream)`, `base/iostream.jl:90-93`. -/
def m90 (stream : NamedIO) (foreignFailed : Bool) : Except StreamErr NamedIO :=
  if foreignFailed then .error .ioError else .ok { stream with file := ioClose stream.file }

/-- `closewrite(s::IOStream)`, `base/iostream.jl:95`. -/
def m95 (_stream : NamedIO) : Unit := ()

/-- `flush(s::IOStream)`, `base/iostream.jl:97-102`. -/
def m97 (stream : NamedIO) : Except StreamErr NamedIO :=
  match ioFlushModel stream.file with
  | .ok file => .ok { stream with file }
  | .error e => .error e

/-- `iswritable(s::IOStream)`, `base/iostream.jl:104`. -/
def m104 (stream : NamedIO) : Bool := stream.file.isopen && stream.file.writable

/-- `isreadable(s::IOStream)`, `base/iostream.jl:106`. -/
def m106 (stream : NamedIO) : Bool := stream.file.isopen && stream.file.readable

/-- `truncate(s, n)`, `base/iostream.jl:137-141`. -/
def m137 (stream : NamedIO) (n : Nat) (foreignFailed : Bool) : Except StreamErr NamedIO :=
  if foreignFailed then .error .ioError else .ok { stream with file := ioTruncate stream.file n }

/-- `seek(s, n)`, `base/iostream.jl:158-163`. -/
def m158 (stream : NamedIO) (n : Nat) (foreignResult : Int) : Except StreamErr NamedIO :=
  if foreignResult = -1 || foreignResult < -1 then .error .ioError
  else .ok { stream with file := ioSeek stream.file n }

/-- `seekstart(s)`, `base/iostream.jl:185`. -/
def m185 (stream : NamedIO) : NamedIO := { stream with file := ioSeek stream.file 0 }

/-- `seekend(s)`, `base/iostream.jl:192-196`. -/
def m192 (stream : NamedIO) (foreignFailed : Bool) : Except StreamErr NamedIO :=
  if foreignFailed then .error .ioError else .ok { stream with file := ioSeekEnd stream.file }

/-- `skip(s, delta)`, `base/iostream.jl:215-220`. -/
def m215 (stream : NamedIO) (delta : Int) (foreignResult : Int) : Except StreamErr NamedIO :=
  if foreignResult = -1 || foreignResult < -1 then .error .ioError
  else .ok { stream with file := ioSkip stream.file delta }

/-- `position(s)`, `base/iostream.jl:247-251`. -/
def m247 (foreignPosition : Int) : Except StreamErr Int :=
  if foreignPosition = -1 then .error .ioError else .ok foreignPosition

/-- `filesize(s)`, `base/iostream.jl:253-260`. -/
def m253 (foreignSize fallbackSize : Int) : Int :=
  if foreignSize = -1 then fallbackSize else foreignSize

/-- `_eof_nolock(s)`, `base/iostream.jl:262`. -/
def m262 (stream : NamedIO) : Bool := ioEof stream.file

/-- `eof(s; cancel)`, `base/iostream.jl:263-268`. -/
def m263 (stream : NamedIO) (cancelled : Bool) : Except StreamErr Bool :=
  if cancelled then .error .ioError else .ok (m262 stream)

/-- `fdio(name, fd, own)`, `base/iostream.jl:281-286`. -/
def m281 (name : String) (fd : Int) (own : Bool) : NamedIO × Int × Bool :=
  (m32 name, fd, own)

/-- `fdio(fd, own)`, `base/iostream.jl:287`. -/
def m287 (fd : Int) (own : Bool) : NamedIO × Int × Bool :=
  m281 ("<fd " ++ toString fd ++ ">") fd own

/-- Keyword `open`, `base/iostream.jl:316-345`. -/
def m316 (name : String) (locking : Bool) (read write create truncate append : Option Bool)
    (openSucceeded appendSeekSucceeded : Bool) : Except StreamErr (NamedIO × OpenFlagsM) :=
  let flags := resolveFlags read write create truncate append
  let stream := { m32 ("<file " ++ name ++ ">") with
    file := ioCtor flags.read flags.write, locking }
  if !openSucceeded then .error .ioError
  else if flags.append && !appendSeekSucceeded then .error .ioError
  else .ok (stream, flags)

/-- AbstractString keyword `open`, `base/iostream.jl:346`. -/
def m346 (convertedName : String) : String := convertedName

/-- Mode-string `open`, `base/iostream.jl:399-407`. -/
def m399 (mode : String) : Except StreamErr OpenMode :=
  match parseOpenMode mode with
  | some value => .ok value
  | none => .error .argumentError

/-- Byte `write`, `base/iostream.jl:411-414`. -/
def m411 (stream : NamedIO) (byte : UInt8) : Except StreamErr (Nat × IOFileM) :=
  ioWrite stream.file [byte]

/-- `unsafe_write`, `base/iostream.jl:416-426`. -/
def m416 (stream : NamedIO) (memory : List UInt8) (n : Nat) (cancelled : Bool) : Except StreamErr (Nat × IOFileM) :=
  if cancelled then .error .ioError
  else ioWrite stream.file (memory.take n)

/-- `bytesavailable`, `base/iostream.jl:429`. -/
def m429 (stream : NamedIO) : Nat := ioBytesAvailable stream.file

/-- `readavailable`, `base/iostream.jl:431-447`. -/
def m431 (stream : NamedIO) (cancelled : Bool) (reportedRead : Nat) : Except StreamErr (List UInt8 × IOFileM) :=
  if cancelled then .error .ioError
  else
    let result := ioReadAvailable stream.file
    if reportedRead != result.1.length then .error .eofError else .ok result

/-- Byte `read`, `base/iostream.jl:449-455`. -/
def m449 (stream : NamedIO) : Except StreamErr (UInt8 × IOFileM) :=
  match stream.file.data[stream.file.position]? with
  | none => .error .eofError
  | some byte => .ok (byte, { stream.file with position := stream.file.position + 1 })

/-- Fixed-width integer `read`, `base/iostream.jl:458-470`. -/
def m458 (stream : NamedIO) (width : Nat) : Except StreamErr (List UInt8 × IOFileM) :=
  ioReadExact stream.file width

/-- Float16 `read`, `base/iostream.jl:472`. -/
def m472 (stream : NamedIO) : Except StreamErr (List UInt8 × IOFileM) := m458 stream 2

/-- Float32 `read`, `base/iostream.jl:473`. -/
def m473 (stream : NamedIO) : Except StreamErr (List UInt8 × IOFileM) := m458 stream 4

/-- Float64 `read`, `base/iostream.jl:474`. -/
def m474 (stream : NamedIO) : Except StreamErr (List UInt8 × IOFileM) := m458 stream 8

/-- `unsafe_read`, `base/iostream.jl:477-483`. -/
def m477 (stream : NamedIO) (n : Nat) : Except StreamErr (List UInt8 × IOFileM) :=
  ioReadExact stream.file n

/-- `take!`, `base/iostream.jl:487-488`. -/
def m487 (stream : NamedIO) : List UInt8 × IOFileM := ioTake stream.file

/-- Byte `readuntil`, `base/iostream.jl:490-493`. -/
def m490 (stream : NamedIO) (delimiter : UInt8) (keep cancelled : Bool) : Except StreamErr (List UInt8 × IOFileM) :=
  if cancelled then .error .ioError else .ok (ioReadUntil stream.file delimiter keep)

/-- `readuntil_string`, `base/iostream.jl:496-498`. -/
def m496 (stream : NamedIO) (delimiter : UInt8) (keep : Bool) : List UInt8 × IOFileM :=
  ioReadUntil stream.file delimiter keep

/-- Character `readuntil`, `base/iostream.jl:499-503`. -/
def m499 (stream : NamedIO) (delimiter : UInt8) (ascii keep cancelled : Bool) : Except StreamErr (List UInt8 × IOFileM) :=
  if cancelled then .error .ioError
  else if ascii then .ok (m496 stream delimiter keep)
  else .ok (ioReadUntil stream.file delimiter keep)

/-- `readline`, `base/iostream.jl:505-508`. -/
def m505 (stream : NamedIO) (keep cancelled : Bool) : Except StreamErr (List UInt8 × IOFileM) :=
  if cancelled then .error .ioError else .ok (ioReadline stream.file keep)

/-- IOBuffer `copyuntil`, `base/iostream.jl:510-533`. -/
def m510 (output : List UInt8) (stream : NamedIO) (delimiter : UInt8) (keep : Bool) : List UInt8 × IOFileM :=
  let read := ioReadUntil stream.file delimiter keep
  (output ++ read.1, read.2)

/-- IOStream `copyuntil`, `base/iostream.jl:535-540`. -/
def m535 (output input : NamedIO) (delimiter : UInt8) (keep : Bool) : Except StreamErr (NamedIO × NamedIO) :=
  let read := ioReadUntil input.file delimiter keep
  match ioWrite output.file read.1 with
  | .error e => .error e
  | .ok written => .ok ({ output with file := written.2 }, { input with file := read.2 })

/-- `readbytes_all!`, `base/iostream.jl:542-568`. -/
def m542 (stream : NamedIO) (buffer : List UInt8) (n : Nat) : Nat × List UInt8 × IOFileM :=
  let read := ioReadN stream.file n
  (read.1.length, buffer ++ read.1, read.2)

/-- `readbytes_some!`, `base/iostream.jl:570-585`. -/
def m570 (stream : NamedIO) (buffer : List UInt8) (n : Nat) : Nat × List UInt8 × IOFileM :=
  let read := ioReadN stream.file n
  (read.1.length, buffer ++ read.1, read.2)

/-- Public `readbytes!`, `base/iostream.jl:599-603`. -/
def m599 (stream : NamedIO) (buffer : List UInt8) (n : Nat) (all cancelled : Bool) : Except StreamErr (Nat × List UInt8 × IOFileM) :=
  if cancelled then .error .ioError
  else .ok (if all then m542 stream buffer n else m570 stream buffer n)

/-- Whole-stream `read`, `base/iostream.jl:605-634`. -/
def m605 (stream : NamedIO) (fillCount sizeHint : Int) : List UInt8 × IOFileM :=
  if fillCount != -1 then ioReadN stream.file fillCount.toNat
  else
    let remaining := if sizeHint < 0 then ioBytesAvailable stream.file else sizeHint.toNat
    ioReadN stream.file remaining

/-- Counted `read`, `base/iostream.jl:646-654`. -/
def m646 (stream : NamedIO) (n : Nat) (all cancelled : Bool) : Except StreamErr (List UInt8 × IOFileM) :=
  if cancelled then .error .ioError
  else
    let read := if all then m542 stream [] n else m570 stream [] n
    .ok (read.2.1, read.2.2)

/-- Byte `peek`, `base/iostream.jl:658-664`. -/
def m658 (stream : NamedIO) : Except StreamErr UInt8 := ioPeek stream.file


end JuliaLean.Streams.Methods.IOStream

namespace JuliaLean.Streams

/-- Prior master checked only the ios writable access bit after close. -/
def legacyIsWritable (s : StreamM) : Bool :=
  if s.kind = .ioStream then s.writable else isWritable s

end JuliaLean.Streams
