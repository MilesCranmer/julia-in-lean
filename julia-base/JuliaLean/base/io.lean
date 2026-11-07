import JuliaLean.Core
import JuliaLean.base.int
import JuliaLean.base.char
import JuliaLean.base.pointer
import JuliaLean.Runtime.Strings
import JuliaLean.Runtime.IO
import JuliaLean.base.strings.string


section

/-!
# The TOML lexer with comment capture (`base/toml/parser.jl`)

Model, at master `bbfa0ce4150`, of the parser state and the character-level utilities of
`base/toml/parser.jl` including line/column bookkeeping and comment capture
(`comments !== nothing`), which `JuliaLean.Toml` leaves out; the comment containers
`CommentBlock` and `Comments`; the `Parser` constructors, `startup` and `reinit!`; the
`@try` macro; and `ParserError` with its formatting (`format_error_message_for_err_type`,
`point_to_line`, `showerror`).

Strings are their bytes and characters their raw `UInt32` values, as in `JuliaLean.Toml`
(`Toml.iterate` decodes UTF-8 as `base/strings/string.jl`). The parsed document, needed by
`path_traverses_array`, is a tree of tables, arrays and leaves. Every `while` loop consumes
one unit of fuel per iteration (each iteration eats at least one byte).
-/

namespace JuliaLean.DocsSyntaxCov.TomlLex

open JuliaLean JuliaLean.DocsSyntaxCov

/-- The bytes `print(io, c::Char)` writes for a raw character value (`write(io, c::Char)`,
`base/io.jl`): the bytes of the big-endian value, stopping at the first zero byte after the
first. -/
def charBytes (u : Nat) : List Nat :=
  let b3 := u / 2 ^ 24 % 256
  let b2 := u / 2 ^ 16 % 256
  let b1 := u / 2 ^ 8 % 256
  let b0 := u % 256
  b3 :: (if b2 == 0 && b1 == 0 && b0 == 0 then [] else b2 :: (if b1 == 0 && b0 == 0 then [] else
    b1 :: (if b0 == 0 then [] else [b0])))

end JuliaLean.DocsSyntaxCov.TomlLex

end

universe readEachUniverse

/-!
# Model of `base/io.jl`

Typed generic IO methods at Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`.
Stream handles and the mutable world are independent type parameters. `Ops` contains
user-extensible IO callees; cancellation, allocation, array and pointer operations
are explicit parameters. `M` preserves the world on exceptions, including partial
reads and writes. An outer `none` represents divergence, rather than a Julia error.
Untranslated source remains visible with a reason. No later-loaded IO implementation
is imported; IOBuffer supplies its adapter in `base/iobuffer.lean`.
-/

namespace JuliaLean.base.io

open JuliaLean

abbrev I := JInt64
abbrev U := JInt .u64
abbrev Byte := JInt .u8

def i (value : Int) : I := JInt.wrap .i64 value
def u (value : Int) : U := JInt.wrap .u64 value
def byte (value : Int) : Byte := JInt.wrap .u8 value

def finallyDo {World A B : Type} (action : M World A) (cleanup : M World B) : M World A := do
  let result ← tryCatch (do pure (Except.ok (← action)))
    (fun error => pure (Except.error error))
  let _ ← cleanup
  match result with
  | .ok value => pure value
  | .error error => throw error

inductive CancelArg (Token : Type) where
  | default
  | explicit (token : Option Token)

structure Cancellation (World Token : Type) where
  check : CancelArg Token → M World (CancelArg Token)
  resolve : CancelArg Token → M World (Option Token)

/-- Abstract IO methods are selected by Julia dispatch, without assumed laws. -/
structure Ops (World Stream : Type) where
  readByte : Stream → M World Byte
  writeByte : Stream → Byte → M World I
  eof : Stream → M World Bool
  bytesavailable : Stream → M World I
  position : Stream → M World I
  seek : Stream → I → M World Unit
  seekend : Stream → M World Unit
  getMark : Stream → M World I
  setMark : Stream → I → M World Unit
  isopen : Stream → M World Bool
  close : Stream → M World Unit
  isreadable : Stream → M World Bool
  iswritable : Stream → M World Bool

structure Flags where
  read : Bool
  write : Bool
  create : Bool
  truncate : Bool
  append : Bool
  deriving DecidableEq

structure SystemError (Extra : Type) where
  messagePrefix : String
  errnum : JInt .i32
  extrainfo : Option Extra

/-- Interned Julia symbols compare by their complete names. -/
structure SymbolName where
  value : String
  deriving DecidableEq

-- UNTRANSLATED
-- Source: base/io.jl:1-27 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- # Generic IO stubs -- all subtypes should implement these (if meaningful)
-- 
-- """
--     IO
-- 
-- Abstract supertype for input/output types.
-- """
-- IO
-- 
-- """
--     EOFError()
-- 
-- No more data was available to read from a file or stream.
-- """
-- struct EOFError <: Exception end
-- 
-- """
--     SystemError(prefix::AbstractString, [errno::Int32])
-- 
-- A system call failed with an error code (in the `errno` global variable).
-- """
-- struct SystemError <: Exception
--     prefix::String
--     errnum::Int32
--     extrainfo
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:28-28 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    SystemError(p::AbstractString, e::Integer, extrainfo) = new(p, e, extrainfo)
```
-/
def systemErrorExtra {World Prefix N Extra : Type}
    (convertPrefix : Prefix → M World String) (convertErrno : N → M World (JInt .i32))
    (messagePrefix : Prefix) (errno : N) (extra : Extra) : M World (SystemError Extra) := do
  pure ⟨← convertPrefix messagePrefix, ← convertErrno errno, some extra⟩

/--
Julia source: base/io.jl:29-29 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    SystemError(p::AbstractString, e::Integer) = new(p, e, nothing)
```
-/
def systemErrorCode {World Prefix N Extra : Type}
    (convertPrefix : Prefix → M World String) (convertErrno : N → M World (JInt .i32))
    (messagePrefix : Prefix) (errno : N) : M World (SystemError Extra) := do
  pure ⟨← convertPrefix messagePrefix, ← convertErrno errno, none⟩

/--
Julia source: base/io.jl:30-30 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    SystemError(p::AbstractString) = new(p, Libc.errno(), nothing)
```
-/
def systemErrorCurrent {World Prefix Extra : Type}
    (convertPrefix : Prefix → M World String) (errno : M World (JInt .i32))
    (messagePrefix : Prefix) : M World (SystemError Extra) := do
  let number ← errno
  pure ⟨← convertPrefix messagePrefix, number, none⟩

-- UNTRANSLATED
-- Source: base/io.jl:31-32 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- end
-- 
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:33-33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lock(::IO) = nothing
```
-/
def lock {World Stream : Type} (_stream : Stream) : M World Unit := pure ()

-- UNTRANSLATED
-- Source: base/io.jl:34-34 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- typeof(lock).name.max_methods = UInt8(1)
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:35-35 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unlock(::IO) = nothing
```
-/
def unlock {World Stream : Type} (_stream : Stream) : M World Unit := pure ()

-- UNTRANSLATED
-- Source: base/io.jl:36-44 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- typeof(unlock).name.max_methods = UInt8(1)
-- 
-- """
--     reseteof(io)
-- 
-- Clear the EOF flag from IO so that further reads (and possibly writes) are
-- again allowed. Note that it may immediately get re-set, if the underlying
-- stream object is at EOF and cannot be resumed.
-- """
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:45-45 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reseteof(x::IO) = nothing
```
-/
def reseteof {World Stream : Type} (_stream : Stream) : M World Unit := pure ()

-- UNTRANSLATED
-- Source: base/io.jl:46-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:47-48 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const SZ_UNBUFFERED_IO = 65536
buffer_writes(x::IO, bufsize=SZ_UNBUFFERED_IO) = x
```
-/
def szUnbufferedIO : I := i 65536

/--
Julia source: base/io.jl:48-48 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
buffer_writes(x::IO, bufsize=SZ_UNBUFFERED_IO) = x
```
-/
def bufferWrites {Stream Size : Type} (stream : Stream) (_size : Size) : Stream := stream

-- UNTRANSLATED
-- Source: base/io.jl:49-182 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     isopen(object)::Bool
-- 
-- Determine whether an object, such as an IO or timer, is still open and hence active.
-- 
-- See also: [`close`](@ref)
-- 
-- # Examples
-- ```jldoctest
-- julia> io = open("my_file.txt", "w+");
-- 
-- julia> isopen(io)
-- true
-- 
-- julia> close(io)
-- 
-- julia> isopen(io)
-- false
-- ```
-- """
-- function isopen end
-- typeof(isopen).name.max_methods = UInt8(1)
-- 
-- """
--     close(io::IO)
-- 
-- Close `io`. Performs a [`flush`](@ref) first.
-- 
-- Closing an IO signals that its underlying resources (OS handle, network
-- connections, etc) should be destroyed.
-- A closed IO is in an undefined state and should not be written to or read from.
-- When attempting to do so, the IO may throw an exception, continue to behave
-- normally, or read/write zero bytes, depending on the implementation.
-- However, implementations should make sure that reading to or writing from a
-- closed IO does not cause undefined behaviour.
-- 
-- See also: [`isopen`](@ref)
-- """
-- function close end
-- typeof(close).name.max_methods = UInt8(1)
-- 
-- """
--     closewrite(stream)
-- 
-- Shutdown the write half of a full-duplex I/O stream. Performs a [`flush`](@ref)
-- first. Notify the other end that no more data will be written to the underlying
-- file. This is not supported by all IO types.
-- 
-- If implemented, `closewrite` causes subsequent `read` or `eof` calls that would
-- block to instead throw EOF or return true, respectively. If the stream is
-- already closed, this is idempotent.
-- 
-- # Examples
-- ```jldoctest
-- julia> io = Base.BufferStream(); # this never blocks, so we can read and write on the same Task
-- 
-- julia> write(io, "request");
-- 
-- julia> # calling `read(io)` here would block forever
-- 
-- julia> closewrite(io);
-- 
-- julia> read(io, String)
-- "request"
-- ```
-- """
-- function closewrite end
-- typeof(closewrite).name.max_methods = UInt8(1)
-- 
-- """
--     flush(io::IO)
-- 
-- Commit all currently buffered writes to the given io.
-- This has a default implementation `flush(::IO) = nothing`, so may be called
-- in generic IO code.
-- """
-- function flush end
-- typeof(flush).name.max_methods = UInt8(1)
-- 
-- """
--     bytesavailable(io)
-- 
-- Return the number of bytes available for reading before a read from this stream or buffer will block.
-- 
-- # Examples
-- ```jldoctest
-- julia> io = IOBuffer("JuliaLang is a GitHub organization");
-- 
-- julia> bytesavailable(io)
-- 34
-- ```
-- """
-- function bytesavailable end
-- typeof(bytesavailable).name.max_methods = UInt8(1)
-- 
-- """
--     readavailable(stream)
-- 
-- Read available buffered data from a stream. Actual I/O is performed only if no
-- data has already been buffered. The result is a `Vector{UInt8}`.
-- 
-- !!! warning
--     The amount of data returned is implementation-dependent; for example it can
--     depend on the internal choice of buffer size. Other functions such as [`read`](@ref)
--     should generally be used instead.
-- """
-- function readavailable end
-- typeof(readavailable).name.max_methods = UInt8(1)
-- 
-- function isexecutable end
-- typeof(isexecutable).name.max_methods = UInt8(1)
-- 
-- """
--     isreadable(io)::Bool
-- 
-- Return `false` if the specified IO object is not readable.
-- 
-- # Examples
-- ```jldoctest
-- julia> open("myfile.txt", "w") do io
--            print(io, "Hello world!");
--            isreadable(io)
--        end
-- false
-- 
-- julia> open("myfile.txt", "r") do io
--            isreadable(io)
--        end
-- true
-- 
-- julia> rm("myfile.txt")
-- ```
-- """
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:183-183 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isreadable(io::IO) = isopen(io)
```
-/
def isreadable {World Stream : Type} (ops : Ops World Stream) (stream : Stream) : M World Bool :=
  ops.isopen stream

-- UNTRANSLATED
-- Source: base/io.jl:184-205 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     iswritable(io)::Bool
-- 
-- Return `false` if the specified IO object is not writable.
-- 
-- # Examples
-- ```jldoctest
-- julia> open("myfile.txt", "w") do io
--            print(io, "Hello world!");
--            iswritable(io)
--        end
-- true
-- 
-- julia> open("myfile.txt", "r") do io
--            iswritable(io)
--        end
-- false
-- 
-- julia> rm("myfile.txt")
-- ```
-- """
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:206-206 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iswritable(io::IO) = isopen(io)
```
-/
def iswritable {World Stream : Type} (ops : Ops World Stream) (stream : Stream) : M World Bool :=
  ops.isopen stream

-- UNTRANSLATED
-- Source: base/io.jl:207-262 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     eof(stream)::Bool
-- 
-- Test whether an I/O stream is at end-of-file. If the stream is not yet exhausted, this
-- function will block to wait for more data if necessary, and then return `false`. Therefore
-- it is always safe to read one byte after seeing `eof` return `false`. `eof` will return
-- `false` as long as buffered data is still available, even if the remote end of a connection
-- is closed.
-- 
-- # Examples
-- ```jldoctest
-- julia> b = IOBuffer("my buffer");
-- 
-- julia> eof(b)
-- false
-- 
-- julia> seekend(b);
-- 
-- julia> eof(b)
-- true
-- ```
-- """
-- function eof end
-- typeof(eof).name.max_methods = UInt8(1)
-- 
-- function copy end
-- function wait_readnb end
-- function wait_close end
-- 
-- """
--     read(io::IO, T)
-- 
-- Read a single value of type `T` from `io`, in canonical binary representation.
-- 
-- Note that Julia does not convert the endianness for you. Use [`ntoh`](@ref) or
-- [`ltoh`](@ref) for this purpose.
-- 
--     read(io::IO, String)
-- 
-- Read the entirety of `io`, as a `String` (see also [`readchomp`](@ref)).
-- 
-- # Examples
-- ```jldoctest
-- julia> io = IOBuffer("JuliaLang is a GitHub organization");
-- 
-- julia> read(io, Char)
-- 'J': ASCII/Unicode U+004A (category Lu: Letter, uppercase)
-- 
-- julia> io = IOBuffer("JuliaLang is a GitHub organization");
-- 
-- julia> read(io, String)
-- "JuliaLang is a GitHub organization"
-- ```
-- """
-- read(stream, t)
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:263-263 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
read(stream, ::Type{Union{}}, slurp...; kwargs...) = error("cannot read a value of type Union{}")
```
-/
def readBottom {World A Stream Args Kw : Type} (_stream : Stream) (_args : Args) (_kw : Kw) : M World A :=
  throw (.errorException "cannot read a value of type Union{}")

-- UNTRANSLATED
-- Source: base/io.jl:264-342 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- 
-- """
--     write(io::IO, x)
-- 
-- Write the canonical binary representation of a value to the given I/O stream or file.
-- Return the number of bytes written into the stream. See also [`print`](@ref) to
-- write a text representation (with an encoding that may depend upon `io`).
-- 
-- The endianness of the written value depends on the endianness of the host system.
-- Convert to/from a fixed endianness when writing/reading (e.g. using  [`htol`](@ref) and
-- [`ltoh`](@ref)) to get results that are consistent across platforms.
-- 
-- You can write multiple values with the same `write` call, i.e. the following are equivalent:
-- 
--     write(io, x, y...)
--     write(io, x) + write(io, y...)
-- 
-- # Examples
-- Consistent serialization:
-- ```jldoctest
-- julia> fname = tempname(); # random temporary filename
-- 
-- julia> open(fname,"w") do f
--            # Make sure we write 64bit integer in little-endian byte order
--            write(f,htol(Int64(42)))
--        end
-- 8
-- 
-- julia> open(fname,"r") do f
--            # Convert back to host byte order and host integer type
--            Int(ltoh(read(f,Int64)))
--        end
-- 42
-- ```
-- 
-- Merging write calls:
-- ```jldoctest
-- julia> io = IOBuffer();
-- 
-- julia> write(io, "JuliaLang is a GitHub organization.", " It has many members.")
-- 56
-- 
-- julia> takestring!(io)
-- "JuliaLang is a GitHub organization. It has many members."
-- 
-- julia> write(io, "Sometimes those members") + write(io, " write documentation.")
-- 44
-- 
-- julia> takestring!(io)
-- "Sometimes those members write documentation."
-- ```
-- User-defined plain-data types without `write` methods can be written when wrapped in a `Ref`:
-- ```jldoctest
-- julia> struct MyStruct; x::Float64; end
-- 
-- julia> io = IOBuffer()
-- IOBuffer(data=UInt8[...], readable=true, writable=true, seekable=true, append=false, size=0, maxsize=Inf, ptr=1, mark=-1)
-- 
-- julia> write(io, Ref(MyStruct(42.0)))
-- 8
-- 
-- julia> seekstart(io); read!(io, Ref(MyStruct(NaN)))
-- Base.RefValue{MyStruct}(MyStruct(42.0))
-- ```
-- """
-- function write end
-- 
-- """
--     writepartial(io::IO, x) -> Int
-- 
-- Write `x` to `io` with partial-write cancellation semantics: where
-- [`write`](@ref) throws the `CancellationRequest` when its governing
-- cancellation token is cancelled mid-write, `writepartial` returns the
-- number of bytes the stream had already accepted, and the (level-triggered)
-- cancellation is delivered at the next cancellation point instead. Callers
-- using it must be prepared for short counts. For IO types whose writes
-- cannot block on cancellable resources it is equivalent to `write`.
-- """
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:343-343 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
writepartial(io::IO, x) = write(io, x)
```
-/
def writepartial {World Stream A N : Type} (write : Stream → A → M World N)
    (stream : Stream) (value : A) : M World N := write stream value

-- UNTRANSLATED
-- Source: base/io.jl:344-345 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- typeof(write).name.max_methods = UInt8(1)
-- 
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:346-346 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
read(s::IO, ::Type{UInt8}) = error(typeof(s)," does not support byte I/O")
```
-/
def readByteFallback {World Stream : Type} (typeName : Stream → String)
    (stream : Stream) : M World Byte :=
  throw (.errorException (typeName stream ++ " does not support byte I/O"))

/--
Julia source: base/io.jl:347-347 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
write(s::IO, x::UInt8) = error(typeof(s)," does not support byte I/O")
```
-/
def writeByteFallback {World Stream : Type} (typeName : Stream → String)
    (stream : Stream) (_value : Byte) : M World I :=
  throw (.errorException (typeName stream ++ " does not support byte I/O"))

-- UNTRANSLATED
-- Source: base/io.jl:348-357 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     unsafe_write(io::IO, ref, nbytes::UInt)
-- 
-- Copy `nbytes` from `ref` (converted to a pointer) into the `IO` object.
-- 
-- It is recommended that subtypes `T<:IO` override the following method signature
-- to provide more efficient implementations:
-- `unsafe_write(s::T, p::Ptr{UInt8}, n::UInt)`
-- """
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:358-364 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_write(s::IO, p::Ptr{UInt8}, n::UInt)
    written::Int = 0
    for i = 1:n
        written += write(s, unsafe_load(p, i))
    end
    return written
end
```
-/
def unsafeWrite {World Stream Pointer : Type} (ops : Ops World Stream)
    (load : Pointer → U → M World Byte) (stream : Stream) (pointer : Pointer) (count : U) : M World I := do
  let mut written := i 0
  for index in List.range count.val.toNat do
    let value ← load pointer (u (index + 1))
    written := written + (← ops.writeByte stream value)
  pure written

-- UNTRANSLATED
-- Source: base/io.jl:365-374 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     unsafe_read(io::IO, ref, nbytes::UInt)
-- 
-- Copy `nbytes` from the `IO` stream object into `ref` (converted to a pointer).
-- 
-- It is recommended that subtypes `T<:IO` override the following method signature
-- to provide more efficient implementations:
-- `unsafe_read(s::T, p::Ptr{UInt8}, n::UInt)`
-- """
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:375-380 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_read(s::IO, p::Ptr{UInt8}, n::UInt)
    for i = 1:n
        unsafe_store!(p, read(s, UInt8)::UInt8, i)
    end
    nothing
end
```
-/
def unsafeRead {World Stream Pointer : Type} (ops : Ops World Stream)
    (store : Pointer → Byte → U → M World Unit) (stream : Stream) (pointer : Pointer) (count : U) : M World Unit := do
  for index in List.range count.val.toNat do
    let value ← ops.readByte stream
    store pointer value (u (index + 1))

-- UNTRANSLATED
-- Source: base/io.jl:381-381 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:382-388 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function peek(s::IO, ::Type{T}) where T
    mark(s)
    try read(s, T)::T
    finally
        reset(s)
    end
end
```
-/
def peek {World Stream A Mark Reset : Type}
    (mark : Stream → M World Mark) (reset : Stream → M World Reset)
    (read : Stream → M World A) (stream : Stream) : M World A := do
  let _ ← mark stream
  finallyDo (read stream) (reset stream)

/--
Julia source: base/io.jl:389-389 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
peek(s::IO, ::Type{Union{}}, slurp...) = throw(MethodError(peek, (s, Union{}, slurp...)))
```
-/
def peekBottom {World Stream Args A : Type} (_stream : Stream) (_args : Args) : M World A :=
  throw (.jl (.methodError "peek"))

-- UNTRANSLATED
-- Source: base/io.jl:390-390 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:391-391 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
peek(s) = peek(s, UInt8)::UInt8
```
-/
def peekByte {World Stream : Type} (peek : Stream → M World Byte)
    (stream : Stream) : M World Byte := peek stream

-- UNTRANSLATED
-- Source: base/io.jl:392-400 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Generic `open` methods
-- 
-- """
--     open_flags(; keywords...)::NamedTuple
-- 
-- Compute the `read`, `write`, `create`, `truncate`, `append` flag value for
-- a given set of keyword arguments to [`open`](@ref) a [`NamedTuple`](@ref).
-- """
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:401-431 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function open_flags(;
    read     :: Union{Bool,Nothing} = nothing,
    write    :: Union{Bool,Nothing} = nothing,
    create   :: Union{Bool,Nothing} = nothing,
    truncate :: Union{Bool,Nothing} = nothing,
    append   :: Union{Bool,Nothing} = nothing,
)
    if write === true && read !== true && append !== true
        create   === nothing && (create   = true)
        truncate === nothing && (truncate = true)
    end

    if truncate === true || append === true
        write  === nothing && (write  = true)
        create === nothing && (create = true)
    end

    write    === nothing && (write    = false)
    read     === nothing && (read     = !write)
    create   === nothing && (create   = false)
    truncate === nothing && (truncate = false)
    append   === nothing && (append   = false)

    return (
        read = read,
        write = write,
        create = create,
        truncate = truncate,
        append = append,
    )
end
```
-/
def openFlags (read write create truncate append : Option Bool) : Flags := Id.run do
  let mut read := read
  let mut write := write
  let mut create := create
  let mut truncate := truncate
  let mut append := append
  if write = some true && read ≠ some true && append ≠ some true then
    if create.isNone then create := some true
    if truncate.isNone then truncate := some true
  if truncate = some true || append = some true then
    if write.isNone then write := some true
    if create.isNone then create := some true
  if write.isNone then write := some false
  if read.isNone then read := some (!write.getD false)
  if create.isNone then create := some false
  if truncate.isNone then truncate := some false
  if append.isNone then append := some false
  return ⟨read.getD false, write.getD false, create.getD false,
    truncate.getD false, append.getD false⟩

-- UNTRANSLATED
-- Source: base/io.jl:432-448 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     open(f::Function, args...; kwargs...)
-- 
-- Apply the function `f` to the result of `open(args...; kwargs...)` and close the resulting file
-- descriptor upon completion.
-- 
-- # Examples
-- ```jldoctest
-- julia> write("myfile.txt", "Hello world!");
-- 
-- julia> open(io->read(io, String), "myfile.txt")
-- "Hello world!"
-- 
-- julia> rm("myfile.txt")
-- ```
-- """
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:449-456 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function open(f::Function, args...; kwargs...)
    io = open(args...; kwargs...)
    try
        f(io)
    finally
        close(io)
    end
end
```
-/
def openWith {World Stream Args Kw A : Type}
    (openIO : Args → Kw → M World Stream) (close : Stream → M World Unit)
    (f : Stream → M World A) (args : Args) (kw : Kw) : M World A := do
  let stream ← openIO args kw
  finallyDo (f stream) (close stream)

-- UNTRANSLATED
-- Source: base/io.jl:457-477 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     AbstractPipe
-- 
-- `AbstractPipe` is an abstract supertype that exists for the convenience of creating
-- pass-through wrappers for other IO objects, so that you only need to implement the
-- additional methods relevant to your type. A subtype only needs to implement one or both of
-- these methods:
-- 
--     struct P <: AbstractPipe; ...; end
--     pipe_reader(io::P) = io.out
--     pipe_writer(io::P) = io.in
-- 
-- If `pipe isa AbstractPipe`, it must obey the following interface:
-- 
-- - `pipe.in` or `pipe.in_stream`, if present, must be of type `IO` and be used to provide input to the pipe
-- - `pipe.out` or `pipe.out_stream`, if present, must be of type `IO` and be used for output from the pipe
-- - `pipe.err` or `pipe.err_stream`, if present, must be of type `IO` and be used for writing errors from the pipe
-- """
-- abstract type AbstractPipe <: IO end
-- 
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:478-484 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getproperty(pipe::AbstractPipe, name::Symbol)
    if name === :in || name === :in_stream || name === :out || name === :out_stream ||
       name === :err || name === :err_stream
        return getfield(pipe, name)::IO
    end
    return getfield(pipe, name)
end
```
-/
def pipeGetproperty {World Pipe Field : Type}
    (getfield : Pipe → SymbolName → M World Field)
    (assertIO : Field → M World Field) (pipe : Pipe) (name : SymbolName) : M World Field := do
  if name.value == "in" || name.value == "in_stream" || name.value == "out" ||
      name.value == "out_stream" || name.value == "err" || name.value == "err_stream" then
    assertIO (← getfield pipe name)
  else getfield pipe name

-- UNTRANSLATED
-- Source: base/io.jl:485-488 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- function pipe_reader end
-- function pipe_writer end
-- 
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:489-489 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iswritable(io::AbstractPipe) = iswritable(pipe_writer(io)::IO)
```
-/
def pipeIswritable {World Pipe Stream : Type} (writer : Pipe → M World Stream)
    (iswritable : Stream → M World Bool) (pipe : Pipe) : M World Bool := do
  iswritable (← writer pipe)

-- UNTRANSLATED
-- Source: base/io.jl:490-494 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # flush/closewrite/unsafe_write accept `cancel` like their LibuvStream
-- # counterparts, so a keyword call on a compound pipe does not miss these
-- # forwarders (only an explicit token is forwarded: the sentinel keeps the
-- # plain call, which any user-defined method of the inner IO supports; see
-- # readbytes! below)
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:495-499 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for f in (:flush, :closewrite)
    @eval $(f)(io::AbstractPipe; cancel::CancelTokenArg=DEFAULT_CANCEL) =
        cancel === DEFAULT_CANCEL ? $(f)(pipe_writer(io)::IO) :
                                    $(f)(pipe_writer(io)::IO; cancel)
end
```
-/
def pipeWriterCancelled {World Pipe Stream Token A : Type}
    (writer : Pipe → M World Stream) (plain : Stream → M World A)
    (explicit : Stream → Option Token → M World A)
    (pipe : Pipe) (cancel : CancelArg Token) : M World A := do
  match cancel with
  | .default => plain (← writer pipe)
  | .explicit token => explicit (← writer pipe) token

/--
Julia source: base/io.jl:500-500 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
write(io::AbstractPipe, byte::UInt8) = write(pipe_writer(io)::IO, byte)
```
-/
def pipeWriteByte {World Pipe Stream : Type} (writer : Pipe → M World Stream)
    (write : Stream → Byte → M World I) (pipe : Pipe) (value : Byte) : M World I := do
  write (← writer pipe) value

/--
Julia source: base/io.jl:501-501 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
writepartial(io::AbstractPipe, x) = writepartial(pipe_writer(io)::IO, x)
```
-/
def pipeWritepartial {World Pipe Stream A N : Type} (writer : Pipe → M World Stream)
    (write : Stream → A → M World N) (pipe : Pipe) (value : A) : M World N := do
  write (← writer pipe) value

/--
Julia source: base/io.jl:502-502 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
write(to::IO, from::AbstractPipe) = write(to, pipe_reader(from))
```
-/
def writePipe {World Pipe Stream Out N : Type} (reader : Pipe → M World Stream)
    (write : Out → Stream → M World N) (out : Out) (pipe : Pipe) : M World N := do
  write out (← reader pipe)

/--
Julia source: base/io.jl:503-505 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_write(io::AbstractPipe, p::Ptr{UInt8}, nb::UInt; cancel::CancelTokenArg=DEFAULT_CANCEL) =
    (cancel === DEFAULT_CANCEL ? unsafe_write(pipe_writer(io)::IO, p, nb) :
                                 unsafe_write(pipe_writer(io)::IO, p, nb; cancel))::Union{Int,UInt}
```
-/
def pipeUnsafeWrite {World Pipe Stream Pointer Token N : Type}
    (writer : Pipe → M World Stream) (plain : Stream → Pointer → U → M World N)
    (explicit : Stream → Pointer → U → Option Token → M World N)
    (pipe : Pipe) (pointer : Pointer) (count : U) (cancel : CancelArg Token) : M World N := do
  match cancel with
  | .default => plain (← writer pipe) pointer count
  | .explicit token => explicit (← writer pipe) pointer count token

/--
Julia source: base/io.jl:506-506 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
buffer_writes(io::AbstractPipe, args...) = buffer_writes(pipe_writer(io)::IO, args...)
```
-/
def pipeBufferWrites {World Pipe Stream Args A : Type} (writer : Pipe → M World Stream)
    (buffer : Stream → Args → M World A) (pipe : Pipe) (args : Args) : M World A := do
  buffer (← writer pipe) args

-- UNTRANSLATED
-- Source: base/io.jl:507-507 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:508-514 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for f in (
        # peek/mark interface
        :mark, :unmark, :reset, :ismarked,
        # Simple reader functions
        :read, :bytesavailable, :reseteof, :isreadable)
    @eval $(f)(io::AbstractPipe) = $(f)(pipe_reader(io)::IO)
end
```
-/
def pipeReaderForward {World Pipe Stream A : Type} (reader : Pipe → M World Stream)
    (method : Stream → M World A) (pipe : Pipe) : M World A := do
  method (← reader pipe)

-- UNTRANSLATED
-- Source: base/io.jl:515-516 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # explicit-token-forwarding reader forwarders (same pattern as readbytes!
-- # below: the sentinel keeps the plain call)
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:517-519 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
readavailable(io::AbstractPipe; cancel::CancelTokenArg=DEFAULT_CANCEL) =
    cancel === DEFAULT_CANCEL ? readavailable(pipe_reader(io)::IO) :
                                readavailable(pipe_reader(io)::IO; cancel)
```
-/
def pipeReadavailable {World Pipe Stream Token A : Type}
    (reader : Pipe → M World Stream) (plain : Stream → M World A)
    (explicit : Stream → Option Token → M World A)
    (pipe : Pipe) (cancel : CancelArg Token) : M World A := do
  match cancel with
  | .default => plain (← reader pipe)
  | .explicit token => explicit (← reader pipe) token

/--
Julia source: base/io.jl:520-522 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
read(io::AbstractPipe, byte::Type{UInt8}; cancel::CancelTokenArg=DEFAULT_CANCEL) =
    (cancel === DEFAULT_CANCEL ? read(pipe_reader(io)::IO, byte) :
                                 read(pipe_reader(io)::IO, byte; cancel))::UInt8
```
-/
def pipeReadByte {World Pipe Stream Token : Type}
    (reader : Pipe → M World Stream) (plain : Stream → M World Byte)
    (explicit : Stream → Option Token → M World Byte)
    (pipe : Pipe) (cancel : CancelArg Token) : M World Byte := do
  match cancel with
  | .default => plain (← reader pipe)
  | .explicit token => explicit (← reader pipe) token

/--
Julia source: base/io.jl:523-523 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_read(io::AbstractPipe, p::Ptr{UInt8}, nb::UInt) = unsafe_read(pipe_reader(io)::IO, p, nb)
```
-/
def pipeUnsafeRead {World Pipe Stream Pointer : Type} (reader : Pipe → M World Stream)
    (read : Stream → Pointer → U → M World Unit)
    (pipe : Pipe) (pointer : Pointer) (count : U) : M World Unit := do
  read (← reader pipe) pointer count

/--
Julia source: base/io.jl:524-527 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copyuntil(out::IO, io::AbstractPipe, arg::UInt8; kw...) = copyuntil(out, pipe_reader(io)::IO, arg; kw...)
copyuntil(out::IO, io::AbstractPipe, arg::AbstractChar; kw...) = copyuntil(out, pipe_reader(io)::IO, arg; kw...)
copyuntil(out::IO, io::AbstractPipe, arg::AbstractString; kw...) = copyuntil(out, pipe_reader(io)::IO, arg; kw...)
copyuntil(out::IO, io::AbstractPipe, arg::AbstractVector; kw...) = copyuntil(out, pipe_reader(io)::IO, arg; kw...)
```
-/
def pipeCopyuntil {World Pipe Stream Out Delim Kw : Type} (reader : Pipe → M World Stream)
    (copy : Out → Stream → Delim → Kw → M World Out)
    (out : Out) (pipe : Pipe) (delim : Delim) (kw : Kw) : M World Out := do
  copy out (← reader pipe) delim kw

/--
Julia source: base/io.jl:528-528 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
readuntil_vector!(io::AbstractPipe, target::AbstractVector, keep::Bool, out) = readuntil_vector!(pipe_reader(io)::IO, target, keep, out)
```
-/
def pipeReaduntilVector {World Pipe Stream Target Out A : Type}
    (reader : Pipe → M World Stream) (read : Stream → Target → Bool → Out → M World A)
    (pipe : Pipe) (target : Target) (keep : Bool) (out : Out) : M World A := do
  read (← reader pipe) target keep out

-- UNTRANSLATED
-- Source: base/io.jl:529-530 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # (only an explicit token is forwarded: the sentinel keeps the plain call,
-- # which any user-defined readbytes! method supports)
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:531-533 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
readbytes!(io::AbstractPipe, target::AbstractVector{UInt8}, n=length(target); cancel::CancelTokenArg=DEFAULT_CANCEL) =
    cancel === DEFAULT_CANCEL ? readbytes!(pipe_reader(io)::IO, target, n) :
                                readbytes!(pipe_reader(io)::IO, target, n; cancel)
```
-/
def pipeReadbytes {World Pipe Stream Target N Token Count : Type}
    (reader : Pipe → M World Stream) (plain : Stream → Target → N → M World Count)
    (explicit : Stream → Target → N → Option Token → M World Count)
    (pipe : Pipe) (target : Target) (count : N) (cancel : CancelArg Token) : M World Count := do
  match cancel with
  | .default => plain (← reader pipe) target count
  | .explicit token => explicit (← reader pipe) target count token

/--
Julia source: base/io.jl:534-534 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
peek(io::AbstractPipe, ::Type{T}) where {T} = peek(pipe_reader(io)::IO, T)::T
```
-/
def pipePeek {World Pipe Stream A : Type} (reader : Pipe → M World Stream)
    (peek : Stream → M World A) (pipe : Pipe) : M World A := do peek (← reader pipe)

/--
Julia source: base/io.jl:535-535 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
wait_readnb(io::AbstractPipe, nb::Int) = wait_readnb(pipe_reader(io)::IO, nb)
```
-/
def pipeWaitReadnb {World Pipe Stream A : Type} (reader : Pipe → M World Stream)
    (wait : Stream → I → M World A) (pipe : Pipe) (count : I) : M World A := do
  wait (← reader pipe) count

/--
Julia source: base/io.jl:536-538 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eof(io::AbstractPipe; cancel::CancelTokenArg=DEFAULT_CANCEL) =
    (cancel === DEFAULT_CANCEL ? eof(pipe_reader(io)::IO) :
                                 eof(pipe_reader(io)::IO; cancel))::Bool
```
-/
def pipeEof {World Pipe Stream Token : Type}
    (reader : Pipe → M World Stream) (plain : Stream → M World Bool)
    (explicit : Stream → Option Token → M World Bool)
    (pipe : Pipe) (cancel : CancelArg Token) : M World Bool := do
  match cancel with
  | .default => plain (← reader pipe)
  | .explicit token => explicit (← reader pipe) token

-- UNTRANSLATED
-- Source: base/io.jl:539-539 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:540-540 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isopen(io::AbstractPipe) = isopen(pipe_writer(io)::IO) || isopen(pipe_reader(io)::IO)
```
-/
def pipeIsopen {World Pipe Stream : Type} (reader writer : Pipe → M World Stream)
    (isopen : Stream → M World Bool) (pipe : Pipe) : M World Bool := do
  if ← isopen (← writer pipe) then pure true else isopen (← reader pipe)

/--
Julia source: base/io.jl:541-541 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
close(io::AbstractPipe) = (close(pipe_writer(io)::IO); close(pipe_reader(io)::IO))
```
-/
def pipeClose {World Pipe Stream : Type} (reader writer : Pipe → M World Stream)
    (close : Stream → M World Unit) (pipe : Pipe) : M World Unit := do
  close (← writer pipe)
  close (← reader pipe)

/--
Julia source: base/io.jl:542-542 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
wait_close(io::AbstractPipe) = (wait_close(pipe_writer(io)::IO); wait_close(pipe_reader(io)::IO))
```
-/
def pipeWaitClose {World Pipe Stream A : Type} (reader writer : Pipe → M World Stream)
    (wait : Stream → M World A) (pipe : Pipe) : M World A := do
  let _ ← wait (← writer pipe)
  wait (← reader pipe)

-- UNTRANSLATED
-- Source: base/io.jl:543-554 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- 
-- # Exception-safe wrappers (io = open(); try f(io) finally close(io))
-- 
-- 
-- """
--     write(filename::AbstractString, content)
-- 
-- Write the canonical binary representation of `content` to a file, which will be created if it does not exist yet or overwritten if it does exist.
-- 
-- Return the number of bytes written into the file.
-- """
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:555-555 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
write(filename::AbstractString, a1, args...) = open(io->write(io, a1, args...), convert(String, filename)::String, "w")
```
-/
def writeFilename {World Filename Stream A Args N : Type}
    (convert : Filename → M World String)
    (openIO : (Stream → M World N) → String → String → M World N)
    (write : Stream → A → Args → M World N)
    (filename : Filename) (first : A) (args : Args) : M World N := do
  let filename ← convert filename
  openIO (fun stream => write stream first args) filename "w"

-- UNTRANSLATED
-- Source: base/io.jl:556-570 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     read(filename::AbstractString)
-- 
-- Read the entire contents of a file as a `Vector{UInt8}`.
-- 
--     read(filename::AbstractString, String)
-- 
-- Read the entire contents of a file as a string.
-- 
--     read(filename::AbstractString, args...)
-- 
-- Open a file and read its contents. `args` is passed to `read`: this is equivalent to
-- `open(io->read(io, args...), filename)`.
-- """
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:571-571 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
read(filename::AbstractString, args...) = open(io->read(io, args...), convert(String, filename)::String)
```
-/
def readFilename {World Filename Stream Args A : Type}
    (convert : Filename → M World String)
    (openIO : (Stream → M World A) → String → M World A)
    (read : Stream → Args → M World A) (filename : Filename) (args : Args) : M World A := do
  let filename ← convert filename
  openIO (fun stream => read stream args) filename

-- UNTRANSLATED
-- Source: base/io.jl:572-572 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:573-573 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
read(filename::AbstractString, ::Type{T}) where {T} = open(io->read(io, T), convert(String, filename)::String)
```
-/
def readFilenameTyped {World Filename Stream A : Type}
    (convert : Filename → M World String)
    (openIO : (Stream → M World A) → String → M World A)
    (read : Stream → M World A) (filename : Filename) : M World A := do
  let filename ← convert filename
  openIO read filename

-- UNTRANSLATED
-- Source: base/io.jl:574-583 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     read!(stream::IO, array::AbstractArray)
--     read!(filename::AbstractString, array::AbstractArray)
-- 
-- Read binary data from an I/O stream or file, filling in `array`.
-- """
-- function read! end
-- typeof(read!).name.max_methods = UInt8(1)
-- 
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:584-584 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
read!(filename::AbstractString, a) = open(io->read!(io, a), convert(String, filename)::String)
```
-/
def readBangFilename {World Filename Stream Array : Type}
    (convert : Filename → M World String)
    (openIO : (Stream → M World Array) → String → M World Array)
    (read : Stream → Array → M World Array) (filename : Filename) (array : Array) : M World Array := do
  let filename ← convert filename
  openIO (fun stream => read stream array) filename

-- UNTRANSLATED
-- Source: base/io.jl:585-622 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # The generic-IO `cancel` convention (referenced as such below): in methods
-- # over abstract `IO`, the inner reads/writes go through arbitrary, possibly
-- # user-extended methods that need not accept a `cancel` keyword. The
-- # resolved token therefore gates *between* those calls, via explicit
-- # cancellation points, while any parks inside them run under the ambient
-- # scope. For the same reason, `cancel` is only forwarded to such methods when
-- # the caller passed it explicitly.
-- 
-- """
--     readuntil(stream::IO, delim; keep::Bool = false)
--     readuntil(filename::AbstractString, delim; keep::Bool = false)
-- 
-- Read a string from an I/O `stream` or a file, up to the given delimiter.
-- The delimiter can be a `UInt8`, `AbstractChar`, string, or vector.
-- Keyword argument `keep` controls whether the delimiter is included in the result.
-- The text is assumed to be encoded in UTF-8.
-- 
-- Return a `String` if `delim` is an `AbstractChar` or a string
-- or otherwise return a `Vector{typeof(delim)}`.   See also [`copyuntil`](@ref)
-- to instead write in-place to another stream (which can be a preallocated [`IOBuffer`](@ref)).
-- 
-- See also [`skipchars`](@ref) to skip characters without returning them; e.g.
-- `skipchars(!=('x'), io)` advances `io` to the next `'x'`, which is left unread.
-- 
-- # Examples
-- ```jldoctest
-- julia> write("my_file.txt", "JuliaLang is a GitHub organization.\\nIt has many members.\\n");
-- 
-- julia> readuntil("my_file.txt", 'L')
-- "Julia"
-- 
-- julia> readuntil("my_file.txt", '.', keep = true)
-- "JuliaLang is a GitHub organization."
-- 
-- julia> rm("my_file.txt")
-- ```
-- """
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:623-623 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
readuntil(filename::AbstractString, delim; kw...) = open(io->readuntil(io, delim; kw...), convert(String, filename)::String)
```
-/
def readuntilFilename {World Filename Stream Delim Kw A : Type}
    (convert : Filename → M World String)
    (openIO : (Stream → M World A) → String → M World A)
    (read : Stream → Delim → Kw → M World A)
    (filename : Filename) (delim : Delim) (kw : Kw) : M World A := do
  let filename ← convert filename
  openIO (fun stream => read stream delim kw) filename

/--
Julia source: base/io.jl:624-626 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
readuntil(stream::IO, delim::UInt8; cancel::CancelTokenArg=DEFAULT_CANCEL, kw...) =
    _unsafe_take!(cancel === DEFAULT_CANCEL ? copyuntil(IOBuffer(sizehint=16), stream, delim; kw...) :
                                              copyuntil(IOBuffer(sizehint=16), stream, delim; cancel, kw...))
```
-/
def readuntilByte {World Stream Buffer Token Kw A : Type}
    (newBuffer : I → M World Buffer)
    (plain : Buffer → Stream → Byte → Kw → M World Buffer)
    (explicit : Buffer → Stream → Byte → Option Token → Kw → M World Buffer)
    (take : Buffer → M World A) (stream : Stream) (delim : Byte)
    (cancel : CancelArg Token) (kw : Kw) : M World A := do
  let out ← newBuffer (i 16)
  let out ← match cancel with
    | .default => plain out stream delim kw
    | .explicit token => explicit out stream delim token kw
  take out

/--
Julia source: base/io.jl:627-629 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
readuntil(stream::IO, delim::Union{AbstractChar, AbstractString}; cancel::CancelTokenArg=DEFAULT_CANCEL, kw...) =
    takestring!(cancel === DEFAULT_CANCEL ? copyuntil(IOBuffer(sizehint=16), stream, delim; kw...) :
                                            copyuntil(IOBuffer(sizehint=16), stream, delim; cancel, kw...))
```
-/
def readuntilText {World Stream Buffer Token Delim Kw Text : Type}
    (newBuffer : I → M World Buffer)
    (plain : Buffer → Stream → Delim → Kw → M World Buffer)
    (explicit : Buffer → Stream → Delim → Option Token → Kw → M World Buffer)
    (takestring : Buffer → M World Text) (stream : Stream) (delim : Delim)
    (cancel : CancelArg Token) (kw : Kw) : M World Text := do
  let out ← newBuffer (i 16)
  let out ← match cancel with
    | .default => plain out stream delim kw
    | .explicit token => explicit out stream delim token kw
  takestring out

/--
Julia source: base/io.jl:630-633 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function readuntil(stream::IO, delim::T; keep::Bool=false, cancel::CancelTokenArg=DEFAULT_CANCEL) where T
    check_cancel_arg(cancel)
    return _copyuntil(Vector{T}(), stream, delim, keep)
end
```
-/
def readuntilScalar {World Stream Delim Token Out : Type}
    (cancellation : Cancellation World Token) (newVector : M World Out)
    (copy : Out → Stream → Delim → Bool → M World Out)
    (stream : Stream) (delim : Delim) (keep : Bool) (cancel : CancelArg Token) : M World Out := do
  let _ ← cancellation.check cancel
  let out ← newVector
  copy out stream delim keep

-- UNTRANSLATED
-- Source: base/io.jl:634-665 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- 
-- """
--     copyuntil(out::IO, stream::IO, delim; keep::Bool = false)
--     copyuntil(out::IO, filename::AbstractString, delim; keep::Bool = false)
-- 
-- Copy a string from an I/O `stream` or a file, up to the given delimiter, to
-- the `out` stream, returning `out`.
-- The delimiter can be a `UInt8`, `AbstractChar`, string, or vector.
-- Keyword argument `keep` controls whether the delimiter is included in the result.
-- The text is assumed to be encoded in UTF-8.
-- 
-- Similar to [`readuntil`](@ref), which returns a `String`; in contrast,
-- `copyuntil` writes directly to `out`, without allocating a string.
-- (This can be used, for example, to read data into a pre-allocated [`IOBuffer`](@ref).)
-- 
-- # Examples
-- ```jldoctest
-- julia> write("my_file.txt", "JuliaLang is a GitHub organization.\\nIt has many members.\\n");
-- 
-- julia> takestring!(copyuntil(IOBuffer(), "my_file.txt", 'L'))
-- "Julia"
-- 
-- julia> takestring!(copyuntil(IOBuffer(), "my_file.txt", '.', keep = true))
-- "JuliaLang is a GitHub organization."
-- 
-- julia> rm("my_file.txt")
-- ```
-- 
-- !!! compat "Julia 1.11"
--     `copyuntil` was introduced in Julia 1.11.
-- """
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:666-666 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copyuntil(out::IO, filename::AbstractString, delim; kw...) = open(io->copyuntil(out, io, delim; kw...), convert(String, filename)::String)
```
-/
def copyuntilFilename {World Filename Stream Out Delim Kw : Type}
    (convert : Filename → M World String)
    (openIO : (Stream → M World Out) → String → M World Out)
    (copy : Out → Stream → Delim → Kw → M World Out)
    (out : Out) (filename : Filename) (delim : Delim) (kw : Kw) : M World Out := do
  let filename ← convert filename
  openIO (fun stream => copy out stream delim kw) filename

-- UNTRANSLATED
-- Source: base/io.jl:667-709 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     readline(io::IO=stdin; keep::Bool=false)
--     readline(filename::AbstractString; keep::Bool=false)
-- 
-- Read a single line of text from the given I/O stream or file (defaults to `stdin`).
-- When reading from a file, the text is assumed to be encoded in UTF-8. Lines in the
-- input end with `'\\n'` or `"\\r\\n"` or the end of an input stream. When `keep` is
-- false (as it is by default), these trailing newline characters are removed from the
-- line before it is returned. When `keep` is true, they are returned as part of the
-- line.
-- 
-- At the end of the stream, an empty string is returned. This is indistinguishable from an
-- empty line unless `keep` is true; alternatively, check [`eof`](@ref) before reading. When
-- reading from a terminal, typing Ctrl-D sets the end-of-file flag of the stream, so subsequent
-- calls return an empty string until [`Base.reseteof`](@ref) is called.
-- 
-- Return a `String`.   See also [`copyline`](@ref) to instead write in-place
-- to another stream (which can be a preallocated [`IOBuffer`](@ref)).
-- 
-- See also [`readuntil`](@ref) for reading until more general delimiters.
-- 
-- # Examples
-- ```jldoctest
-- julia> write("my_file.txt", "JuliaLang is a GitHub organization.\\nIt has many members.\\n");
-- 
-- julia> readline("my_file.txt")
-- "JuliaLang is a GitHub organization."
-- 
-- julia> readline("my_file.txt", keep=true)
-- "JuliaLang is a GitHub organization.\\n"
-- 
-- julia> rm("my_file.txt")
-- ```
-- ```julia-repl
-- julia> print("Enter your name: ")
-- Enter your name:
-- 
-- julia> your_name = readline()
-- Logan
-- "Logan"
-- ```
-- """
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:710-713 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function readline(filename::AbstractString; keep::Bool=false, cancel::CancelTokenArg=DEFAULT_CANCEL)
    tok = resolve_cancel_token(cancel)
    return open(io -> readline(io; keep, cancel=tok), filename)
end
```
-/
def readlineFilename {World Filename Stream Token Text : Type}
    (cancellation : Cancellation World Token)
    (openIO : (Stream → M World Text) → Filename → M World Text)
    (readline : Stream → Bool → CancelArg Token → M World Text)
    (filename : Filename) (keep : Bool) (cancel : CancelArg Token) : M World Text := do
  let token ← cancellation.resolve cancel
  openIO (fun stream => readline stream keep (.explicit token)) filename

/--
Julia source: base/io.jl:714-716 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
readline(s::IO=stdin; keep::Bool=false, cancel::CancelTokenArg=DEFAULT_CANCEL) =
    takestring!(cancel === DEFAULT_CANCEL ? copyline(IOBuffer(sizehint=16), s; keep) :
                                            copyline(IOBuffer(sizehint=16), s; keep, cancel))
```
-/
def readline {World Stream Buffer Token Text : Type}
    (newBuffer : I → M World Buffer)
    (plain : Buffer → Stream → Bool → M World Buffer)
    (explicit : Buffer → Stream → Bool → Option Token → M World Buffer)
    (takestring : Buffer → M World Text)
    (stream : Stream) (keep : Bool) (cancel : CancelArg Token) : M World Text := do
  let out ← newBuffer (i 16)
  let out ← match cancel with
    | .default => plain out stream keep
    | .explicit token => explicit out stream keep token
  takestring out

-- UNTRANSLATED
-- Source: base/io.jl:717-752 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     copyline(out::IO, io::IO=stdin; keep::Bool=false)
--     copyline(out::IO, filename::AbstractString; keep::Bool=false)
-- 
-- Copy a single line of text from an I/O `stream` or a file to the `out` stream,
-- returning `out`.
-- 
-- When reading from a file, the text is assumed to be encoded in UTF-8. Lines in the
-- input end with `'\\n'` or `"\\r\\n"` or the end of an input stream. When `keep` is
-- false (as it is by default), these trailing newline characters are removed from the
-- line before it is returned. When `keep` is true, they are returned as part of the
-- line.
-- 
-- Similar to [`readline`](@ref), which returns a `String`; in contrast,
-- `copyline` writes directly to `out`, without allocating a string.
-- (This can be used, for example, to read data into a pre-allocated [`IOBuffer`](@ref).)
-- 
-- See also [`copyuntil`](@ref) for reading until more general delimiters.
-- 
-- # Examples
-- ```jldoctest
-- julia> write("my_file.txt", "JuliaLang is a GitHub organization.\\nIt has many members.\\n");
-- 
-- julia> takestring!(copyline(IOBuffer(), "my_file.txt"))
-- "JuliaLang is a GitHub organization."
-- 
-- julia> takestring!(copyline(IOBuffer(), "my_file.txt", keep=true))
-- "JuliaLang is a GitHub organization.\\n"
-- 
-- julia> rm("my_file.txt")
-- ```
-- 
-- !!! compat "Julia 1.11"
--     `copyline` was introduced in Julia 1.11.
-- """
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:753-757 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copyline(out::IO, filename::AbstractString; keep::Bool=false,
                  cancel::CancelTokenArg=DEFAULT_CANCEL)
    tok = resolve_cancel_token(cancel)
    return open(io -> copyline(out, io; keep, cancel=tok), filename)
end
```
-/
def copylineFilename {World Filename Stream Out Token : Type}
    (cancellation : Cancellation World Token)
    (openIO : (Stream → M World Out) → Filename → M World Out)
    (copyline : Out → Stream → Bool → CancelArg Token → M World Out)
    (out : Out) (filename : Filename) (keep : Bool) (cancel : CancelArg Token) : M World Out := do
  let token ← cancellation.resolve cancel
  openIO (fun stream => copyline out stream keep (.explicit token)) filename

-- UNTRANSLATED
-- Source: base/io.jl:758-759 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # fallback to optimized methods for IOBuffer in iobuffer.jl
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:760-779 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copyline(out::IO, s::IO; keep::Bool=false, cancel::CancelTokenArg=DEFAULT_CANCEL)
    if keep
        return cancel === DEFAULT_CANCEL ? copyuntil(out, s, 0x0a; keep=true) :
                                           copyuntil(out, s, 0x0a; keep=true, cancel)
    else
        check_cancel_arg(cancel)
        # more complicated to deal with CRLF logic
        while !eof(s)
            b = read(s, UInt8)
            b == 0x0a && break
            if b == 0x0d && !eof(s)
                b = read(s, UInt8)
                b == 0x0a && break
                write(out, 0x0d)
            end
            write(out, b)
        end
        return out
    end
end
```
-/
def copyline {World Stream Out Token : Type} (ops : Ops World Stream)
    (cancellation : Cancellation World Token)
    (write : Out → Byte → M World I)
    (copyuntil : Out → Stream → Byte → Bool → CancelArg Token → M World Out)
    (out : Out) (stream : Stream) (keep : Bool) (cancel : CancelArg Token) : M World Out := do
  if keep then return (← copyuntil out stream (byte 10) true cancel)
  let _ ← cancellation.check cancel
  whileLoop (fun _ : Unit => do
    if ← ops.eof stream then return .inl out
    let mut value ← ops.readByte stream
    if value.val = 10 then return .inl out
    if value.val = 13 then
      if !(← ops.eof stream) then
        value ← ops.readByte stream
        if value.val = 10 then return .inl out
        let _ ← write out (byte 13)
    let _ ← write out value
    return .inr ()) ()

-- UNTRANSLATED
-- Source: base/io.jl:780-806 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     readlines(io::IO=stdin; keep::Bool=false)
--     readlines(filename::AbstractString; keep::Bool=false)
-- 
-- Read all lines of an I/O stream or a file as a vector of strings. Behavior is
-- equivalent to saving the result of reading [`readline`](@ref) repeatedly with the same
-- arguments and saving the resulting lines as a vector of strings.  See also
-- [`eachline`](@ref) to iterate over the lines without reading them all at once.
-- 
-- # Examples
-- ```jldoctest
-- julia> write("my_file.txt", "JuliaLang is a GitHub organization.\\nIt has many members.\\n");
-- 
-- julia> readlines("my_file.txt")
-- 2-element Vector{String}:
--  "JuliaLang is a GitHub organization."
--  "It has many members."
-- 
-- julia> readlines("my_file.txt", keep=true)
-- 2-element Vector{String}:
--  "JuliaLang is a GitHub organization.\\n"
--  "It has many members.\\n"
-- 
-- julia> rm("my_file.txt")
-- ```
-- """
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:807-811 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function readlines(filename::AbstractString; kw...)
    open(filename) do f
        readlines(f; kw...)
    end
end
```
-/
def readlinesFilename {World Filename Stream Kw Lines : Type}
    (openIO : (Stream → M World Lines) → Filename → M World Lines)
    (readlines : Stream → Kw → M World Lines) (filename : Filename) (kw : Kw) : M World Lines :=
  openIO (fun stream => readlines stream kw) filename

/--
Julia source: base/io.jl:812-813 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
readlines(s=stdin; cancel::CancelTokenArg=DEFAULT_CANCEL, kw...) =
    collect(eachline(s; cancel, kw...))
```
-/
def readlines {World Stream Token Kw Iterator Lines : Type}
    (eachline : Stream → CancelArg Token → Kw → M World Iterator)
    (collect : Iterator → M World Lines) (stream : Stream) (cancel : CancelArg Token) (kw : Kw) : M World Lines := do
  collect (← eachline stream cancel kw)

-- UNTRANSLATED
-- Source: base/io.jl:814-816 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- ## byte-order mark, ntoh & hton ##
-- 
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:817-835 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
let a = UInt32[0x01020304]
    endian_bom = GC.@preserve a unsafe_load(convert(Ptr{UInt8}, pointer(a)))
    global ntoh, hton, ltoh, htol
    if endian_bom == 0x01
        ntoh(x) = x
        hton(x) = x
        ltoh(x) = bswap(x)
        htol(x) = bswap(x)
        const global ENDIAN_BOM = 0x01020304
    elseif endian_bom == 0x04
        ntoh(x) = bswap(x)
        hton(x) = bswap(x)
        ltoh(x) = x
        htol(x) = x
        const global ENDIAN_BOM = 0x04030201
    else
        error("seriously? what is this machine?")
    end
end
```
-/
inductive Endian where
  | big | little
  deriving DecidableEq
/--
Julia source: base/io.jl:817-835 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
let a = UInt32[0x01020304]
    endian_bom = GC.@preserve a unsafe_load(convert(Ptr{UInt8}, pointer(a)))
    global ntoh, hton, ltoh, htol
    if endian_bom == 0x01
        ntoh(x) = x
        hton(x) = x
        ltoh(x) = bswap(x)
        htol(x) = bswap(x)
        const global ENDIAN_BOM = 0x01020304
    elseif endian_bom == 0x04
        ntoh(x) = bswap(x)
        hton(x) = bswap(x)
        ltoh(x) = x
        htol(x) = x
        const global ENDIAN_BOM = 0x04030201
    else
        error("seriously? what is this machine?")
    end
end
```
-/
def initializeEndian {World Array Pointer : Type}
    (allocate : List (JInt .u32) → M World Array)
    (pointer : Array → M World Pointer) (load : Pointer → M World Byte)
    (preserve : Array → (Unit → M World Byte) → M World Byte) : M World Endian := do
  let array ← allocate [JInt.wrap .u32 0x01020304]
  let bom ← preserve array (fun _ => do load (← pointer array))
  if bom.val = 1 then pure .big
  else if bom.val = 4 then pure .little
  else throw (.errorException "seriously? what is this machine?")


/--
Julia source: base/io.jl:817-835 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
let a = UInt32[0x01020304]
    endian_bom = GC.@preserve a unsafe_load(convert(Ptr{UInt8}, pointer(a)))
    global ntoh, hton, ltoh, htol
    if endian_bom == 0x01
        ntoh(x) = x
        hton(x) = x
        ltoh(x) = bswap(x)
        htol(x) = bswap(x)
        const global ENDIAN_BOM = 0x01020304
    elseif endian_bom == 0x04
        ntoh(x) = bswap(x)
        hton(x) = bswap(x)
        ltoh(x) = x
        htol(x) = x
        const global ENDIAN_BOM = 0x04030201
    else
        error("seriously? what is this machine?")
    end
end
```
-/
def endianBom (endian : Endian) : JInt .u32 :=
  JInt.wrap .u32 (if endian = .big then 0x01020304 else 0x04030201)

/--
Julia source: base/io.jl:817-835 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
let a = UInt32[0x01020304]
    endian_bom = GC.@preserve a unsafe_load(convert(Ptr{UInt8}, pointer(a)))
    global ntoh, hton, ltoh, htol
    if endian_bom == 0x01
        ntoh(x) = x
        hton(x) = x
        ltoh(x) = bswap(x)
        htol(x) = bswap(x)
        const global ENDIAN_BOM = 0x01020304
    elseif endian_bom == 0x04
        ntoh(x) = bswap(x)
        hton(x) = bswap(x)
        ltoh(x) = x
        htol(x) = x
        const global ENDIAN_BOM = 0x04030201
    else
        error("seriously? what is this machine?")
    end
end
```
-/
def ntoh {A : Type} (endian : Endian) (bswap : A → A) (value : A) : A :=
  if endian = .big then value else bswap value

/--
Julia source: base/io.jl:817-835 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
let a = UInt32[0x01020304]
    endian_bom = GC.@preserve a unsafe_load(convert(Ptr{UInt8}, pointer(a)))
    global ntoh, hton, ltoh, htol
    if endian_bom == 0x01
        ntoh(x) = x
        hton(x) = x
        ltoh(x) = bswap(x)
        htol(x) = bswap(x)
        const global ENDIAN_BOM = 0x01020304
    elseif endian_bom == 0x04
        ntoh(x) = bswap(x)
        hton(x) = bswap(x)
        ltoh(x) = x
        htol(x) = x
        const global ENDIAN_BOM = 0x04030201
    else
        error("seriously? what is this machine?")
    end
end
```
-/
def hton {A : Type} (endian : Endian) (bswap : A → A) (value : A) : A :=
  if endian = .big then value else bswap value

/--
Julia source: base/io.jl:817-835 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
let a = UInt32[0x01020304]
    endian_bom = GC.@preserve a unsafe_load(convert(Ptr{UInt8}, pointer(a)))
    global ntoh, hton, ltoh, htol
    if endian_bom == 0x01
        ntoh(x) = x
        hton(x) = x
        ltoh(x) = bswap(x)
        htol(x) = bswap(x)
        const global ENDIAN_BOM = 0x01020304
    elseif endian_bom == 0x04
        ntoh(x) = bswap(x)
        hton(x) = bswap(x)
        ltoh(x) = x
        htol(x) = x
        const global ENDIAN_BOM = 0x04030201
    else
        error("seriously? what is this machine?")
    end
end
```
-/
def ltoh {A : Type} (endian : Endian) (bswap : A → A) (value : A) : A :=
  if endian = .big then bswap value else value

/--
Julia source: base/io.jl:817-835 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
let a = UInt32[0x01020304]
    endian_bom = GC.@preserve a unsafe_load(convert(Ptr{UInt8}, pointer(a)))
    global ntoh, hton, ltoh, htol
    if endian_bom == 0x01
        ntoh(x) = x
        hton(x) = x
        ltoh(x) = bswap(x)
        htol(x) = bswap(x)
        const global ENDIAN_BOM = 0x01020304
    elseif endian_bom == 0x04
        ntoh(x) = bswap(x)
        hton(x) = bswap(x)
        ltoh(x) = x
        htol(x) = x
        const global ENDIAN_BOM = 0x04030201
    else
        error("seriously? what is this machine?")
    end
end
```
-/
def htol {A : Type} (endian : Endian) (bswap : A → A) (value : A) : A :=
  if endian = .big then bswap value else value

-- UNTRANSLATED
-- Source: base/io.jl:836-892 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     ENDIAN_BOM
-- 
-- The 32-bit byte-order-mark indicates the native byte order of the host machine.
-- Little-endian machines will contain the value `0x04030201`. Big-endian machines will contain
-- the value `0x01020304`.
-- """
-- ENDIAN_BOM
-- 
-- """
--     ntoh(x)
-- 
-- Convert the endianness of a value from Network byte order (big-endian) to that used by the Host.
-- """
-- ntoh(x)
-- 
-- """
--     hton(x)
-- 
-- Convert the endianness of a value from that used by the Host to Network byte order (big-endian).
-- """
-- hton(x)
-- 
-- """
--     ltoh(x)
-- 
-- Convert the endianness of a value from Little-endian to that used by the Host.
-- """
-- ltoh(x)
-- 
-- """
--     htol(x)
-- 
-- Convert the endianness of a value from that used by the Host to Little-endian.
-- """
-- htol(x)
-- 
-- 
-- """
--     isreadonly(io)::Bool
-- 
-- Determine whether a stream is read-only.
-- 
-- # Examples
-- ```jldoctest
-- julia> io = IOBuffer("JuliaLang is a GitHub organization");
-- 
-- julia> isreadonly(io)
-- true
-- 
-- julia> io = IOBuffer();
-- 
-- julia> isreadonly(io)
-- false
-- ```
-- """
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:893-893 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isreadonly(s) = isreadable(s) && !iswritable(s)
```
-/
def isreadonly {World Stream : Type} (ops : Ops World Stream) (stream : Stream) : M World Bool := do
  if ← ops.isreadable stream then pure (!(← ops.iswritable stream)) else pure false

-- UNTRANSLATED
-- Source: base/io.jl:894-896 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- ## binary I/O ##
-- 
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:897-897 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
write(io::IO, x) = throw(MethodError(write, (io, x)))
```
-/
def writeFallback {World Stream A N : Type} (_stream : Stream) (_value : A) : M World N :=
  throw (.jl (.methodError "write"))

/--
Julia source: base/io.jl:898-905 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function write(io::IO, x1, xs...; cancel::CancelTokenArg=DEFAULT_CANCEL)
    check_cancel_arg(cancel)
    written::Int = write(io, x1)
    for x in xs
        written += write(io, x)
    end
    return written
end
```
-/
def writeMany {World Stream A Token : Type} (cancellation : Cancellation World Token)
    (write : Stream → A → M World I) (stream : Stream) (first : A)
    (rest : List A) (cancel : CancelArg Token) : M World I := do
  let _ ← cancellation.check cancel
  let mut written ← write stream first
  for value in rest do
    written := written + (← write stream value)
  pure written

-- UNTRANSLATED
-- Source: base/io.jl:906-906 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:907-908 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline unsafe_write(s::IO, p::Ref{T}, n::Integer) where {T} =
    unsafe_write(s, unsafe_convert(Ref{T}, p)::Ptr, n) # mark noinline to ensure ref is gc-rooted somewhere (by the caller)
```
-/
def unsafeWriteRef {World Stream Ref Pointer N Count : Type}
    (convert : Ref → M World Pointer) (write : Stream → Pointer → N → M World Count)
    (stream : Stream) (reference : Ref) (count : N) : M World Count := do
  write stream (← convert reference) count

/--
Julia source: base/io.jl:909-909 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_write(s::IO, p::Ptr, n::Integer) = unsafe_write(s, convert(Ptr{UInt8}, p), convert(UInt, n))
```
-/
def unsafeWritePointer {World Stream Pointer BytePointer N Count : Type}
    (convertPointer : Pointer → M World BytePointer) (convertCount : N → M World U)
    (write : Stream → BytePointer → U → M World Count)
    (stream : Stream) (pointer : Pointer) (count : N) : M World Count := do
  let pointer ← convertPointer pointer
  let count ← convertCount count
  write stream pointer count

/--
Julia source: base/io.jl:910-917 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function write(s::IO, x::Ref{T}) where {T}
    x isa Ptr && error("write cannot copy from a Ptr")
    if isbitstype(T)
        Int(unsafe_write(s, x, Core.sizeof(T)))
    else
        write(s, x[])
    end
end
```
-/
def writeRef {World Stream Ref A N : Type}
    (isPointer : Ref → Bool) (isBits : Bool) (sizeof : I)
    (unsafeWrite : Stream → Ref → I → M World N) (toInt : N → M World I)
    (get : Ref → M World A) (write : Stream → A → M World I)
    (stream : Stream) (reference : Ref) : M World I := do
  if isPointer reference then throw (.errorException "write cannot copy from a Ptr")
  if isBits then toInt (← unsafeWrite stream reference sizeof)
  else write stream (← get reference)

/--
Julia source: base/io.jl:918-918 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
write(s::IO, x::Int8) = write(s, reinterpret(UInt8, x))
```
-/
def writeInt8 {World Stream : Type} (ops : Ops World Stream)
    (stream : Stream) (value : JInt .i8) : M World I :=
  ops.writeByte stream (JInt.wrap .u8 value.val)

/--
Julia source: base/io.jl:919-921 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function write(s::IO, x::Union{Int16,UInt16,Int32,UInt32,Int64,UInt64,Int128,UInt128,Float16,Float32,Float64})
    return unsafe_write(s, Ref(x), Core.sizeof(x))
end
```
-/
def writeBits {World Stream A Ref N : Type} (reference : A → M World Ref)
    (sizeof : A → I) (unsafeWrite : Stream → Ref → I → M World N)
    (stream : Stream) (value : A) : M World N := do
  unsafeWrite stream (← reference value) (sizeof value)

-- UNTRANSLATED
-- Source: base/io.jl:922-922 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:923-923 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
write(s::IO, x::Bool) = write(s, UInt8(x))
```
-/
def writeBool {World Stream : Type} (ops : Ops World Stream)
    (stream : Stream) (value : Bool) : M World I :=
  ops.writeByte stream (byte (if value then 1 else 0))

/--
Julia source: base/io.jl:924-924 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
write(to::IO, p::Ptr) = write(to, convert(UInt, p))
```
-/
def writePointer {World Stream Pointer N : Type} (convert : Pointer → M World U)
    (write : Stream → U → M World N) (stream : Stream) (pointer : Pointer) : M World N := do
  write stream (← convert pointer)

-- UNTRANSLATED
-- Source: base/io.jl:925-925 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:926-938 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function write(s::IO, A::AbstractArray; cancel::CancelTokenArg=DEFAULT_CANCEL)
    check_cancel_arg(cancel)
    if !isbitstype(eltype(A))
        error("`write` is not supported on non-isbits arrays")
    end
    nb = 0
    r = Ref{eltype(A)}()
    for a in A
        r[] = a
        nb += @noinline unsafe_write(s, r, Core.sizeof(r)) # r must be heap-allocated
    end
    return nb
end
```
-/
def writeArray {World Stream Array A Ref State Token : Type}
    (cancellation : Cancellation World Token) (isBits : Bool)
    (newRef : M World Ref) (setRef : Ref → A → M World Unit) (sizeofRef : Ref → I)
    (iterate : Array → Option State → M World (Option (A × State)))
    (unsafeWrite : Stream → Ref → I → M World I)
    (stream : Stream) (array : Array) (cancel : CancelArg Token) : M World I := do
  let _ ← cancellation.check cancel
  if !isBits then throw (.errorException "`write` is not supported on non-isbits arrays")
  let reference ← newRef
  whileLoop (fun ((state, count) : Option State × I) => do
    match ← iterate array state with
    | none => pure (.inl count)
    | some (value, state) => do
      setRef reference value
      let count := count + (← unsafeWrite stream reference (sizeofRef reference))
      pure (.inr (some state, count))) (none, i 0)

-- UNTRANSLATED
-- Source: base/io.jl:939-939 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:940-971 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function write(s::IO, A::StridedArray; cancel::CancelTokenArg=DEFAULT_CANCEL)
    check_cancel_arg(cancel)
    if !isbitstype(eltype(A))
        error("`write` is not supported on non-isbits arrays")
    end
    _checkcontiguous(Bool, A) &&
        return GC.@preserve A unsafe_write(s, pointer(A), elsize(A) * length(A))
    sz::Dims = size(A)
    st::Dims = strides(A)
    msz, mst, n = merge_adjacent_dim(sz, st)
    mst == 1 || return invoke(write, Tuple{IO, AbstractArray}, s, A; cancel=nothing)
    n == ndims(A) &&
        return GC.@preserve A unsafe_write(s, pointer(A), elsize(A) * length(A))
    sz′, st′ = tail(sz), tail(st)
    while n > 1
        sz′ = (tail(sz′)..., 1)
        st′ = (tail(st′)..., 0)
        n -= 1
    end
    GC.@preserve A begin
        nb = 0
        iter = CartesianIndices(sz′)
        for I in iter
            p = pointer(A)
            for i in 1:length(sz′)
                p += elsize(A) * st′[i] * (I[i] - 1)
            end
            nb += unsafe_write(s, p, elsize(A) * msz)
        end
        return nb
    end
end
```
-/
def writeStridedArray {World Stream Array Pointer Token : Type}
    (cancellation : Cancellation World Token) (isBits : Bool)
    (contiguous : Array → M World Bool) (pointer : Array → M World Pointer)
    (elementSize arrayLength : Array → M World I)
    (unsafeWrite : Stream → Pointer → I → M World I)
    (size strides : Array → M World (List I))
    (mergeAdjacentDim : List I → List I → M World (I × I × I))
    (writeAbstractArray : Stream → Array → M World I)
    (addPointer : Pointer → I → M World Pointer)
    (stream : Stream) (array : Array) (cancel : CancelArg Token) : M World I := do
  let _ ← cancellation.check cancel
  if !isBits then throw (.errorException "`write` is not supported on non-isbits arrays")
  let whole : M World I := do
    unsafeWrite stream (← pointer array) ((← elementSize array) * (← arrayLength array))
  if ← contiguous array then return ← whole
  let sz ← size array
  let st ← strides array
  let (msz, mst, n) ← mergeAdjacentDim sz st
  if mst.val ≠ 1 then return ← writeAbstractArray stream array
  if n.val = sz.length then return ← whole
  let (sz', st') ← stridedTails sz st n
  whileLoop (fun ((index, count) : Option (List I) × I) => do
    match index with
    | none => pure (.inl count)
    | some index => do
      let p ← stridedPointer (pointer array) (elementSize array) addPointer st' index
      let count := count + (← unsafeWrite stream p ((← elementSize array) * msz))
      pure (.inr (cartesianNext sz' index, count))) (cartesianFirst sz', i 0)
where
  /-- `tail(t)` of a `Dims` tuple: `ArgumentError` for the empty tuple. -/
  tail (xs : List I) : M World (List I) :=
    match xs with
    | [] => throw (.jl (.argumentError "Cannot call tail on an empty tuple."))
    | _ :: rest => pure rest
  /-- `sz′, st′ = tail(sz), tail(st)` and the `while n > 1` loop. -/
  stridedTails (sz st : List I) (n : I) : M World (List I × List I) := do
    whileLoop (fun ((sz', st', n) : List I × List I × I) => do
      if n.val > 1 then
        pure (.inr ((← tail sz') ++ [i 1], (← tail st') ++ [i 0], n - i 1))
      else pure (.inl (sz', st'))) ((← tail sz), (← tail st), n)
  /-- The first element of `CartesianIndices(sz)`, in column-major order. -/
  cartesianFirst (sz : List I) : Option (List I) :=
    if sz.all (fun s => decide (1 ≤ s.val)) then some (sz.map fun _ => i 1) else none
  /-- The element of `CartesianIndices(sz)` after `index`. -/
  cartesianNext : List I → List I → Option (List I)
    | s :: sz, x :: xs =>
      if x.val < s.val then some ((x + i 1) :: xs) else (cartesianNext sz xs).map (i 1 :: ·)
    | _, _ => none
  /-- `p = pointer(A)` and the `for i in 1:length(sz′)` loop. -/
  stridedPointer (pointer : M World Pointer) (elementSize : M World I)
      (addPointer : Pointer → I → M World Pointer) (st' index : List I) : M World Pointer := do
    let mut p ← pointer
    for (stride, x) in st'.zip index do
      p ← addPointer p ((← elementSize) * stride * (x - i 1))
    pure p

-- UNTRANSLATED
-- Source: base/io.jl:972-972 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:973-980 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function write(io::IO, c::Char)
    u = bswap(reinterpret(UInt32, c))
    n = 0
    while true
        n += write(io, u % UInt8)
        (u >>= 8) == 0 && return n
    end
end
```
-/
def writeChar {World Stream : Type} (ops : Ops World Stream)
    (stream : Stream) (character : JuliaLean.base.char.JChar) : M World I := do
  let word : JInt .u32 := JInt.wrap .u32 character.toNat
  let word := JuliaLean.base.int.bswap_int word (by decide)
  whileLoop (fun ((word, count) : JInt .u32 × I) => do
    let count := count + (← ops.writeByte stream (JInt.rem .u8 word))
    let word := JuliaLean.base.int.lshr_int word (i 8)
    if word.val = 0 then return .inl count
    else return .inr (word, count)) (word, i 0)

-- UNTRANSLATED
-- Source: base/io.jl:981-983 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # write(io, ::AbstractChar) is not defined: implementations
-- # must provide their own encoding-specific method.
-- 
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:984-987 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function write(io::IO, s::Symbol)
    pname = unsafe_convert(Ptr{UInt8}, s)
    return unsafe_write(io, pname, ccall(:strlen, Csize_t, (Cstring,), pname))
end
```
-/
def writeSymbol {World Stream Symbol Pointer N : Type}
    (pointer : Symbol → M World Pointer) (strlen : Pointer → M World U)
    (unsafeWrite : Stream → Pointer → U → M World N)
    (stream : Stream) (symbol : Symbol) : M World N := do
  let name ← pointer symbol
  unsafeWrite stream name (← strlen name)

-- UNTRANSLATED
-- Source: base/io.jl:988-988 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:989-995 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function write(to::IO, from::IO)
    n = 0
    while !eof(from)
        n += write(to, readavailable(from))
    end
    return n
end
```
-/
def writeStream {World Stream Out Chunk : Type} (ops : Ops World Stream)
    (readavailable : Stream → M World Chunk) (write : Out → Chunk → M World I)
    (out : Out) (stream : Stream) : M World I :=
  whileLoop (fun count => do
    if ← ops.eof stream then return .inl count
    let count := count + (← write out (← readavailable stream))
    return .inr count) (i 0)

-- UNTRANSLATED
-- Source: base/io.jl:996-996 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:997-997 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline unsafe_read(s::IO, p::Ref{T}, n::Integer) where {T} = unsafe_read(s, unsafe_convert(Ref{T}, p)::Ptr, n) # mark noinline to ensure ref is gc-rooted somewhere (by the caller)
```
-/
def unsafeReadRef {World Stream Ref Pointer N : Type}
    (convert : Ref → M World Pointer) (read : Stream → Pointer → N → M World Unit)
    (stream : Stream) (reference : Ref) (count : N) : M World Unit := do
  read stream (← convert reference) count

/--
Julia source: base/io.jl:998-998 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_read(s::IO, p::Ptr, n::Integer) = unsafe_read(s, convert(Ptr{UInt8}, p), convert(UInt, n))
```
-/
def unsafeReadPointer {World Stream Pointer BytePointer N : Type}
    (convertPointer : Pointer → M World BytePointer) (convertCount : N → M World U)
    (read : Stream → BytePointer → U → M World Unit)
    (stream : Stream) (pointer : Pointer) (count : N) : M World Unit := do
  let pointer ← convertPointer pointer
  let count ← convertCount count
  read stream pointer count

/--
Julia source: base/io.jl:999-1007 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function read!(s::IO, x::Ref{T}) where {T}
    x isa Ptr && error("read! cannot copy into a Ptr")
    if isbitstype(T)
        unsafe_read(s, x, Core.sizeof(T))
    else
        x[] = read(s, T)
    end
    return x
end
```
-/
def readRef {World Stream Ref A : Type}
    (isPointer : Ref → Bool) (isBits : Bool) (sizeof : I)
    (unsafeRead : Stream → Ref → I → M World Unit)
    (read : Stream → M World A) (set : Ref → A → M World Unit)
    (stream : Stream) (reference : Ref) : M World Ref := do
  if isPointer reference then throw (.errorException "read! cannot copy into a Ptr")
  if isBits then unsafeRead stream reference sizeof
  else set reference (← read stream)
  pure reference

-- UNTRANSLATED
-- Source: base/io.jl:1008-1008 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:1009-1009 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
read(s::IO, ::Type{Int8}) = reinterpret(Int8, read(s, UInt8))
```
-/
def readInt8 {World Stream : Type} (ops : Ops World Stream)
    (stream : Stream) : M World (JInt .i8) := do
  pure (JInt.rem .i8 (← ops.readByte stream))

/--
Julia source: base/io.jl:1010-1014 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function read(s::IO, T::Union{Type{Int16},Type{UInt16},Type{Int32},Type{UInt32},Type{Int64},Type{UInt64},Type{Int128},Type{UInt128},Type{Float16},Type{Float32},Type{Float64}})
    r = Ref{T}(0)
    unsafe_read(s, r, Core.sizeof(T))
    return r[]
end
```
-/
def readBits {World Stream A Ref : Type}
    (zeroRef : M World Ref) (sizeof : I)
    (unsafeRead : Stream → Ref → I → M World Unit) (get : Ref → M World A)
    (stream : Stream) : M World A := do
  let reference ← zeroRef
  unsafeRead stream reference sizeof
  get reference

-- UNTRANSLATED
-- Source: base/io.jl:1015-1015 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:1016-1016 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
read(s::IO, ::Type{Bool}) = (read(s, UInt8) != 0)
```
-/
def readBool {World Stream : Type} (ops : Ops World Stream) (stream : Stream) : M World Bool := do
  pure ((← ops.readByte stream).val != 0)

/--
Julia source: base/io.jl:1017-1017 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
read(s::IO, ::Type{Ptr{T}}) where {T} = convert(Ptr{T}, read(s, UInt))
```
-/
def readPointer {World Stream Pointer : Type}
    (readUInt : Stream → M World U) (convert : U → M World Pointer)
    (stream : Stream) : M World Pointer := do convert (← readUInt stream)

-- UNTRANSLATED
-- Source: base/io.jl:1018-1018 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:1019-1037 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function read!(s::IO, A::AbstractArray{T}; cancel::CancelTokenArg=DEFAULT_CANCEL) where {T}
    check_cancel_arg(cancel)
    if isbitstype(T) && _checkcontiguous(Bool, A)
        GC.@preserve A unsafe_read(s, pointer(A), elsize(A) * length(A))
    else
        if isbitstype(T)
            r = Ref{T}()
            for i in eachindex(A)
                @noinline unsafe_read(s, r, Core.sizeof(r)) # r must be heap-allocated
                A[i] = r[]
            end
        else
            for i in eachindex(A)
                A[i] = read(s, T)
            end
        end
    end
    return A
end
```
-/
def readArray {World Stream Array Index IndexIterator State Pointer A Ref Token : Type}
    (cancellation : Cancellation World Token) (isBits : Bool)
    (contiguous : Array → M World Bool) (pointer : Array → M World Pointer)
    (elementSize arrayLength : Array → M World I)
    (unsafeReadPointer : Stream → Pointer → I → M World Unit)
    (newRef : M World Ref) (sizeofRef : Ref → I)
    (unsafeRead : Stream → Ref → I → M World Unit) (getRef : Ref → M World A)
    (eachindex : Array → M World IndexIterator)
    (iterate : IndexIterator → Option State → M World (Option (Index × State)))
    (set : Array → Index → A → M World Unit) (read : Stream → M World A)
    (stream : Stream) (array : Array) (cancel : CancelArg Token) : M World Array := do
  let _ ← cancellation.check cancel
  let bulk ← if isBits then contiguous array else pure false
  if bulk then
    let pointer ← pointer array
    let elementSize ← elementSize array
    let length ← arrayLength array
    unsafeReadPointer stream pointer (elementSize * length)
  else
    if isBits then
      let reference ← newRef
      let indices ← eachindex array
      whileLoop (fun state : Option State => do
        match ← iterate indices state with
        | none => pure (.inl ())
        | some (index, state) => do
          unsafeRead stream reference (sizeofRef reference)
          set array index (← getRef reference)
          pure (.inr (some state))) none
    else
      let indices ← eachindex array
      whileLoop (fun state : Option State => do
        match ← iterate indices state with
        | none => pure (.inl ())
        | some (index, state) => do
          set array index (← read stream)
          pure (.inr (some state))) none
  pure array

-- UNTRANSLATED
-- Source: base/io.jl:1038-1042 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # bitarray.jl loads before cancellation machinery in bootstrap order, so
-- # write the specialization here.
-- # TODO: because the generic `write` design relies on a bug (#9498), we have to
-- # explicitly add a `cancel` kwarg to avoid hitting the ::AbstractArray method
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:1043-1046 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function write(s::IO, B::BitArray; cancel::CancelTokenArg=DEFAULT_CANCEL)
    check_cancel_arg(cancel)
    return write(s, B.chunks)
end
```
-/
def writeBitArray {World Stream Array Chunks Token N : Type}
    (cancellation : Cancellation World Token) (chunks : Array → M World Chunks)
    (write : Stream → Chunks → M World N) (stream : Stream) (array : Array)
    (cancel : CancelArg Token) : M World N := do
  let _ ← cancellation.check cancel
  write stream (← chunks array)

/--
Julia source: base/io.jl:1047-1057 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function read!(s::IO, B::BitArray; cancel::CancelTokenArg=DEFAULT_CANCEL)
    check_cancel_arg(cancel)
    n = length(B)
    Bc = B.chunks
    read!(s, Bc)
    if length(Bc) > 0 && Bc[end] & _msk_end(n) ≠ Bc[end]
        Bc[end] &= _msk_end(n) # ensure that the BitArray is not broken
        throw(DimensionMismatch("read mismatch, found non-zero bits after BitArray length"))
    end
    return B
end
```
-/
def readBitArray {World Stream Array Chunks Token : Type}
    (cancellation : Cancellation World Token) (length : Array → M World I)
    (chunks : Array → M World Chunks) (read : Stream → Chunks → M World Chunks)
    (chunksLength : Chunks → M World I) (last : Chunks → M World U)
    (setLast : Chunks → U → M World Unit) (maskEnd : I → M World U)
    (stream : Stream) (array : Array) (cancel : CancelArg Token) : M World Array := do
  let _ ← cancellation.check cancel
  let length ← length array
  let chunks ← chunks array
  let _ ← read stream chunks
  if (← chunksLength chunks).val > 0 then
    let word ← last chunks
    let mask ← maskEnd length
    let current ← last chunks
    if (JuliaLean.base.int.and_int word mask).val != current.val then
      let word ← last chunks
      let mask ← maskEnd length
      setLast chunks (JuliaLean.base.int.and_int word mask)
      throw (.foreignError "DimensionMismatch" "read mismatch, found non-zero bits after BitArray length")
  pure array

-- UNTRANSLATED
-- Source: base/io.jl:1058-1058 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:1059-1089 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function read!(s::IO, A::StridedArray{T}; cancel::CancelTokenArg=DEFAULT_CANCEL) where {T}
    check_cancel_arg(cancel)
    if !isbitstype(T) || _checkcontiguous(Bool, A)
        return invoke(read!, Tuple{IO, AbstractArray}, s, A; cancel=nothing)
    end
    sz::Dims = size(A)
    st::Dims = strides(A)
    msz, mst, n = merge_adjacent_dim(sz, st)
    mst == 1 || return invoke(read!, Tuple{IO, AbstractArray}, s, A; cancel=nothing)
    if n == ndims(A)
        GC.@preserve A unsafe_read(s, pointer(A), elsize(A) * length(A))
    else
        sz′, st′ = tail(sz), tail(st)
        while n > 1
            sz′ = (tail(sz′)..., 1)
            st′ = (tail(st′)..., 0)
            n -= 1
        end
        GC.@preserve A begin
            iter = CartesianIndices(sz′)
            for I in iter
                p = pointer(A)
                for i in 1:length(sz′)
                    p += elsize(A) * st′[i] * (I[i] - 1)
                end
                unsafe_read(s, p, elsize(A) * msz)
            end
        end
    end
    return A
end
```
-/
def readStridedArray {World Stream Array Pointer Token : Type}
    (cancellation : Cancellation World Token) (isBits : Bool)
    (contiguous : Array → M World Bool) (pointer : Array → M World Pointer)
    (elementSize arrayLength : Array → M World I)
    (unsafeRead : Stream → Pointer → I → M World Unit)
    (size strides : Array → M World (List I))
    (mergeAdjacentDim : List I → List I → M World (I × I × I))
    (readAbstractArray : Stream → Array → M World Array)
    (addPointer : Pointer → I → M World Pointer)
    (stream : Stream) (array : Array) (cancel : CancelArg Token) : M World Array := do
  let _ ← cancellation.check cancel
  if !isBits then return ← readAbstractArray stream array
  if ← contiguous array then return ← readAbstractArray stream array
  let sz ← size array
  let st ← strides array
  let (msz, mst, n) ← mergeAdjacentDim sz st
  if mst.val ≠ 1 then return ← readAbstractArray stream array
  if n.val = sz.length then
    unsafeRead stream (← pointer array) ((← elementSize array) * (← arrayLength array))
  else
    let (sz', st') ← writeStridedArray.stridedTails sz st n
    whileLoop (fun (index : Option (List I)) => do
      match index with
      | none => pure (.inl ())
      | some index => do
        let p ← writeStridedArray.stridedPointer (pointer array) (elementSize array) addPointer st' index
        unsafeRead stream p ((← elementSize array) * msz)
        pure (.inr (writeStridedArray.cartesianNext sz' index)))
      (writeStridedArray.cartesianFirst sz')
  pure array

-- UNTRANSLATED
-- Source: base/io.jl:1090-1090 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:1091-1106 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function read(io::IO, ::Type{Char})
    b0 = read(io, UInt8)::UInt8
    lo = UInt8(leading_ones(b0))
    c = UInt32(b0) << 24
    if 0x02 ≤ lo ≤ 0x04
        l = 0x08 * (0x04 - lo)
        s = 16
        while s ≥ l && !eof(io)::Bool
            peek(io) & 0xc0 == 0x80 || break
            b = read(io, UInt8)::UInt8
            c |= UInt32(b) << s
            s -= 8
        end
    end
    return reinterpret(Char, c)
end
```
-/
def readChar {World Stream : Type} (ops : Ops World Stream)
    (peek : Stream → M World Byte) (stream : Stream) : M World JuliaLean.base.char.JChar := do
  let first ← ops.readByte stream
  let leading := JInt.rem .u8 (JuliaLean.base.int.leading_ones_Integer
    JuliaLean.base.int.leading_zeros JuliaLean.base.int.bnot first)
  let word : JInt .u32 := JuliaLean.base.int.shl_int (JInt.rem .u32 first) (i 24)
  let word ← if 2 ≤ leading.val && leading.val ≤ 4 then do
    let limit : Byte := byte 8 * (byte 4 - leading)
    whileLoop (fun ((shift, word) : I × JInt .u32) => do
      if shift.val < limit.val then return .inl word
      if ← ops.eof stream then return .inl word
      let next ← peek stream
      if (JuliaLean.base.int.and_int next (byte 192)).val != 128 then return .inl word
      let value ← ops.readByte stream
      let word := JuliaLean.base.int.or_int word
        (JuliaLean.base.int.shl_int (JInt.rem .u32 value) shift)
      return .inr (shift - i 8, word)) (i 16, word)
    else pure word
  pure (UInt32.ofNat word.val.toNat)

-- UNTRANSLATED
-- Source: base/io.jl:1107-1109 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # read(io, T) is not defined for other AbstractChar: implementations
-- # must provide their own encoding-specific method.
-- 
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:1110-1124 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copyuntil(out::IO, s::IO, delim::AbstractChar; keep::Bool=false, cancel::CancelTokenArg=DEFAULT_CANCEL)
    if delim ≤ '\x7f'
        return cancel === DEFAULT_CANCEL ? copyuntil(out, s, delim % UInt8; keep) :
                                           copyuntil(out, s, delim % UInt8; keep, cancel)
    end
    check_cancel_arg(cancel)
    for c in readeach(s, Char)
        if c == delim
            keep && write(out, c)
            break
        end
        write(out, c)
    end
    return out
end
```
-/
def copyuntilChar {World Stream Out Char Delim Token : Type} (ops : Ops World Stream)
    (cancellation : Cancellation World Token)
    (atMostAscii : Delim → M World Bool) (toByte : Delim → M World Byte)
    (byteCopy : Out → Stream → Byte → Bool → CancelArg Token → M World Out)
    (readChar : Stream → M World Char) (equal : Char → Delim → M World Bool)
    (writeChar : Out → Char → M World I)
    (out : Out) (stream : Stream) (delim : Delim) (keep : Bool) (cancel : CancelArg Token) : M World Out := do
  if ← atMostAscii delim then return (← byteCopy out stream (← toByte delim) keep cancel)
  let _ ← cancellation.check cancel
  whileLoop (fun _ : Unit => do
    if ← ops.eof stream then return .inl out
    let character ← readChar stream
    if ← equal character delim then
      if keep then let _ ← writeChar out character
      return .inl out
    let _ ← writeChar out character
    return .inr ()) ()

-- UNTRANSLATED
-- Source: base/io.jl:1125-1127 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # note: optimized methods of copyuntil for IOStreams and delim::UInt8 in iostream.jl
-- #       and for IOBuffer with delim::UInt8 in iobuffer.jl
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:1128-1131 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copyuntil(out::IO, s::IO, delim; keep::Bool=false, cancel::CancelTokenArg=DEFAULT_CANCEL)
    check_cancel_arg(cancel)
    return _copyuntil(out, s, delim, keep)
end
```
-/
def copyuntil {World Stream Out Delim Token : Type}
    (cancellation : Cancellation World Token)
    (copy : Out → Stream → Delim → Bool → M World Out)
    (out : Out) (stream : Stream) (delim : Delim) (keep : Bool) (cancel : CancelArg Token) : M World Out := do
  let _ ← cancellation.check cancel
  copy out stream delim keep

-- UNTRANSLATED
-- Source: base/io.jl:1132-1133 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # supports out::Union{IO, AbstractVector} for use with both copyuntil & readuntil
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:1134-1144 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _copyuntil(out, s::IO, delim::T, keep::Bool) where T
    output! = isa(out, IO) ? write : push!
    for c in readeach(s, T)
        if c == delim
            keep && output!(out, c)
            break
        end
        output!(out, c)
    end
    return out
end
```
-/
def copyuntilCore {World Stream Out Delim : Type} (ops : Ops World Stream)
    (read : Stream → M World Delim) (equal : Delim → Delim → M World Bool)
    (output : Out → Delim → M World Unit)
    (out : Out) (stream : Stream) (delim : Delim) (keep : Bool) : M World Out :=
  whileLoop (fun _ : Unit => do
    if ← ops.eof stream then return .inl out
    let value ← read stream
    if ← equal value delim then
      if keep then output out value
      return .inl out
    output out value
    return .inr ()) ()

-- UNTRANSLATED
-- Source: base/io.jl:1145-1160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # requires that indices for target are the integer unit range from firstindex to lastindex
-- # returns whether the delimiter was matched
-- # uses the Knuth–Morris–Pratt_algorithm, with the first and second cache entries unrolled
-- # For longer targets, the cache improves the big-O efficiency of scanning of sequences
-- # with repeated patterns
-- # Each cache entry tells us which index we should start the search at.
-- # We assume this is unlikely, so we only lazy-initialize as much of the cache as we need to use
-- # When we allocate the cache, we initialize it to 0 (and offset by the first index afterwards).
-- # Suppose target is:
-- #    Index:  1245689
-- #    Value: "aδcaδcx"
-- # We would set the cache to
-- #    0 0 0 1 2 3 4 0
-- # So after if we mismatch after the second aδc sequence,
-- # we can immediately jump back to index 5 (4 + 1).
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:1161-1230 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function readuntil_vector!(io::IO, target::AbstractVector{T}, keep::Bool, out) where {T}
    first = firstindex(target)
    last = lastindex(target)
    len = last - first + 1
    if len < 1
        return true
    end
    pos = 0 # array-offset
    max_pos = 1 # array-offset in cache
    local cache # will be lazy initialized when needed
    output! = (isa(out, IO) ? write : push!)
    for c in readeach(io, T)
        # Backtrack until the next target character matches what was found
        while true
            c1 = target[pos + first]
            if c == c1
                pos += 1
                break
            elseif pos == 0
                break
            elseif pos == 1
                if !keep
                    output!(out, target[first])
                end
                pos = 0
            else
                # grow cache to contain up to `pos`
                if !@isdefined(cache)
                    cache = zeros(Int, len)
                end
                while max_pos < pos
                    ci = target[max_pos + first]
                    b = max_pos
                    max_pos += 1
                    while b != 0
                        b = cache[b]
                        cb = target[b + first]
                        if ci == cb
                            cache[max_pos] = b + 1
                            break
                        end
                    end
                end
                # read new position from cache
                pos1 = cache[pos]
                if !keep
                    # and add the removed prefix from the target to the output
                    # if not always keeping the match
                    for b in 1:(pos - pos1)
                        output!(out, target[b - 1 + first])
                    end
                end
                pos = pos1
            end
        end
        if keep || pos == 0
            output!(out, c)
        end
        pos == len && return true
    end
    if !keep
        # failed early without finishing the match,
        # add the partial match to the output
        # if not always keeping the match
        for b in 1:pos
            output!(out, target[b - 1 + first])
        end
    end
    return false
end
```
-/
def readuntilVectorBang {World Stream Target A Out : Type} (ops : Ops World Stream)
    (read : Stream → M World A) (eq : A → A → M World Bool)
    (firstindex lastindex : Target → M World I) (getindex : Target → I → M World A)
    (output : Out → A → M World Unit)
    (stream : Stream) (target : Target) (keep : Bool) (out : Out) : M World Bool := do
  let first ← firstindex target
  let last ← lastindex target
  let len := last - first + i 1
  if len.val < 1 then return true
  -- `for b in 1:count; output!(out, target[b - 1 + first]); end`
  let outputPrefix (count : I) : M World Unit :=
    if count.val < 1 then pure ()
    else whileLoop (fun b : I => do
      output out (← getindex target (b - i 1 + first))
      if b.val = count.val then pure (.inl ()) else pure (.inr (b + i 1))) (i 1)
  -- the `while true` backtracking loop for the read element `c`
  let backtrack (c : A) (state : I × I × Option (List I)) :
      M World (Sum (I × I × Option (List I)) (I × I × Option (List I))) := do
    let (pos, maxPos, cache) := state
    let c1 ← getindex target (pos + first)
    if ← eq c c1 then return .inl (pos + i 1, maxPos, cache)
    if pos.val = 0 then return .inl (pos, maxPos, cache)
    if pos.val = 1 then
      if !keep then output out (← getindex target first)
      return .inr (i 0, maxPos, cache)
    -- `cache = zeros(Int, len)` unless already defined
    let cache := cache.getD (List.replicate len.val.toNat (i 0))
    let (maxPos, cache) ← whileLoop (fun ((maxPos, cache) : I × List I) => do
      if !(maxPos.val < pos.val) then return .inl (maxPos, cache)
      let ci ← getindex target (maxPos + first)
      let b := maxPos
      let maxPos := maxPos + i 1
      let cache ← whileLoop (fun ((b, cache) : I × List I) => do
        if b.val = 0 then return .inl cache
        let b ← cacheGet cache b
        let cb ← getindex target (b + first)
        if ← eq ci cb then return .inl (← cacheSet cache maxPos (b + i 1))
        return .inr (b, cache)) (b, cache)
      return .inr (maxPos, cache)) (maxPos, cache)
    let pos1 ← cacheGet cache pos
    if !keep then outputPrefix (pos - pos1)
    return .inr (pos1, maxPos, some cache)
  -- the `for c in readeach(io, T)` loop: `iterate` is `eof(io) ? nothing : (read(io, T), nothing)`
  whileLoop (fun ((pos, maxPos, cache) : I × I × Option (List I)) => do
    if ← ops.eof stream then
      if !keep then outputPrefix pos
      return .inl false
    let c ← read stream
    let (pos, maxPos, cache) ← whileLoop (backtrack c) (pos, maxPos, cache)
    if keep || pos.val = 0 then output out c
    if pos.val = len.val then return .inl true
    return .inr (pos, maxPos, cache)) (i 0, i 1, none)
where
  /-- `cache[b]` of the `Vector{Int}` cache. -/
  cacheGet (cache : List I) (b : I) : M World I :=
    if 1 ≤ b.val ∧ b.val ≤ cache.length then pure (cache.getD (b.val - 1).toNat (i 0))
    else throw (.jl .boundsError)
  /-- `cache[b] = v`. -/
  cacheSet (cache : List I) (b v : I) : M World (List I) :=
    if 1 ≤ b.val ∧ b.val ≤ cache.length then pure (cache.set (b.val - 1).toNat v)
    else throw (.jl .boundsError)

-- UNTRANSLATED
-- Source: base/io.jl:1231-1231 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:1232-1248 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copyuntil(out::IO, io::IO, target::AbstractString; keep::Bool=false, cancel::CancelTokenArg=DEFAULT_CANCEL)
    # small-string target optimizations
    x = Iterators.peel(target)
    isnothing(x) && return out
    c, rest = x
    if isempty(rest) && c <= '\x7f'
        return cancel === DEFAULT_CANCEL ? copyuntil(out, io, c % UInt8; keep) :
                                           copyuntil(out, io, c % UInt8; keep, cancel)
    end
    # convert String to a utf8-byte-iterator
    if !(target isa String) && !(target isa SubString{String})
        target = String(target)
    end
    target = codeunits(target)::AbstractVector
    return cancel === DEFAULT_CANCEL ? copyuntil(out, io, target; keep) :
                                       copyuntil(out, io, target; keep, cancel)
end
```
-/
def copyuntilString {World Stream Out Text Char Rest Vector Token : Type}
    (peel : Text → M World (Option (Char × Rest))) (empty : Rest → M World Bool)
    (atMostAscii : Char → M World Bool) (toByte : Char → M World Byte)
    (byteCopy : Out → Stream → Byte → Bool → CancelArg Token → M World Out)
    (isConcrete : Text → Bool) (toString : Text → M World Text)
    (codeunits : Text → M World Vector)
    (vectorCopy : Out → Stream → Vector → Bool → CancelArg Token → M World Out)
    (out : Out) (stream : Stream) (target : Text) (keep : Bool) (cancel : CancelArg Token) : M World Out := do
  match ← peel target with
  | none => pure out
  | some (character, rest) => do
    if ← empty rest then
      if ← atMostAscii character then return (← byteCopy out stream (← toByte character) keep cancel)
    let target ← if isConcrete target then pure target else toString target
    let target ← codeunits target
    vectorCopy out stream target keep cancel

-- UNTRANSLATED
-- Source: base/io.jl:1249-1252 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # like the vector copyuntil below: without the `cancel` keyword here, a
-- # keyword call would bypass this method for the scalar-delimiter catch-all
-- # above (keyword dispatch only sees keyword-accepting methods)
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:1253-1260 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function readuntil(io::IO, target::AbstractVector{T}; keep::Bool=false,
                   cancel::CancelTokenArg=DEFAULT_CANCEL) where T
    # entry gate only (generic-IO cancel convention)
    check_cancel_arg(cancel)
    out = (T === UInt8 ? resize!(StringVector(16), 0) : Vector{T}())
    readuntil_vector!(io, target, keep, out)
    return out
end
```
-/
def readuntilVector {World Stream Target Out Token : Type}
    (cancellation : Cancellation World Token) (byteElements : Bool)
    (newStringVector : I → M World Out) (resize : Out → I → M World Out)
    (newVector : M World Out)
    (readuntilVector : Stream → Target → Bool → Out → M World Bool)
    (stream : Stream) (target : Target) (keep : Bool) (cancel : CancelArg Token) : M World Out := do
  let _ ← cancellation.check cancel
  let out ← if byteElements then resize (← newStringVector (i 16)) (i 0) else newVector
  let _ ← readuntilVector stream target keep out
  pure out

/--
Julia source: base/io.jl:1261-1267 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copyuntil(out::IO, io::IO, target::AbstractVector; keep::Bool=false, cancel::CancelTokenArg=DEFAULT_CANCEL)
    # entry gate only, ahead of readuntil_vector!'s generic reads
    # (generic-IO cancel convention)
    check_cancel_arg(cancel)
    readuntil_vector!(io, target, keep, out)
    return out
end
```
-/
def copyuntilVector {World Stream Target Out Token : Type}
    (cancellation : Cancellation World Token)
    (readuntilVector : Stream → Target → Bool → Out → M World Bool)
    (out : Out) (stream : Stream) (target : Target) (keep : Bool) (cancel : CancelArg Token) : M World Out := do
  let _ ← cancellation.check cancel
  let _ ← readuntilVector stream target keep out
  pure out

-- UNTRANSLATED
-- Source: base/io.jl:1268-1284 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     readchomp(x)
-- 
-- Read the entirety of `x` as a string and remove a single trailing newline
-- if there is one. Equivalent to `chomp(read(x, String))`.
-- 
-- # Examples
-- ```jldoctest
-- julia> write("my_file.txt", "JuliaLang is a GitHub organization.\\nIt has many members.\\n");
-- 
-- julia> readchomp("my_file.txt")
-- "JuliaLang is a GitHub organization.\\nIt has many members."
-- 
-- julia> rm("my_file.txt");
-- ```
-- """
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:1285-1290 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function readchomp(x; cancel::CancelTokenArg=DEFAULT_CANCEL)
    # `x` may be anything readable (a stream, file name, command): entry
    # gate only (generic-IO cancel convention)
    check_cancel_arg(cancel)
    return chomp(read(x, String))
end
```
-/
def readchomp {World Input Text Token : Type} (cancellation : Cancellation World Token)
    (read : Input → M World Text) (chomp : Text → M World Text)
    (input : Input) (cancel : CancelArg Token) : M World Text := do
  let _ ← cancellation.check cancel
  chomp (← read input)

-- UNTRANSLATED
-- Source: base/io.jl:1291-1300 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # read up to nb bytes into nb, returning # bytes read
-- 
-- """
--     readbytes!(stream::IO, b::AbstractVector{UInt8}, nb=length(b))
-- 
-- Read at most `nb` bytes from `stream` into `b`, returning the number of bytes read.
-- The size of `b` will be increased if needed (i.e. if `nb` is greater than `length(b)`
-- and enough bytes could be read), but it will never be decreased.
-- """
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:1301-1319 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function readbytes!(s::IO, b::AbstractArray{UInt8}, nb=length(b); cancel::CancelTokenArg=DEFAULT_CANCEL)
    check_cancel_arg(cancel)
    require_one_based_indexing(b)
    olb = lb = length(b)
    nr = 0
    while nr < nb && !eof(s)
        a = read(s, UInt8)
        nr += 1
        if nr > lb
            lb = nr * 2
            resize!(b, lb)
        end
        b[nr] = a
    end
    if lb > olb
        resize!(b, nr) # shrink to just contain input data if was resized
    end
    return nr
end
```
-/
def readbytes {World Stream Array Count Token : Type} (ops : Ops World Stream)
    (cancellation : Cancellation World Token) (requireOneBased : Array → M World Unit)
    (length : Array → M World I) (lessCount : I → Count → M World Bool)
    (resize : Array → I → M World Unit) (set : Array → I → Byte → M World Unit)
    (stream : Stream) (array : Array) (count : Count) (cancel : CancelArg Token) : M World I := do
  let _ ← cancellation.check cancel
  requireOneBased array
  let originalLength ← length array
  let (readCount, bufferLength) ← whileLoop (fun ((readCount, bufferLength) : I × I) => do
    if !(← lessCount readCount count) then return .inl (readCount, bufferLength)
    if ← ops.eof stream then return .inl (readCount, bufferLength)
    let value ← ops.readByte stream
    let readCount := readCount + i 1
    let bufferLength ← if readCount.val > bufferLength.val then do
      let bufferLength := readCount * i 2
      resize array bufferLength
      pure bufferLength
      else pure bufferLength
    set array readCount value
    return .inr (readCount, bufferLength)) (i 0, originalLength)
  if bufferLength.val > originalLength.val then resize array readCount
  pure readCount

-- UNTRANSLATED
-- Source: base/io.jl:1320-1325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     read(s::IO, nb=typemax(Int))
-- 
-- Read at most `nb` bytes from `s`, returning a `Vector{UInt8}` of the bytes read.
-- """
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:1326-1335 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function read(s::IO, nb::Integer = typemax(Int); cancel::CancelTokenArg=DEFAULT_CANCEL)
    # Let readbytes! grow the array progressively by default
    # instead of taking the risk of over-allocating
    b = Vector{UInt8}(undef, nb == typemax(Int) ? 1024 : nb)
    # an explicit token is forwarded to readbytes! (whose Base methods all
    # accept it); the default sentinel keeps the plain call, which any
    # user-defined readbytes! method supports
    nr = cancel === DEFAULT_CANCEL ? readbytes!(s, b, nb) : readbytes!(s, b, nb; cancel)
    return resize!(b, nr)
end
```
-/
def readCount {World Stream Count Array Token : Type}
    (isTypemax : Count → M World Bool) (allocate : Sum I Count → M World Array)
    (plain : Stream → Array → Count → M World I)
    (explicit : Stream → Array → Count → Option Token → M World I)
    (resize : Array → I → M World Array)
    (stream : Stream) (count : Count) (cancel : CancelArg Token) : M World Array := do
  let size ← if ← isTypemax count then pure (Sum.inl (i 1024)) else pure (Sum.inr count)
  let buffer ← allocate size
  let readCount ← match cancel with
    | .default => plain stream buffer count
    | .explicit token => explicit stream buffer count token
  resize buffer readCount

-- UNTRANSLATED
-- Source: base/io.jl:1336-1336 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:1337-1344 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function read(s::IO, ::Type{String}; cancel::CancelTokenArg=DEFAULT_CANCEL)
    # thread the token (or an explicit `nothing` shield) into the inner
    # read, which does the actual blocking; the sentinel keeps the plain
    # call, which any user-defined `read` method supports
    cancel === DEFAULT_CANCEL && return String(read(s)::Vector{UInt8})
    cancel = check_cancel_arg(cancel)
    return String(read(s; cancel)::Vector{UInt8})
end
```
-/
def readString {World Stream Array Text Token : Type}
    (cancellation : Cancellation World Token)
    (plain : Stream → M World Array)
    (explicit : Stream → CancelArg Token → M World Array)
    (string : Array → M World Text)
    (stream : Stream) (cancel : CancelArg Token) : M World Text := do
  match cancel with
  | .default => string (← plain stream)
  | .explicit _ =>
    let cancel ← cancellation.check cancel
    string (← explicit stream cancel)

/--
Julia source: base/io.jl:1345-1345 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
read(s::IO, T::Type) = error("The IO stream does not support reading objects of type $T.")
```
-/
def readTypeFallback {World Stream A : Type} (typeName : String) (_stream : Stream) : M World A :=
  throw (.errorException ("The IO stream does not support reading objects of type " ++ typeName ++ "."))

-- UNTRANSLATED
-- Source: base/io.jl:1346-1348 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- ## high-level iterator interfaces ##
-- 
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:1349-1357 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct EachLine{IOT <: IO}
    stream::IOT
    ondone::Function
    keep::Bool
    cancel::CancelTokenArg
    EachLine(stream::IO=stdin; ondone::Function=()->nothing, keep::Bool=false,
             cancel::CancelTokenArg=DEFAULT_CANCEL) =
        new{typeof(stream)}(stream, ondone, keep, cancel)
end
```
-/
structure EachLine (World Stream Token : Type) where
  stream : Stream
  ondone : M World Unit
  keep : Bool
  cancel : CancelArg Token

/--
Julia source: base/io.jl:1354-1356 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    EachLine(stream::IO=stdin; ondone::Function=()->nothing, keep::Bool=false,
             cancel::CancelTokenArg=DEFAULT_CANCEL) =
        new{typeof(stream)}(stream, ondone, keep, cancel)
```
-/
def newEachLine {World Stream Token : Type} (stream : Stream)
    (ondone : M World Unit := pure ()) (keep : Bool := false)
    (cancel : CancelArg Token := .default) : EachLine World Stream Token :=
  ⟨stream, ondone, keep, cancel⟩

-- UNTRANSLATED
-- Source: base/io.jl:1358-1391 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     eachline(io::IO=stdin; keep::Bool=false)
--     eachline(filename::AbstractString; keep::Bool=false)
-- 
-- Create an iterable `EachLine` object that will yield each line from an I/O stream
-- or a file. Iteration calls [`readline`](@ref) on the stream argument repeatedly with
-- `keep` passed through, determining whether trailing end-of-line characters are
-- retained. When called with a file name, the file is opened once at the beginning of
-- iteration and closed at the end. If iteration is interrupted, the file will be
-- closed when the `EachLine` object is garbage collected.
-- 
-- To iterate over each line of a `String`, `eachline(IOBuffer(str))` can be used.
-- 
-- [`Iterators.reverse`](@ref) can be used on an `EachLine` object to read the lines
-- in reverse order (for files, buffers, and other I/O streams supporting [`seek`](@ref)),
-- and [`first`](@ref) or [`last`](@ref) can be used to extract the initial or final
-- lines, respectively.
-- 
-- # Examples
-- ```jldoctest
-- julia> write("my_file.txt", "JuliaLang is a GitHub organization.\\n It has many members.\\n");
-- 
-- julia> for line in eachline("my_file.txt")
--            print(line)
--        end
-- JuliaLang is a GitHub organization. It has many members.
-- 
-- julia> rm("my_file.txt");
-- ```
-- 
-- !!! compat "Julia 1.8"
--        Julia 1.8 is required to use `Iterators.reverse` or `last` with `eachline` iterators.
-- """
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:1392-1394 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function eachline(stream::IO=stdin; keep::Bool=false, cancel::CancelTokenArg=DEFAULT_CANCEL)
    EachLine(stream; keep, cancel)::EachLine
end
```
-/
def eachline {World Stream Token : Type} (stream : Stream)
    (keep : Bool := false) (cancel : CancelArg Token := .default) : EachLine World Stream Token :=
  ⟨stream, pure (), keep, cancel⟩

-- UNTRANSLATED
-- Source: base/io.jl:1395-1395 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:1396-1399 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function eachline(filename::AbstractString; keep::Bool=false, cancel::CancelTokenArg=DEFAULT_CANCEL)
    s = open(filename)
    EachLine(s; ondone=()->close(s), keep, cancel)::EachLine
end
```
-/
def eachlineFilename {World Stream Filename Token : Type}
    (openIO : Filename → M World Stream) (close : Stream → M World Unit)
    (filename : Filename) (keep : Bool := false) (cancel : CancelArg Token := .default) :
    M World (EachLine World Stream Token) := do
  let stream ← openIO filename
  pure ⟨stream, close stream, keep, cancel⟩

-- UNTRANSLATED
-- Source: base/io.jl:1400-1400 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:1401-1409 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(itr::EachLine, state=nothing)
    # token-gate between lines (generic-IO cancel convention)
    cancel = itr.cancel
    check_cancel_arg(cancel)
    eof(itr.stream) && return (itr.ondone(); nothing)
    line = cancel === DEFAULT_CANCEL ? readline(itr.stream; keep=itr.keep) :
                                       readline(itr.stream; keep=itr.keep, cancel)
    (line, nothing)
end
```
-/
def iterateEachLine {World Stream Text Token : Type} (ops : Ops World Stream)
    (cancellation : Cancellation World Token)
    (plain : Stream → Bool → M World Text)
    (explicit : Stream → Bool → Option Token → M World Text)
    (iterator : EachLine World Stream Token) (_state : Unit := ()) : M World (Option (Text × Unit)) := do
  let cancel := iterator.cancel
  let _ ← cancellation.check cancel
  if ← ops.eof iterator.stream then
    iterator.ondone
    return none
  let line ← match cancel with
    | .default => plain iterator.stream iterator.keep
    | .explicit token => explicit iterator.stream iterator.keep token
  pure (some (line, ()))

-- UNTRANSLATED
-- Source: base/io.jl:1410-1410 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:1411-1411 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{<:EachLine}) = String
```
-/
def eachLineEltype : Type := JuliaLean.base.strings.string.JString

-- UNTRANSLATED
-- Source: base/io.jl:1412-1412 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:1413-1413 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorSize(::Type{<:EachLine}) = SizeUnknown()
```
-/
inductive IteratorSize where
  | unknown
  deriving DecidableEq

/--
Julia source: base/io.jl:1413-1413 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorSize(::Type{<:EachLine}) = SizeUnknown()
```
-/
def eachLineIteratorSize : IteratorSize := .unknown

-- UNTRANSLATED
-- Source: base/io.jl:1414-1414 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:1415-1415 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isdone(itr::EachLine, state...) = eof(itr.stream)
```
-/
def eachLineIsdone {World Stream Token State : Type} (ops : Ops World Stream)
    (iterator : EachLine World Stream Token) (_states : State) : M World Bool :=
  ops.eof iterator.stream
/-- The `Vector{Vector{UInt8}}` chunk buffer and `IOBuffer` operations used by reverse `EachLine`
iteration. `Chunks` is the circular vector of chunks and `Chunk` one `Vector{UInt8}`; both are
mutable objects of the world, so a mutation through one reference is seen through every other. -/
structure ReverseChunkOps (World Stream Chunks Chunk Buffer Text : Type) where
  /-- `empty!(Vector{Vector{UInt8}}(undef, 2))`. -/
  newChunks : M World Chunks
  /-- `Vector{UInt8}(undef, n)`. -/
  newChunk : I → M World Chunk
  /-- `length(chunk)`. -/
  chunkLength : Chunk → M World I
  /-- `chunk[k]`, with its `BoundsError`. -/
  chunkGet : Chunk → I → M World Byte
  /-- `resize!(chunk, n)`. -/
  chunkResize : Chunk → I → M World Unit
  /-- `length(chunks)`. -/
  chunksLength : Chunks → M World I
  /-- `chunks[k]`, with its `BoundsError`. -/
  chunksGet : Chunks → I → M World Chunk
  /-- `pushfirst!(chunks, chunk)`. -/
  chunksPushfirst : Chunks → Chunk → M World Unit
  /-- `insert!(chunks, k, chunk)`. -/
  chunksInsert : Chunks → I → Chunk → M World Unit
  /-- `empty!(chunks)`. -/
  chunksEmpty : Chunks → M World Unit
  /-- `isempty(chunks)`. -/
  chunksIsempty : Chunks → M World Bool
  /-- `readbytes!(stream, chunk)`. -/
  readbytes : Stream → Chunk → M World I
  /-- `IOBuffer(sizehint = n)`. -/
  newBuffer : I → M World Buffer
  /-- `write(buf, chunk)`. -/
  writeChunk : Buffer → Chunk → M World I
  /-- `write(buf, view(chunk, lo:hi))`, with the `BoundsError` of the view. -/
  writeView : Buffer → Chunk → I → I → M World I
  /-- `buf.size`. -/
  bufferSize : Buffer → M World I
  /-- `buf.size = n`. -/
  setBufferSize : Buffer → I → M World Unit
  /-- `buf.data[k]`, with its `BoundsError`. -/
  bufferByte : Buffer → I → M World Byte
  /-- `unsafe_takestring!(buf)`. -/
  takestring : Buffer → M World Text
  /-- `String(view(chunk, lo:hi))`, with the `BoundsError` of the view. -/
  viewString : Chunk → I → I → M World Text

/-- The state named tuple `(; p0, p, chunks, ichunk, inewline, jchunk, jnewline)`. -/
structure ReverseEachLineState (Chunks : Type) where
  p0 : I
  p : I
  chunks : Chunks
  ichunk : I
  inewline : I
  jchunk : I
  jnewline : I

/-- `something(findprev(==(UInt8('\n')), chunk, start), 0)` (array.jl `findprev(testf, A, start)`:
`nothing` for `start < 1`, otherwise `chunk[k]` is read for `k = start, start-1, ..., 1`,
each read with its `BoundsError`). `findlast` is `findprev` from `length(chunk)`. -/
def reverseFindprevNewline {World Stream Chunks Chunk Buffer Text : Type}
    (co : ReverseChunkOps World Stream Chunks Chunk Buffer Text) (chunk : Chunk) (start : I) :
    M World I :=
  whileLoop (fun (k : I) => do
    if k.val < 1 then return .inl (i 0)
    if (← co.chunkGet chunk k).val = 10 then return .inl k
    pure (.inr (k - i 1))) start

/-- `something(findlast(==(UInt8('\n')), chunk), 0)`. -/
def reverseFindlastNewline {World Stream Chunks Chunk Buffer Text : Type}
    (co : ReverseChunkOps World Stream Chunks Chunk Buffer Text) (chunk : Chunk) : M World I := do
  reverseFindprevNewline co chunk (← co.chunkLength chunk)

/-- `min(4096, p - p0)`. -/
def reverseChunkSize (p p0 : I) : I :=
  let d := p - p0
  if (i 4096).val ≤ d.val then i 4096 else d

/-- `_stripnewline(keep, pos, data)`, the local function of the second `iterate` method: strip
`\n` or `\r\n` from `data[pos]` by decrementing `pos`. -/
def reverseStripnewline {World : Type} (data : I → M World Byte) (keep : Bool) (pos : I) :
    M World I := do
  if !keep && decide (0 < pos.val) then
    if (← data pos).val = 10 then
      let pos := pos - i 1
      let cr ← if decide (0 < pos.val) then (do pure (decide ((← data pos).val = 13))) else pure false
      return if cr then pos - i 1 else pos
  return pos

-- UNTRANSLATED
-- Source: base/io.jl:1416-1418 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Reverse-order iteration for the EachLine iterator for seekable streams,
-- # which works by reading the stream from the end in 4kiB chunks.
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

mutual
/--
Julia source: base/io.jl:1419-1439 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(r::Iterators.Reverse{<:EachLine})
    p0 = position(r.itr.stream)
    seekend(r.itr.stream) # may throw if io is non-seekable
    p = position(r.itr.stream)
    # chunks = circular buffer of 4kiB blocks read from end of stream
    chunks = empty!(Vector{Vector{UInt8}}(undef, 2)) # allocate space for 2 buffers (common case)
    inewline = jnewline = 0
    while p > p0 && inewline == 0 # read chunks until we find a newline or we read whole file
        chunk = Vector{UInt8}(undef, min(4096, p-p0))
        p -= length(chunk)
        readbytes!(seek(r.itr.stream, p), chunk)
        pushfirst!(chunks, chunk)
        inewline = something(findlast(==(UInt8('\n')), chunk), 0)
        if length(chunks) == 1 && inewline == length(chunks[1])
            # found newline at end of file … keep looking
            jnewline = inewline
            inewline = something(findprev(==(UInt8('\n')), chunk, inewline-1), 0)
        end
    end
    return iterate(r, (; p0, p, chunks, ichunk=1, inewline, jchunk=length(chunks), jnewline = jnewline == 0 && !isempty(chunks) ? length(chunks[end]) : jnewline))
end
```
-/
def reverseEachLineIterate {World Stream Token Chunks Chunk Buffer Text : Type}
    (ops : Ops World Stream) (co : ReverseChunkOps World Stream Chunks Chunk Buffer Text)
    (iterator : EachLine World Stream Token) :
    M World (Option (Text × ReverseEachLineState Chunks)) := do
  let p0 ← ops.position iterator.stream
  ops.seekend iterator.stream
  let p ← ops.position iterator.stream
  let chunks ← co.newChunks
  -- `while p > p0 && inewline == 0`, with state `(p, inewline, jnewline)`
  let (p, inewline, jnewline) ← whileLoop (fun ((p, inewline, jnewline) : I × I × I) => do
    if !(decide (p0.val < p.val) && inewline.val = 0) then return .inl (p, inewline, jnewline)
    let chunk ← co.newChunk (reverseChunkSize p p0)
    let p := p - (← co.chunkLength chunk)
    ops.seek iterator.stream p
    let _ ← co.readbytes iterator.stream chunk
    co.chunksPushfirst chunks chunk
    let inewline ← reverseFindlastNewline co chunk
    if (← co.chunksLength chunks).val = 1 then
      if inewline.val = (← co.chunkLength (← co.chunksGet chunks (i 1))).val then
        let jnewline := inewline
        let inewline ← reverseFindprevNewline co chunk (inewline - i 1)
        return .inr (p, inewline, jnewline)
    pure (.inr (p, inewline, jnewline))) (p, i 0, i 0)
  let jchunk ← co.chunksLength chunks
  let jnewline ←
    if jnewline.val = 0 && !(← co.chunksIsempty chunks) then do
      co.chunkLength (← co.chunksGet chunks (← co.chunksLength chunks))
    else pure jnewline
  reverseEachLineIterateState ops co iterator
    { p0, p, chunks, ichunk := i 1, inewline, jchunk, jnewline }

/--
Julia source: base/io.jl:1440-1519 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(r::Iterators.Reverse{<:EachLine}, state)
    function _stripnewline(keep, pos, data)
        # strip \n or \r\n from data[pos] by decrementing pos
        if !keep && pos > 0 && data[pos] == UInt8('\n')
            pos -= 1
            pos -= pos > 0 && data[pos] == UInt8('\r')
        end
        return pos
    end
    # state tuple: p0 = initial file position, p = current position,
    #              chunks = circular array of chunk buffers,
    #              current line is from chunks[ichunk][inewline+1] to chunks[jchunk][jnewline]
    p0, p, chunks, ichunk, inewline, jchunk, jnewline = state
    if inewline == 0 # no newline found, remaining line = rest of chunks (if any)
        isempty(chunks) && return (r.itr.ondone(); nothing)
        buf = IOBuffer(sizehint = ichunk==jchunk ? jnewline : 4096)
        while ichunk != jchunk
            write(buf, chunks[ichunk])
            ichunk = ichunk == length(chunks) ? 1 : ichunk + 1
        end
        chunk = chunks[jchunk]
        write(buf, view(chunk, 1:jnewline))
        buf.size = _stripnewline(r.itr.keep, buf.size, buf.data)
        empty!(chunks) # will cause next iteration to terminate
        seekend(r.itr.stream) # reposition to end of stream for isdone
        s = unsafe_takestring!(buf)
    else
        # extract the string from chunks[ichunk][inewline+1] to chunks[jchunk][jnewline]
        if ichunk == jchunk # common case: current and previous newline in same chunk
            chunk = chunks[ichunk]
            s = String(view(chunk, inewline+1:_stripnewline(r.itr.keep, jnewline, chunk)))
        else
            buf = IOBuffer(sizehint=max(128, length(chunks[ichunk])-inewline+jnewline))
            write(buf, view(chunks[ichunk], inewline+1:length(chunks[ichunk])))
            i = ichunk
            while true
                i = i == length(chunks) ? 1 : i + 1
                i == jchunk && break
                write(buf, chunks[i])
            end
            write(buf, view(chunks[jchunk], 1:jnewline))
            buf.size = _stripnewline(r.itr.keep, buf.size, buf.data)
            s = unsafe_takestring!(buf)

            # overwrite obsolete chunks (ichunk+1:jchunk)
            i = jchunk
            while i != ichunk
                chunk = chunks[i]
                p -= length(resize!(chunk, min(4096, p-p0)))
                readbytes!(seek(r.itr.stream, p), chunk)
                i = i == 1 ? length(chunks) : i - 1
            end
        end

        # find the newline previous to inewline
        jchunk = ichunk
        jnewline = inewline
        while true
            inewline = something(findprev(==(UInt8('\n')), chunks[ichunk], inewline-1), 0)
            inewline > 0 && break
            ichunk = ichunk == 1 ? length(chunks) : ichunk - 1
            ichunk == jchunk && break # found nothing — may need to read more chunks
            inewline = length(chunks[ichunk])+1 # start for next findprev
        end

        # read more chunks to look for a newline (should rarely happen)
        if inewline == 0 && p > p0
            ichunk = jchunk + 1
            while true
                chunk = Vector{UInt8}(undef, min(4096, p-p0))
                p -= length(chunk)
                readbytes!(seek(r.itr.stream, p), chunk)
                insert!(chunks, ichunk, chunk)
                inewline = something(findlast(==(UInt8('\n')), chunk), 0)
                (p == p0 || inewline > 0) && break
            end
        end
    end
    return (s, (; p0, p, chunks, ichunk, inewline, jchunk, jnewline))
end
```
-/
def reverseEachLineIterateState {World Stream Token Chunks Chunk Buffer Text : Type}
    (ops : Ops World Stream) (co : ReverseChunkOps World Stream Chunks Chunk Buffer Text)
    (iterator : EachLine World Stream Token) (state : ReverseEachLineState Chunks) :
    M World (Option (Text × ReverseEachLineState Chunks)) := do
  let { p0, p, chunks, ichunk, inewline, jchunk, jnewline } := state
  let next : I → M World I := fun k => do
    if k.val = (← co.chunksLength chunks).val then pure (i 1) else pure (k + i 1)
  let prev : I → M World I := fun k => do
    if k.val = 1 then co.chunksLength chunks else pure (k - i 1)
  if inewline.val = 0 then
    if ← co.chunksIsempty chunks then
      iterator.ondone
      return none
    let buf ← co.newBuffer (if ichunk.val = jchunk.val then jnewline else i 4096)
    let ichunk ← whileLoop (fun (ichunk : I) => do
      if ichunk.val = jchunk.val then return .inl ichunk
      let _ ← co.writeChunk buf (← co.chunksGet chunks ichunk)
      pure (.inr (← next ichunk))) ichunk
    let chunk ← co.chunksGet chunks jchunk
    let _ ← co.writeView buf chunk (i 1) jnewline
    co.setBufferSize buf
      (← reverseStripnewline (co.bufferByte buf) iterator.keep (← co.bufferSize buf))
    co.chunksEmpty chunks
    ops.seekend iterator.stream
    let s ← co.takestring buf
    return some (s, { p0, p, chunks, ichunk, inewline, jchunk, jnewline })
  -- extract the string from `chunks[ichunk][inewline+1]` to `chunks[jchunk][jnewline]`
  let (s, p) ← if ichunk.val = jchunk.val then do
      let chunk ← co.chunksGet chunks ichunk
      let lo := inewline + i 1
      let hi ← reverseStripnewline (co.chunkGet chunk) iterator.keep jnewline
      pure ((← co.viewString chunk lo hi), p)
    else do
      let first ← co.chunkLength (← co.chunksGet chunks ichunk)
      let hint := first - inewline + jnewline
      let buf ← co.newBuffer (if hint.val < 128 then i 128 else hint)
      let chunk ← co.chunksGet chunks ichunk
      let _ ← co.writeView buf chunk (inewline + i 1)
        (← co.chunkLength (← co.chunksGet chunks ichunk))
      whileLoop (fun (k : I) => do
        let k ← next k
        if k.val = jchunk.val then return .inl ()
        let _ ← co.writeChunk buf (← co.chunksGet chunks k)
        pure (.inr k)) ichunk
      let _ ← co.writeView buf (← co.chunksGet chunks jchunk) (i 1) jnewline
      co.setBufferSize buf
        (← reverseStripnewline (co.bufferByte buf) iterator.keep (← co.bufferSize buf))
      let s ← co.takestring buf
      -- overwrite obsolete chunks (`ichunk+1:jchunk`)
      let p ← whileLoop (fun ((k, p) : I × I) => do
        if k.val = ichunk.val then return .inl p
        let chunk ← co.chunksGet chunks k
        co.chunkResize chunk (reverseChunkSize p p0)
        let p := p - (← co.chunkLength chunk)
        ops.seek iterator.stream p
        let _ ← co.readbytes iterator.stream chunk
        pure (.inr ((← prev k), p))) (jchunk, p)
      pure (s, p)
  -- find the newline previous to `inewline`
  let jchunk := ichunk
  let jnewline := inewline
  let (ichunk, inewline) ← whileLoop (fun ((ichunk, inewline) : I × I) => do
    let inewline ← reverseFindprevNewline co (← co.chunksGet chunks ichunk) (inewline - i 1)
    if 0 < inewline.val then return .inl (ichunk, inewline)
    let ichunk ← prev ichunk
    if ichunk.val = jchunk.val then return .inl (ichunk, inewline)
    let inewline := (← co.chunkLength (← co.chunksGet chunks ichunk)) + i 1
    pure (.inr (ichunk, inewline))) (ichunk, inewline)
  -- read more chunks to look for a newline
  let (p, ichunk, inewline) ←
    if inewline.val = 0 && decide (p0.val < p.val) then do
      let ichunk := jchunk + i 1
      let (p, inewline) ← whileLoop (fun (p : I) => do
        let chunk ← co.newChunk (reverseChunkSize p p0)
        let p := p - (← co.chunkLength chunk)
        ops.seek iterator.stream p
        let _ ← co.readbytes iterator.stream chunk
        co.chunksInsert chunks ichunk chunk
        let inewline ← reverseFindlastNewline co chunk
        if p.val = p0.val || decide (0 < inewline.val) then return .inl (p, inewline)
        pure (.inr p)) p
      pure (p, ichunk, inewline)
    else pure (p, ichunk, inewline)
  return some (s, { p0, p, chunks, ichunk, inewline, jchunk, jnewline })
end

/--
Julia source: base/io.jl:1520-1520 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isdone(r::Iterators.Reverse{<:EachLine}, state) = isempty(state.chunks)
```
-/
def reverseEachLineIsdone {World State Chunks : Type}
    (chunks : State → Chunks) (empty : Chunks → M World Bool) (state : State) : M World Bool :=
  empty (chunks state)

/--
Julia source: base/io.jl:1521-1521 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isdone(r::Iterators.Reverse{<:EachLine}) = isdone(r.itr)
```
-/
def reverseEachLineIsdoneInitial {World Stream Token State : Type} (ops : Ops World Stream)
    (iterator : EachLine World Stream Token) (state : State) : M World Bool :=
  eachLineIsdone ops iterator state

-- UNTRANSLATED
-- Source: base/io.jl:1522-1523 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # use reverse iteration to get end of EachLines (if possible)
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:1524-1524 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
last(itr::EachLine) = first(Iterators.reverse(itr))
```
-/
def lastEachLine {World Iterator Reverse Text : Type}
    (reverse : Iterator → M World Reverse) (first : Reverse → M World Text)
    (iterator : Iterator) : M World Text := do first (← reverse iterator)

-- UNTRANSLATED
-- Source: base/io.jl:1525-1525 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:1526-1528 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct ReadEachIterator{T, IOT <: IO}
    stream::IOT
end
```
-/
structure ReadEachIterator (Stream : Type) (Element : Type readEachUniverse) where
  stream : Stream

inductive AnyValue : Type 1 where
  | pack {α : Type} (value : α) : AnyValue

-- UNTRANSLATED
-- Source: base/io.jl:1529-1550 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     readeach(io::IO, T)
-- 
-- Return an iterable object yielding [`read(io, T)`](@ref).
-- 
-- See also [`skipchars`](@ref), [`eachline`](@ref), [`readuntil`](@ref).
-- 
-- !!! compat "Julia 1.6"
--     `readeach` requires Julia 1.6 or later.
-- 
-- # Examples
-- ```jldoctest
-- julia> io = IOBuffer("JuliaLang is a GitHub organization.\\n It has many members.\\n");
-- 
-- julia> for c in readeach(io, Char)
--            c == '\\n' && break
--            print(c)
--        end
-- JuliaLang is a GitHub organization.
-- ```
-- """
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:1551-1551 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
readeach(stream::IOT, T::Type) where IOT<:IO = ReadEachIterator{T,IOT}(stream)
```
-/
def readeach {Stream : Type} (stream : Stream) (element : Type) : ReadEachIterator Stream element :=
  ⟨stream⟩

-- UNTRANSLATED
-- Source: base/io.jl:1552-1552 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:1553-1554 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(itr::ReadEachIterator{T}, state=nothing) where T =
    eof(itr.stream) ? nothing : (read(itr.stream, T), nothing)
```
-/
def iterateReadEach {World Stream Element : Type} (ops : Ops World Stream)
    (read : Stream → M World Element) (iterator : ReadEachIterator Stream Element)
    (_state : Unit := ()) : M World (Option (Element × Unit)) := do
  if ← ops.eof iterator.stream then pure none
  else pure (some (← read iterator.stream, ()))

-- UNTRANSLATED
-- Source: base/io.jl:1555-1555 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:1556-1556 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{<:ReadEachIterator{T}}) where {T} = T
```
-/
def readEachEltype {Stream Element : Type} (_iterator : ReadEachIterator Stream Element) : Type := Element

/--
Julia source: base/io.jl:1557-1557 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{ReadEachIterator}) = Any
```
-/
def readEachAnyEltype {Stream : Type} (_iterator : ReadEachIterator Stream AnyValue) : Type 1 :=
  AnyValue

-- UNTRANSLATED
-- Source: base/io.jl:1558-1558 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:1559-1559 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorSize(::Type{<:ReadEachIterator}) = SizeUnknown()
```
-/
def readEachIteratorSize : IteratorSize := .unknown

-- UNTRANSLATED
-- Source: base/io.jl:1560-1560 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:1561-1561 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isdone(itr::ReadEachIterator, state...) = eof(itr.stream)
```
-/
def readEachIsdone {World Stream Element State : Type} (ops : Ops World Stream)
    (iterator : ReadEachIterator Stream Element) (_states : State) : M World Bool :=
  ops.eof iterator.stream

-- UNTRANSLATED
-- Source: base/io.jl:1562-1574 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # IOStream Marking
-- # Note that these functions expect that io.mark exists for
-- # the concrete IO type. This may not be true for IO types
-- # not in base.
-- 
-- """
--     mark(s::IO)
-- 
-- Add a mark at the current position of stream `s`. Return the marked position.
-- 
-- See also [`unmark`](@ref), [`reset`](@ref), [`ismarked`](@ref).
-- """
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:1575-1577 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function mark(io::IO)
    io.mark = position(io)
end
```
-/
def mark {World Stream : Type} (ops : Ops World Stream) (stream : Stream) : M World I := do
  let position ← ops.position stream
  ops.setMark stream position
  pure position

-- UNTRANSLATED
-- Source: base/io.jl:1578-1585 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     unmark(s::IO)
-- 
-- Remove a mark from stream `s`. Return `true` if the stream was marked, `false` otherwise.
-- 
-- See also [`mark`](@ref), [`reset`](@ref), [`ismarked`](@ref).
-- """
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:1586-1590 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unmark(io::IO)
    !ismarked(io) && return false
    io.mark = -1
    return true
end
```
-/
def unmark {World Stream : Type} (ops : Ops World Stream) (stream : Stream) : M World Bool := do
  if (← ops.getMark stream).val < 0 then return false
  ops.setMark stream (i (-1))
  pure true

-- UNTRANSLATED
-- Source: base/io.jl:1591-1599 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     reset(s::IO)
-- 
-- Reset a stream `s` to a previously marked position, and remove the mark. Return the
-- previously marked position. Throw an error if the stream is not marked.
-- 
-- See also [`mark`](@ref), [`unmark`](@ref), [`ismarked`](@ref).
-- """
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:1600-1606 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function reset(io::T) where T<:IO
    ismarked(io) || throw(ArgumentError(LazyString(T, " not marked")))
    m = io.mark
    seek(io, m)
    io.mark = -1 # must be after seek, or seek may fail
    return m
end
```
-/
def reset {World Stream : Type} (ops : Ops World Stream)
    (typeName : Stream → String) (stream : Stream) : M World I := do
  if (← ops.getMark stream).val < 0 then throw (.jl (.argumentError (typeName stream ++ " not marked")))
  let marked ← ops.getMark stream
  ops.seek stream marked
  ops.setMark stream (i (-1))
  pure marked

-- UNTRANSLATED
-- Source: base/io.jl:1607-1614 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     ismarked(s::IO)
-- 
-- Return `true` if stream `s` is marked.
-- 
-- See also [`mark`](@ref), [`unmark`](@ref), [`reset`](@ref).
-- """
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:1615-1615 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ismarked(io::IO) = io.mark >= 0
```
-/
def ismarked {World Stream : Type} (ops : Ops World Stream) (stream : Stream) : M World Bool := do
  pure ((← ops.getMark stream).val ≥ 0)

-- UNTRANSLATED
-- Source: base/io.jl:1616-1619 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Make sure all IO streams support flush, even if only as a no-op,
-- # to make it easier to write generic I/O code.
-- 
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:1620-1620 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
flush(io::IO) = nothing
```
-/
def flush {World Stream : Type} (_stream : Stream) : M World Unit := pure ()

-- UNTRANSLATED
-- Source: base/io.jl:1621-1642 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     skipchars(predicate, io::IO; linecomment=nothing)
-- 
-- Advance the stream `io` such that the next-read character will be the first remaining for
-- which `predicate` returns `false`. If the keyword argument `linecomment` is specified, all
-- characters from that character until the start of the next line are ignored.
-- 
-- See also [`readuntil`](@ref).
-- 
-- # Examples
-- ```jldoctest
-- julia> buf = IOBuffer("    text")
-- IOBuffer(data=UInt8[...], readable=true, writable=false, seekable=true, append=false, size=8, maxsize=Inf, ptr=1, mark=-1)
-- 
-- julia> skipchars(isspace, buf)
-- IOBuffer(data=UInt8[...], readable=true, writable=false, seekable=true, append=false, size=8, maxsize=Inf, ptr=5, mark=-1)
-- 
-- julia> String(readavailable(buf))
-- "text"
-- ```
-- """
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:1643-1653 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function skipchars(predicate, io::IO; linecomment=nothing)
    for c in readeach(io, Char)
        if c === linecomment
            readline(io)
        elseif !predicate(c)
            skip(io, -ncodeunits(c))
            break
        end
    end
    return io
end
```
-/
def skipchars {World Stream Char Text : Type} (ops : Ops World Stream)
    (read : Stream → M World Char) (identical : Char → Option Char → M World Bool)
    (predicate : Char → M World Bool) (readline : Stream → M World Text)
    (ncodeunits : Char → M World I) (skip : Stream → I → M World Unit)
    (stream : Stream) (linecomment : Option Char := none) : M World Stream :=
  whileLoop (fun _ : Unit => do
    if ← ops.eof stream then return .inl stream
    let character ← read stream
    if ← identical character linecomment then
      let _ ← readline stream
    else if !(← predicate character) then
      skip stream (-(← ncodeunits character))
      return .inl stream
    return .inr ()) ()

-- UNTRANSLATED
-- Source: base/io.jl:1654-1699 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     countlines(io::IO; eol::AbstractChar = '\\n')
--     countlines(filename::AbstractString; eol::AbstractChar = '\\n')
-- 
-- Read `io` until the end of the stream/file and count the number of lines. To specify a file
-- pass the filename as the first argument. EOL markers other than `'\\n'` are supported by
-- passing them as the second argument.  The last non-empty line of `io` is counted even if it does not
-- end with the EOL, matching the length returned by [`eachline`](@ref) and [`readlines`](@ref).
-- 
-- To count lines of a `String`, `countlines(IOBuffer(str))` can be used.
-- 
-- # Examples
-- ```jldoctest
-- julia> io = IOBuffer("JuliaLang is a GitHub organization.\\n");
-- 
-- julia> countlines(io)
-- 1
-- 
-- julia> io = IOBuffer("JuliaLang is a GitHub organization.");
-- 
-- julia> countlines(io)
-- 1
-- 
-- julia> eof(io) # counting lines moves the file pointer
-- true
-- 
-- julia> io = IOBuffer("JuliaLang is a GitHub organization.");
-- 
-- julia> countlines(io, eol = '.')
-- 1
-- ```
-- ```jldoctest
-- julia> write("my_file.txt", "JuliaLang is a GitHub organization.\\n")
-- 36
-- 
-- julia> countlines("my_file.txt")
-- 1
-- 
-- julia> countlines("my_file.txt", eol = 'n')
-- 4
-- 
-- julia> rm("my_file.txt")
-- 
-- ```
-- """
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:1700-1715 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function countlines(io::IO; eol::AbstractChar='\n')
    isascii(eol) || throw(ArgumentError("only ASCII line terminators are supported"))
    aeol = UInt8(eol)
    a = Vector{UInt8}(undef, 8192)
    nl = nb = 0
    while !eof(io)
        nb = readbytes!(io, a)
        @simd for i=1:nb
            @inbounds nl += a[i] == aeol
        end
    end
    if nb > 0 && a[nb] != aeol
        nl += 1 # final line is not terminated with eol
    end
    nl
end
```
-/
def countlines {World Stream Char Array : Type} (ops : Ops World Stream)
    (isAscii : Char → M World Bool) (toByte : Char → M World Byte)
    (allocate : I → M World Array) (readbytes : Stream → Array → M World I)
    (get : Array → I → M World Byte) (stream : Stream) (eol : Char) : M World I := do
  if !(← isAscii eol) then throw (.jl (.argumentError "only ASCII line terminators are supported"))
  let eol ← toByte eol
  let array ← allocate (i 8192)
  let (lines, count) ← whileLoop (fun ((lines, _count) : I × I) => do
    if ← ops.eof stream then return .inl (lines, _count)
    let count ← readbytes stream array
    let mut lines := lines
    for index in List.range count.val.toNat do
      let value ← get array (i (index + 1))
      lines := lines + i (if value.val = eol.val then 1 else 0)
    return .inr (lines, count)) (i 0, i 0)
  if count.val > 0 then
    if (← get array count).val != eol.val then return lines + i 1
  pure lines

-- UNTRANSLATED
-- Source: base/io.jl:1716-1716 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, generic-function/type declarations, or dispatch metadata; no method body.

/--
Julia source: base/io.jl:1717-1717 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
countlines(f::AbstractString; eol::AbstractChar = '\n') = open(io->countlines(io, eol = eol), f)::Int
```
-/
def countlinesFilename {World Filename Stream Char : Type}
    (openIO : (Stream → M World I) → Filename → M World I)
    (countlines : Stream → Char → M World I) (filename : Filename) (eol : Char) : M World I :=
  openIO (fun stream => countlines stream eol) filename

end JuliaLean.base.io

/-!
Shared vocabulary of the `IOCov` area: the exceptions thrown by the I/O, path,
environment, libc, libdl and command files of Base, and small byte helpers.

Foreign calls (`ccall`) are modelled as function arguments: a model receives
the C function's result and mirrors the Julia code around it (argument
conversions, error checks, result conversions).
-/

namespace JuliaLean.IOCov

open JuliaLean

deriving instance DecidableEq for Except

/-- Exceptions raised by the modelled methods. -/
inductive Err where
  /-- An exception already in `JuliaLean.JlError` (`ArgumentError`, `InexactError`, ...). -/
  | jl (e : JlError)
  /-- `SystemError(prefix, errno)` from `systemerror(prefix, cond)`. -/
  | systemError (pfx : String)
  /-- `IOError` from `uv_error(prefix, rc)` / `Base.uv_error`. -/
  | uvError (pfx : String)
  /-- `EOFError()`. -/
  | eofError
  /-- `KeyError(k)`. -/
  | keyError (k : List UInt8)
  /-- `ErrorException(msg)` from `error(...)`. -/
  | errorException (msg : String)
  /-- `FieldError`: access to a field the type does not have. -/
  | fieldError (field : String)
  /-- `TypeError`. -/
  | typeError (ctx : String)
  /-- `MethodError(f, args)`. -/
  | methodError (f : String)
  deriving Repr, DecidableEq, Inhabited

abbrev R (α : Type) := Except Err α

/-- `throw(ArgumentError(msg))`. -/
def argErr {α} (msg : String) : R α := .error (.jl (.argumentError msg))

/-- `systemerror(p, cond)`: throws `SystemError(p)` when `cond` holds. -/
def systemerror (p : String) (cond : Bool) : R Unit :=
  if cond then .error (.systemError p) else .ok ()

/-- `Base.uv_error(p, rc)`: throws when the libuv return code is negative. -/
def uvError (p : String) (rc : Int) : R Unit :=
  if rc < 0 then .error (.uvError p) else .ok ()

/-- `T(x)` for a Julia integer type `T`: `InexactError` when `x` is out of range. -/
def toInt (t : IntTy) (x : Int) : R Int :=
  if t.min ≤ x ∧ x ≤ t.max then .ok x else .error (.jl (.inexactError t.name))

/-- `x % T` for a Julia integer type `T` (two's-complement wrap). -/
def wrapTo (t : IntTy) (x : Int) : Int := wrapInt t x

/-- A C string: `none` is `C_NULL`, `some bytes` the bytes before the NUL. -/
abbrev CStr := Option (List UInt8)

/-- `p == C_NULL ? "" : unsafe_string(p)`. -/
def cstrOrEmpty : CStr → List UInt8
  | none => []
  | some s => s


/-- Bytes of an ASCII string literal. -/
def bs (s : String) : List UInt8 := s.toList.map (fun c => c.toNat.toUInt8)


end JuliaLean.IOCov

namespace JuliaLean.Streams

open JuliaLean

inductive StreamKind where
  | ioStream
  | libuvStream
  | bufferStream
  deriving Repr, DecidableEq

inductive StreamStatus where
  | active
  | eof
  | closing
  | closed
  deriving Repr, DecidableEq

structure StreamM where
  kind : StreamKind
  status : StreamStatus
  buffer : List UInt8
  writable : Bool
  deriving Repr, DecidableEq

inductive StreamErr where
  | eofError
  | ioError
  | argumentError
  | invalidPointer
  | methodError
  deriving Repr, DecidableEq

abbrev SR (α : Type) := Except StreamErr α



structure DelimSplit where
  before : List UInt8
  found : Bool
  after : List UInt8
  deriving Repr, DecidableEq

/-- Split at the first delimiter, consuming it when present. -/
def splitUntil (delim : UInt8) : List UInt8 → DelimSplit
  | [] => ⟨[], false, []⟩
  | b :: bs =>
      if b == delim then ⟨[], true, bs⟩
      else
        let r := splitUntil delim bs
        ⟨b :: r.before, r.found, r.after⟩


def stripTrailingCR (bytes : List UInt8) : List UInt8 :=
  match bytes.reverse with
  | 13 :: rest => rest.reverse
  | _ => bytes

/-- `readline`, including CRLF removal, `base/io.jl:668-716` and
`base/iostream.jl:505-508`. -/
def readLine (s : StreamM) (keep : Bool) : SR (List UInt8 × StreamM) :=
  let r := splitUntil 10 s.buffer
  let bytes :=
    if keep && r.found then r.before ++ [10]
    else if r.found then stripTrailingCR r.before
    else r.before
  .ok (bytes, { s with buffer := r.after })




end JuliaLean.Streams

namespace JuliaLean.MissingChar

open JuliaLean.Strings (bswap32)

/-- `write(io, c::Char)`, `base/io.jl:973-980`: the bytes of `bswap(c)` from the
low end, stopping once the remaining bits are zero. Bound: 4 iterations. -/
def writeCharLoop : Nat → UInt32 → List UInt8
  | 0, _ => []
  | fuel + 1, u => u.toUInt8 :: (if u >>> 8 = 0 then [] else writeCharLoop fuel (u >>> 8))

def writeChar (c : UInt32) : List UInt8 := writeCharLoop 4 (bswap32 c)

end JuliaLean.MissingChar

namespace JuliaLean.IOCov.Io

open JuliaLean JuliaLean.IOCov

abbrev Bytes := List UInt8

structure St where
  pre : Bytes
  inp : Bytes
  mark : Int := -1
  out : Bytes := []
  seekable : Bool := true
  isopen : Bool := true
  deriving DecidableEq, Repr

/-- A stream whose unread contents are `b`. -/
def St.of (b : Bytes) : St := { pre := [], inp := b }

/-! ## Primitive operations of a concrete stream type -/

/-- `eof(s)`. -/
def eof (s : St) : Bool := s.inp.isEmpty
/-- `read(s, UInt8)` of a concrete type: `EOFError` at the end. -/
def readByte (s : St) : R (UInt8 × St) :=
  match s.inp with
  | [] => .error .eofError
  | b :: r => .ok (b, { s with pre := s.pre ++ [b], inp := r })
/-- `write(s, b::UInt8)` of a concrete type: appends `b`, returns 1. -/
def writeByte (s : St) (b : UInt8) : Nat × St := (1, { s with out := s.out ++ [b] })
/-- `position(s)`. -/
def position (s : St) : Nat := s.pre.length
/-- `seek(s, n)` of a concrete type (as for `IOBuffer`: allowed when seekable, or when
`n` is the mark of a marked stream). -/
def seek (s : St) (n : Nat) : R St :=
  if s.seekable || (s.mark ≥ 0 && (n : Int) = s.mark) then
    let all := s.pre ++ s.inp
    .ok { s with pre := all.take n, inp := all.drop n }
  else argErr "seek failed, IOBuffer is not seekable and is not marked"
/-- `skip(s, n) = seek(s, position(s) + n)`. -/
def skip (s : St) (n : Int) : R St := seek s ((position s : Int) + n).toNat
/-- `close(s)`. -/
def close (s : St) : St := { s with isopen := false }

/-! ## Exceptions and trivial methods, lines 25-48 -/

/-- `struct SystemError`, lines 25-31: `prefix`, `errnum`, `extrainfo`. -/
structure SystemErrorM where
  pfx : String
  errnum : Int
  extrainfo : Option String
  deriving DecidableEq, Repr

/-- `SystemError(p, e, extrainfo)`, line 28 (`errnum::Int32` converts `e`). -/
def systemError3 (p : String) (e : Int) (x : Option String) : R SystemErrorM := do
  let e ← toInt .i32 e
  pure ⟨p, e, x⟩
/-- `SystemError(p, e)`, line 29. -/
def systemError2 (p : String) (e : Int) : R SystemErrorM := systemError3 p e none
/-- `SystemError(p) = new(p, Libc.errno(), nothing)`, line 30. -/
def systemError1 (errno : Int) (p : String) : R SystemErrorM := systemError3 p errno none

/-- `lock(::IO) = nothing`, `unlock(::IO) = nothing`, `reseteof(x::IO) = nothing`. -/
def lockIO (_s : St) : Unit := ()
def unlockIO (_s : St) : Unit := ()
def reseteof (_s : St) : Unit := ()
/-- `buffer_writes(x::IO, bufsize=SZ_UNBUFFERED_IO) = x`, line 48. -/
def bufferWrites (s : St) (_bufsize : Nat := 65536) : St := s
/-- `isreadable(io::IO) = isopen(io)`, line 124; `iswritable(io::IO) = isopen(io)`, line 147. -/
def isreadable (s : St) : Bool := s.isopen
def iswritable (s : St) : Bool := s.isopen
/-- `isreadonly(s) = isreadable(s) && !iswritable(s)`, line 893. -/
def isreadonly (r w : Bool) : Bool := r && !w
/-- `flush(io::IO) = nothing`, line 1620. -/
def flushIO (_s : St) : Unit := ()

/-- `read(stream, ::Type{Union{}}, slurp...)`, line 263. -/
def readUnion {α} (_s : St) : R α := .error (.errorException "cannot read a value of type Union{}")
/-- `peek(s::IO, ::Type{Union{}}, slurp...)`, line 389. -/
def peekUnion {α} (_s : St) : R α := .error (.methodError "peek")
/-- `read(s::IO, ::Type{UInt8})` and `write(s::IO, x::UInt8)` fallbacks, lines 346-347: a type
without byte I/O. -/
def readByteFallback {α} (tyname : String) : R α := .error (.errorException (tyname ++ " does not support byte I/O"))
/-- `write(io::IO, x) = throw(MethodError(write, (io, x)))`, line 897. -/
def writeFallback {α} : R α := .error (.methodError "write")
/-- `read(s::IO, T::Type)`, line 1345. -/
def readTypeFallback {α} (tname : String) : R α :=
  .error (.errorException ("The IO stream does not support reading objects of type " ++ tname ++ "."))

/-! ## Byte loops, lines 343-391 -/

/-- `writepartial(io::IO, x) = write(io, x)`, line 343. -/
def writepartial {α} (write : St → α) (s : St) : α := write s

/-- `unsafe_write(s::IO, p::Ptr{UInt8}, n::UInt)`, lines 358-364: one `write(s, byte)` per
byte, summing the counts. -/
def unsafeWrite (s : St) : Bytes → Nat × St
  | [] => (0, s)
  | b :: bs =>
    let (k, s1) := writeByte s b
    let (n, s2) := unsafeWrite s1 bs
    (k + n, s2)

/-- `unsafe_read(s::IO, p::Ptr{UInt8}, n::UInt)`, lines 375-380: `n` calls of
`read(s, UInt8)`; the stored bytes are returned. -/
def unsafeRead : Nat → St → R (Bytes × St)
  | 0, s => .ok ([], s)
  | n + 1, s => do
    let (b, s1) ← readByte s
    let (bs, s2) ← unsafeRead n s1
    pure (b :: bs, s2)

/-- `mark(io::IO)`, lines 1575-1577. -/
def mark (s : St) : Int × St := (position s, { s with mark := position s })
/-- `ismarked(io::IO) = io.mark >= 0`, line 1615. -/
def ismarked (s : St) : Bool := decide (s.mark ≥ 0)
/-- `unmark(io::IO)`, lines 1586-1590. -/
def unmark (s : St) : Bool × St := if !ismarked s then (false, s) else (true, { s with mark := -1 })
/-- `reset(io::T)`, lines 1600-1606. -/
def reset (s : St) : R (Int × St) :=
  if !ismarked s then argErr "not marked" else do
    let m := s.mark
    let s1 ← seek s m.toNat
    pure (m, { s1 with mark := -1 })

/-- `peek(s::IO, ::Type{T})`, lines 382-388: `mark`, `read(s, T)`, and `reset` in `finally`.
`read` is the reader of `T`. -/
def peek {α} (read : St → R (α × St)) (s : St) : R (α × St) :=
  let s1 := (mark s).2
  match read s1 with
  | .ok (v, s2) => do let (_, s3) ← reset s2; pure (v, s3)
  | .error e => match reset s1 with
    | .ok _ => .error e
    | .error e' => .error e'
/-- `peek(s) = peek(s, UInt8)::UInt8`, line 391. -/
def peekByte (s : St) : R (UInt8 × St) := peek readByte s

/-! ## `open_flags` and `open(f, args...)`, lines 401-456 -/

structure Flags where
  read : Bool
  write : Bool
  create : Bool
  truncate : Bool
  append : Bool
  deriving DecidableEq, Repr

/-- `open_flags(; read, write, create, truncate, append)`, lines 401-431; `none` is `nothing`. -/
def openFlags (read write create truncate append : Option Bool) : Flags :=
  let (create, truncate) :=
    if write = some true ∧ read ≠ some true ∧ append ≠ some true then
      (if create = none then some true else create, if truncate = none then some true else truncate)
    else (create, truncate)
  let (write, create) :=
    if truncate = some true ∨ append = some true then
      (if write = none then some true else write, if create = none then some true else create)
    else (write, create)
  let write := write.getD false
  let read := read.getD (!write)
  ⟨read, write, create.getD false, truncate.getD false, append.getD false⟩

/-- `open(f::Function, args...; kwargs...)`, lines 449-456: `f` runs on the opened stream
and the stream it leaves is closed whether or not `f` throws. `f` returns its result and
the stream state. -/
def openDo {α} (opened : R St) (f : St → R α × St) : R α × Option St :=
  match opened with
  | .error e => (.error e, none)
  | .ok io => let (r, io') := f io; (r, some (close io'))

/-! ## `AbstractPipe`, lines 476-542 -/

/-- A pipe object: its reader and writer streams (`pipe_reader`, `pipe_writer`). -/
structure Pipe where
  rd : St
  wr : St
  deriving DecidableEq, Repr

/-- `pipe_reader(io)`, `pipe_writer(io)`, lines 486-487. -/
def pipeReader (p : Pipe) : St := p.rd
def pipeWriter (p : Pipe) : St := p.wr
/-- Run a reader operation on `pipe_reader(io)`. -/
def onReader {α} (op : St → R (α × St)) (p : Pipe) : R (α × Pipe) := do
  let (a, s) ← op (pipeReader p)
  pure (a, { p with rd := s })
/-- Run a writer operation on `pipe_writer(io)`. -/
def onWriter {α} (op : St → R (α × St)) (p : Pipe) : R (α × Pipe) := do
  let (a, s) ← op (pipeWriter p)
  pure (a, { p with wr := s })

/-- `getproperty(pipe::AbstractPipe, name)`, lines 478-484: the stream fields are
type-asserted to be `IO`. -/
def pipeGetproperty {α} (getfield : String → α) (isIO : α → Bool) (name : String) : R α :=
  if name ∈ ["in", "in_stream", "out", "out_stream", "err", "err_stream"] then
    if isIO (getfield name) then .ok (getfield name) else .error (.typeError "typeassert")
  else .ok (getfield name)

/-- `iswritable(io::AbstractPipe)`, line 489. -/
def pipeIswritable (p : Pipe) : Bool := iswritable (pipeWriter p)
/-- `flush`/`closewrite(io::AbstractPipe)`, lines 496-498 (the `@eval` loop). -/
def pipeFlushLike (f : St → R (Unit × St)) (p : Pipe) : R (Unit × Pipe) := onWriter f p
/-- `write(io::AbstractPipe, byte::UInt8)`, line 500. -/
def pipeWriteByte (p : Pipe) (b : UInt8) : R (Nat × Pipe) := onWriter (fun s => .ok (writeByte s b)) p
/-- `writepartial(io::AbstractPipe, x)`, line 501. -/
def pipeWritepartial {α} (w : St → R (α × St)) (p : Pipe) : R (α × Pipe) := onWriter (writepartial w) p
/-- `write(to::IO, from::AbstractPipe) = write(to, pipe_reader(from))`, line 502. -/
def writeFromPipe {α} (w : St → St → α) (to : St) (p : Pipe) : α := w to (pipeReader p)
/-- `unsafe_write(io::AbstractPipe, p, nb)`, lines 503-505. -/
def pipeUnsafeWrite (p : Pipe) (bs : Bytes) : R (Nat × Pipe) := onWriter (fun s => .ok (unsafeWrite s bs)) p
/-- `buffer_writes(io::AbstractPipe, args...)`, line 506. -/
def pipeBufferWrites (p : Pipe) : St := bufferWrites (pipeWriter p)
/-- `mark`, `unmark`, `reset`, `ismarked`, `read`, `bytesavailable`, `reseteof`, `isreadable`
on `AbstractPipe`, line 513 (the `@eval` loop): forwarded to `pipe_reader`. -/
def pipeReaderOp {α} (f : St → R (α × St)) (p : Pipe) : R (α × Pipe) := onReader f p
/-- `readavailable(io::AbstractPipe)`, lines 517-519. -/
def pipeReadavailable (ra : St → R (Bytes × St)) (p : Pipe) : R (Bytes × Pipe) := onReader ra p
/-- `read(io::AbstractPipe, ::Type{UInt8})`, lines 520-522. -/
def pipeReadByte (p : Pipe) : R (UInt8 × Pipe) := onReader readByte p
/-- `unsafe_read(io::AbstractPipe, p, nb)`, line 523. -/
def pipeUnsafeRead (p : Pipe) (n : Nat) : R (Bytes × Pipe) := onReader (unsafeRead n) p
/-- `copyuntil(out, io::AbstractPipe, arg)` for `UInt8`, `AbstractChar`, `AbstractString`,
`AbstractVector` delimiters, lines 524-527, and `readuntil_vector!(io::AbstractPipe, ...)`,
line 528, and `readbytes!(io::AbstractPipe, ...)`, lines 531-533, and
`peek(io::AbstractPipe, T)`, line 534, and `wait_readnb(io::AbstractPipe, nb)`, line 535:
forwarded with the same arguments to `pipe_reader(io)`. -/
def pipeForward {α} (op : St → R (α × St)) (p : Pipe) : R (α × Pipe) := onReader op p
/-- `eof(io::AbstractPipe)`, lines 536-538. -/
def pipeEof (p : Pipe) : Bool := eof (pipeReader p)
/-- `isopen(io::AbstractPipe)`, line 540. -/
def pipeIsopen (p : Pipe) : Bool := (pipeWriter p).isopen || (pipeReader p).isopen
/-- `close(io::AbstractPipe)`, line 541: writer first, then reader. -/
def pipeClose (p : Pipe) : Pipe := let p1 := { p with wr := close (pipeWriter p) }; { p1 with rd := close (pipeReader p1) }
/-- `wait_close(io::AbstractPipe)`, line 542: writer, then reader. -/
def pipeWaitClose (wc : St → List String) (p : Pipe) : List String := wc (pipeWriter p) ++ wc (pipeReader p)

/-! ## Binary I/O, lines 897-1037 -/

/-- The `n` little-endian bytes of `x` (the memory of `Ref(x)` on the supported
little-endian platforms). -/
def leBytes : Nat → Nat → Bytes
  | 0, _ => []
  | n + 1, x => (x % 256).toUInt8 :: leBytes n (x / 256)

/-- The value of little-endian bytes. -/
def leVal : Bytes → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leVal bs

/-- The two's-complement bit pattern of `x : T`. -/
def bitsOf (t : IntTy) (x : Int) : Nat := (x % 2 ^ t.bits).toNat

/-- `write(io::IO, x1, xs...)`, lines 898-905: `write` each argument, summing counts. -/
def writeMany {α} (w : St → α → Nat × St) (s : St) (x1 : α) (xs : List α) : Nat × St :=
  let (n, s1) := w s x1
  xs.foldl (fun (acc : Nat × St) x => let (k, s') := w acc.2 x; (acc.1 + k, s')) (n, s1)

/-- `unsafe_write(s, p::Ref{T}, n)` and `unsafe_write(s, p::Ptr, n)`, lines 907-909: convert
the pointer and the count, then the byte method. -/
def unsafeWriteRef (s : St) (mem : Bytes) (n : Int) : R (Nat × St) := do
  let n ← toInt .u64 n
  pure (unsafeWrite s (mem.take n.toNat))
/-- `write(s::IO, x::Ref{T})`, lines 910-917: `isbits` contents are written as their
`sizeof(T)` bytes, otherwise `write(s, x[])`. -/
def writeRef (isPtr isbits : Bool) (bytes : Bytes) (writeVal : St → R (Nat × St)) (s : St) :
    R (Nat × St) :=
  if isPtr then .error (.errorException "write cannot copy from a Ptr")
  else if isbits then .ok (unsafeWrite s bytes) else writeVal s
/-- `write(s::IO, x::Int8) = write(s, reinterpret(UInt8, x))`, line 918. -/
def writeInt8 (s : St) (x : Int) : Nat × St := writeByte s (bitsOf .i8 x).toUInt8
/-- `write(s::IO, x::Union{Int16,...,Float64})`, lines 919-921: `unsafe_write(s, Ref(x),
sizeof(x))`; a float is its bit pattern `bits` of `nbytes` bytes. -/
def writeInt (t : IntTy) (s : St) (x : Int) : Nat × St := unsafeWrite s (leBytes (t.bits / 8) (bitsOf t x))
def writeFloat (nbytes : Nat) (s : St) (bits : Nat) : Nat × St := unsafeWrite s (leBytes nbytes bits)
/-- `write(s::IO, x::Bool) = write(s, UInt8(x))`, line 923. -/
def writeBool (s : St) (b : Bool) : Nat × St := writeByte s (if b then 1 else 0)
/-- `write(to::IO, p::Ptr) = write(to, convert(UInt, p))`, line 924. -/
def writePtr (s : St) (p : Nat) : Nat × St := writeInt .u64 s p

/-- `write(s::IO, A::AbstractArray)`, lines 926-938: each element through a `Ref`;
elements are given by their bytes. -/
def writeArray (isbits : Bool) (s : St) (elems : List Bytes) : R (Nat × St) :=
  if !isbits then .error (.errorException "`write` is not supported on non-isbits arrays")
  else .ok (elems.foldl (fun (acc : Nat × St) e => let (k, s') := unsafeWrite acc.2 e; (acc.1 + k, s')) (0, s))

/-- `merge_adjacent_dim(sz, st)` (`base/reshapedarray.jl:448-465`) on the dimensions
`sz`, `st` from `n` on; returns `(msz, mst, n)`. -/
def mergeLoop (sz st : List Nat) : Nat → Nat → Nat → Nat → Nat × Nat × Nat
  | 0, m, s, n => (m, s, n)
  | fuel + 1, m, s, n =>
    if n < sz.length then
      let szn := sz.getD n 0
      let stn := st.getD n 0
      if m = 1 then mergeLoop sz st fuel szn stn (n + 1)
      else if stn = s * m ∨ szn = 1 then mergeLoop sz st fuel (m * szn) s (n + 1)
      else (m, s, n)
    else (m, s, n)
def mergeAdjacentDim (sz st : List Nat) : Nat × Nat × Nat :=
  match sz, st with
  | [], _ => (1, 1, 0)
  | [a], [b] => (a, b, 1)
  | a :: _, b :: _ => mergeLoop sz st sz.length a b 1
  | _, _ => (1, 1, 0)

/-- Column-major `CartesianIndices(dims)`, as lists of 1-based indices. -/
def cartesian : List Nat → List (List Nat)
  | [] => [[]]
  | d :: ds => (cartesian ds).flatMap (fun J => (List.range d).map (fun i => (i + 1) :: J))

/-- How a strided array write/read is carried out by `write(s, A::StridedArray)`,
lines 940-971, and `read!(s, A::StridedArray)`, lines 1059-1089. -/
inductive StridedPlan where
  | notIsbits
  | whole (nelem : Nat)
  | generic
  | runs (offsets : List Nat) (msz : Nat)
  deriving DecidableEq, Repr

/-- The dispatch and the run offsets (in elements, from `pointer(A)`) of the strided
methods: contiguous arrays are one `unsafe_write`; `mst != 1` falls back to the
`AbstractArray` method; otherwise one run of `msz` elements per index of the
remaining dimensions `sz′` padded with ones, at offset `sum(st′[i]*(I[i]-1))`. -/
def stridedPlan (isbits contiguous : Bool) (sz st : List Nat) : StridedPlan :=
  if !isbits then .notIsbits
  else if contiguous then .whole (sz.foldl (· * ·) 1)
  else
    let (msz, mst, n) := mergeAdjacentDim sz st
    if mst ≠ 1 then .generic
    else if n = sz.length then .whole (sz.foldl (· * ·) 1)
    else
      -- `sz′, st′ = tail(sz), tail(st)`; `n - 1` shifts `(tail(x)..., pad)`
      let shift (l : List Nat) (pad : Nat) (k : Nat) : List Nat :=
        (List.range k).foldl (fun acc _ => acc.tail ++ [pad]) l
      let sz' := shift sz.tail 1 (n - 1)
      let st' := shift st.tail 0 (n - 1)
      let offs := (cartesian sz').map (fun I =>
        ((List.range sz'.length).map (fun i => st'.getD i 0 * (I.getD i 1 - 1))).foldl (· + ·) 0)
      .runs offs msz

/-- `write(s::IO, A::StridedArray)`: the elements are read from memory `mem` (element
`k` at `mem[k]`, 0-based from `pointer(A)`); `generic` gives the `AbstractArray` method's
column-major element list. -/
def writeStrided (isbits contiguous : Bool) (sz st : List Nat) (mem : List Bytes)
    (genericElems : List Bytes) (s : St) : R (Nat × St) :=
  match stridedPlan isbits contiguous sz st with
  | .notIsbits => .error (.errorException "`write` is not supported on non-isbits arrays")
  | .whole n => .ok (unsafeWrite s (mem.take n).flatten)
  | .generic => writeArray true s genericElems
  | .runs offs msz => .ok (offs.foldl (fun (acc : Nat × St) o =>
      let (k, s') := unsafeWrite acc.2 ((mem.drop o).take msz).flatten; (acc.1 + k, s')) (0, s))

/-- `read!(s::IO, A::StridedArray{T})`, lines 1059-1089: non-`isbits` or contiguous arrays
use the `AbstractArray` method; otherwise as for `write`, with `unsafe_read` of runs.
The result lists the `(offset, bytes)` stores into the array memory (offsets in elements,
`nb` bytes per element); `generic` stands for the `AbstractArray` method. -/
def readStrided (isbits contiguous : Bool) (sz st : List Nat) (nb : Nat) (s : St) :
    R (Option (List (Nat × Bytes)) × St) :=
  if !isbits || contiguous then .ok (none, s)
  else
    match stridedPlan true false sz st with
    | .whole n => do let (bs, s') ← unsafeRead (nb * n) s; pure (some [(0, bs)], s')
    | .runs offs msz =>
      let rec go : List Nat → St → R (List (Nat × Bytes) × St)
        | [], s => .ok ([], s)
        | o :: os, s => do
          let (bs, s1) ← unsafeRead (nb * msz) s
          let (rest, s2) ← go os s1
          pure ((o, bs) :: rest, s2)
      do let (ws, s') ← go offs s; pure (some ws, s')
    | _ => .ok (none, s)

/-- `write(io::IO, c::Char)`, lines 973-980: the bytes of `bswap(reinterpret(UInt32, c))`
from the least significant, stopping once the rest is zero (at least one byte). -/
def writeCharLoop (s : St) (u : Nat) (n : Nat) : Nat × St :=
  let (k, s1) := writeByte s (u % 256).toUInt8
  if u / 256 = 0 then (n + k, s1) else writeCharLoop s1 (u / 256) (n + k)
termination_by u
decreasing_by omega

/-- `bswap` of a `UInt32`. -/
def bswap32 (c : Nat) : Nat :=
  (c % 256) * 2 ^ 24 + (c / 256 % 256) * 2 ^ 16 + (c / 65536 % 256) * 2 ^ 8 + c / 16777216 % 256
def writeChar (s : St) (c : Nat) : Nat × St := writeCharLoop s (bswap32 c) 0

/-- `write(io::IO, s::Symbol)`, lines 984-987: `unsafe_write` of the `strlen` bytes of the
name. -/
def writeSymbol (s : St) (name : Bytes) : Nat × St := unsafeWrite s (name.takeWhile (· != 0))

/-- `write(to::IO, from::IO)`, lines 989-995: `write(to, readavailable(from))` until
`eof(from)`; here `readavailable` returns the next `k ≥ 1` bytes. -/
def writeFromIO (k : Nat) (to frm : St) : Nat × St × St :=
  let rec go (fuel : Nat) (n : Nat) (to frm : St) : Nat × St × St :=
    match fuel with
    | 0 => (n, to, frm)
    | fuel + 1 =>
      if eof frm then (n, to, frm)
      else
        let chunk := frm.inp.take (max k 1)
        let frm' := { frm with pre := frm.pre ++ chunk, inp := frm.inp.drop (max k 1) }
        let (w, to') := unsafeWrite to chunk
        go fuel (n + w) to' frm'
  go (frm.inp.length + 1) 0 to frm

/-- `unsafe_read(s, p::Ref{T}, n)` and `unsafe_read(s, p::Ptr, n)`, lines 997-998. -/
def unsafeReadRef (s : St) (n : Int) : R (Bytes × St) := do
  let n ← toInt .u64 n
  unsafeRead n.toNat s
/-- `read!(s::IO, x::Ref{T})`, lines 999-1007. -/
def readRefBang {α} (isPtr isbits : Bool) (size : Nat) (readVal : St → R (α × St)) (s : St) :
    R (Sum Bytes α × St) :=
  if isPtr then .error (.errorException "read! cannot copy into a Ptr")
  else if isbits then do let (b, s') ← unsafeRead size s; pure (.inl b, s')
  else do let (v, s') ← readVal s; pure (.inr v, s')
/-- `read(s::IO, ::Type{Int8}) = reinterpret(Int8, read(s, UInt8))`, line 1009. -/
def readInt8 (s : St) : R (Int × St) := do
  let (b, s') ← readByte s
  pure (wrapInt .i8 b.toNat, s')
/-- `read(s::IO, T::Union{Type{Int16},...})`, lines 1010-1014: `unsafe_read` of `sizeof(T)`
bytes into a `Ref{T}`. -/
def readInt (t : IntTy) (s : St) : R (Int × St) := do
  let (bs, s') ← unsafeRead (t.bits / 8) s
  pure (wrapInt t (leVal bs), s')
def readFloat (nbytes : Nat) (s : St) : R (Nat × St) := do
  let (bs, s') ← unsafeRead nbytes s
  pure (leVal bs, s')
/-- `read(s::IO, ::Type{Bool}) = (read(s, UInt8) != 0)`, line 1016. -/
def readBool (s : St) : R (Bool × St) := do
  let (b, s') ← readByte s
  pure (b != 0, s')
/-- `read(s::IO, ::Type{Ptr{T}}) = convert(Ptr{T}, read(s, UInt))`, line 1017. -/
def readPtr (s : St) : R (Int × St) := readInt .u64 s

/-- `read!(s::IO, A::AbstractArray{T})`, lines 1019-1037: for `isbits` element types one
`unsafe_read` of the whole array when contiguous, else one per element; otherwise
`read(s, T)` per element. Elements are returned as their bytes (`nbytes` each). -/
def readArrayBang (isbits contiguous : Bool) (nbytes len : Nat) (s : St) : R (List Bytes × St) :=
  if isbits && contiguous then do
    let (bs, s') ← unsafeRead (nbytes * len) s
    pure ((List.range len).map (fun i => (bs.drop (i * nbytes)).take nbytes), s')
  else
    let rec go : Nat → St → R (List Bytes × St)
      | 0, s => .ok ([], s)
      | k + 1, s => do
        let (b, s1) ← unsafeRead nbytes s
        let (bs, s2) ← go k s1
        pure (b :: bs, s2)
    go len s

/-- `write(s::IO, B::BitArray) = write(s, B.chunks)`, lines 1043-1046. -/
def writeBitArray (s : St) (chunks : List Nat) : R (Nat × St) :=
  writeArray true s (chunks.map (leBytes 8))
/-- `_msk_end(n)`: the mask of the used bits of the last chunk. -/
def mskEnd (n : Nat) : Nat := if n % 64 = 0 then 2 ^ 64 - 1 else 2 ^ (n % 64) - 1
/-- `read!(s::IO, B::BitArray)`, lines 1047-1057: read the chunks; nonzero bits past
`length(B)` are cleared and raise `DimensionMismatch`. -/
def readBitArrayBang (n : Nat) (s : St) : R (List Nat × St) := do
  let nchunks := (n + 63) / 64
  let (cs, s') ← readArrayBang true true 8 nchunks s
  let chunks := cs.map leVal
  match chunks.getLast? with
  | some last =>
    if last &&& mskEnd n ≠ last then
      .error (.jl (.argumentError "DimensionMismatch: read mismatch, found non-zero bits after BitArray length"))
    else pure (chunks, s')
  | none => pure (chunks, s')

/-! ## `read(io, Char)`, lines 1091-1106 -/

/-- `leading_ones(b)` of a byte. -/
def leadingOnes (b : UInt8) : Nat :=
  if b.toNat ≥ 0xff then 8 else if b.toNat ≥ 0xfe then 7 else if b.toNat ≥ 0xfc then 6
  else if b.toNat ≥ 0xf8 then 5 else if b.toNat ≥ 0xf0 then 4 else if b.toNat ≥ 0xe0 then 3
  else if b.toNat ≥ 0xc0 then 2 else if b.toNat ≥ 0x80 then 1 else 0

/-- The `while s ≥ l && !eof(io)` loop: `s` runs over 16, 8, 0 (shift amounts); `peek(io)`
is the generic `peek`, which resets the mark. -/
def readCharLoop : List Nat → Nat → St → R (Nat × St)
  | [], c, st => .ok (c, st)
  | sh :: shs, c, st =>
    if eof st then .ok (c, st)
    else match peekByte st with
      | .error e => .error e
      | .ok (p, st1) =>
        if p.toNat / 64 = 2 then
          match readByte st1 with
          | .error e => .error e
          | .ok (b, st2) => readCharLoop shs (c + b.toNat * 2 ^ sh) st2
        else .ok (c, st1)

/-- `read(io::IO, ::Type{Char})`: the Julia `Char` as its `UInt32` representation. -/
def readChar (st : St) : R (Nat × St) := do
  let (b0, st1) ← readByte st
  let lo := leadingOnes b0
  let c := b0.toNat * 2 ^ 24
  if 2 ≤ lo ∧ lo ≤ 4 then
    -- `l = 8*(4-lo)`, `s` from 16 down to `l` by 8
    readCharLoop ([16, 8, 0].take (lo - 1)) c st1
  else pure (c, st1)

/-- The `UInt32` of a `Char` given by its (1 to 4) bytes, most significant first. -/
def packChar (bs : Bytes) : Nat :=
  (bs.getD 0 0).toNat * 2 ^ 24 + (bs.getD 1 0).toNat * 2 ^ 16 + (bs.getD 2 0).toNat * 2 ^ 8 + (bs.getD 3 0).toNat

/-! ## `skipchars`, lines 1643-1653 -/

/-- `skipchars(predicate, io; linecomment)`: characters are read with `read(io, Char)`
(their byte counts are `ncodeunits`); a non-matching character is pushed back with
`skip(io, -ncodeunits(c))`. `readLine` is `readline(io)`. `fuel` bounds the iterations
(each consumes at least one byte). -/
def skipchars (pred : Nat → Bool) (linecomment : Option Nat) (readLine : St → R St) :
    Nat → St → R St
  | 0, s => .ok s
  | fuel + 1, s =>
    if eof s then .ok s
    else do
      let n0 := position s
      let (c, s1) ← readChar s
      if some c = linecomment then
        let s2 ← readLine s1
        skipchars pred linecomment readLine fuel s2
      else if !pred c then skip s1 (-((position s1 - n0 : Nat) : Int))
      else skipchars pred linecomment readLine fuel s1

/-- `copyline(out::IO, s::IO; keep=false)`, lines 760-779: the byte loop; after a `'\r'` the
next byte is read, and if it is not `'\n'` both are written. Returns the output and the
unread input. -/
def copylineLoop (out inp : Bytes) : Bytes × Bytes :=
  match inp with
  | [] => (out, [])
  | b :: r =>
    if b = 0x0a then (out, r)
    else if b = 0x0d then
      match r with
      | [] => (out ++ [b], [])
      | b2 :: r2 => if b2 = 0x0a then (out, r2) else copylineLoop (out ++ [0x0d, b2]) r2
    else copylineLoop (out ++ [b]) r
termination_by inp.length
decreasing_by all_goals simp_all <;> omega

end JuliaLean.IOCov.Io

namespace JuliaLean.IOCov.IOText

open JuliaLean
open JuliaLean.IOCov.Io

abbrev B := List UInt8
abbrev RR (alpha : Type) := Except JlError alpha

/-! ## Filename wrappers -/

/-- `write(filename, a1, args...)`, `base/io.jl:555`. -/
def writeFilename (openWrite : String -> B -> Nat) (filename : String) (content : B) : Nat :=
  openWrite filename content
/-- `read(filename, args...)`, `base/io.jl:571`. -/
def readFilename (openRead : String -> B) (filename : String) : B := openRead filename
/-- `read(filename, ::Type{T})`, `base/io.jl:573`. -/
def readFilenameType {alpha : Type} (openRead : String -> alpha) (filename : String) : alpha :=
  openRead filename
/-- `read!(filename, a)`, `base/io.jl:584`. -/
def readBangFilename {alpha : Type} (openRead : String -> alpha -> alpha)
    (filename : String) (a : alpha) : alpha := openRead filename a
/-- `readuntil(filename, delim; kw...)`, `base/io.jl:623`. -/
def readuntilFilename {d : Type} (openRead : String -> d -> B) (filename : String) (delim : d) : B :=
  openRead filename delim
/-- `copyuntil(out, filename, delim; kw...)`, `base/io.jl:666`. -/
def copyuntilFilename {out d : Type} (openCopy : out -> String -> d -> out)
    (o : out) (filename : String) (delim : d) : out := openCopy o filename delim
/-- `readline(filename; keep, cancel)`, `base/io.jl:710-713`. -/
def readlineFilename (openLine : String -> Bool -> B) (filename : String) (keep : Bool) : B :=
  openLine filename keep
/-- `copyline(out, filename; keep, cancel)`, `base/io.jl:753-757`. -/
def copylineFilename {out : Type} (openLine : out -> String -> Bool -> out)
    (o : out) (filename : String) (keep : Bool) : out := openLine o filename keep
/-- `readlines(filename; kw...)`, `base/io.jl:807-811`. -/
def readlinesFilename (openLines : String -> List B) (filename : String) : List B :=
  openLines filename
/-- `countlines(filename; eol)`, `base/io.jl:1717`. -/
def countlinesFilename (openCount : String -> UInt8 -> Nat) (filename : String) (eol : UInt8) : Nat :=
  openCount filename eol

/-! ## Scalar delimiters and lines -/

def findByte (b : UInt8) (xs : B) : Option Nat := xs.idxOf? b

def consume (s : St) (n : Nat) : St :=
  { s with pre := s.pre ++ s.inp.take n, inp := s.inp.drop n }

/-- `copyuntil` for a byte delimiter, the behavior used by `readuntil`,
`base/io.jl:624-626` and the generic contract at `:637-648`. -/
def copyUntilByte (s : St) (delim : UInt8) (keep : Bool) : B × St :=
  match findByte delim s.inp with
  | none => (s.inp, consume s s.inp.length)
  | some k => (s.inp.take (if keep then k + 1 else k), consume s (k + 1))

/-- `readuntil(stream, delim::UInt8)`, `base/io.jl:624-626`. -/
def readuntilByte (s : St) (delim : UInt8) (keep : Bool) : B × St :=
  copyUntilByte s delim keep

def startsWith {alpha : Type} [DecidableEq alpha] (xs target : List alpha) : Bool :=
  xs.take target.length == target

def findSublist {alpha : Type} [DecidableEq alpha] (target xs : List alpha) : Option Nat :=
  (List.range (xs.length + 1)).find? (fun k => startsWith (xs.drop k) target)

/-- Observable behavior of `readuntil_vector!`, `base/io.jl:1161-1230`.
The source KMP cache changes only the search cost; this model preserves its
source-order empty-target, match, keep, and early-EOF branches. -/
def readuntilVector {alpha : Type} [DecidableEq alpha]
    (input target : List alpha) (keep : Bool) : List alpha × List alpha × Bool :=
  if target.isEmpty then ([], input, true)
  else
    match findSublist target input with
    | some k => (input.take (if keep then k + target.length else k),
        input.drop (k + target.length), true)
    | none => (input, [], false)

/-- `readuntil(stream, delim::Union{AbstractChar,AbstractString})`,
`base/io.jl:627-629`, after UTF-8 encoding of the delimiter. -/
def readuntilText (s : St) (delim : B) (keep : Bool) : B × St :=
  let r := readuntilVector s.inp delim keep
  (r.1, consume s (s.inp.length - r.2.1.length))

/-- Generic scalar `readuntil`, `base/io.jl:630-633`. -/
def readuntilScalar {alpha : Type} [DecidableEq alpha]
    (input : List alpha) (delim : alpha) (keep : Bool) : List alpha × List alpha :=
  match input.idxOf? delim with
  | none => (input, [])
  | some k => (input.take (if keep then k + 1 else k), input.drop (k + 1))

/-- `_copyuntil`, `base/io.jl:1134-1144`. -/
def copyuntilScalar {alpha : Type} [DecidableEq alpha]
    (out input : List alpha) (delim : alpha) (keep : Bool) : List alpha × List alpha :=
  let r := readuntilScalar input delim keep
  (out ++ r.1, r.2)

/-- `copyuntil(out, s, delim::AbstractChar)`, `base/io.jl:1110-1124`.
ASCII uses the byte path; other characters use `readeach(Char)`. -/
def copyuntilChar (out input : B) (delim : UInt32) (encoded : B) (keep : Bool) : B × B :=
  if delim.toNat <= 0x7f then
    let r := readuntilScalar input delim.toNat.toUInt8 keep
    (out ++ r.1, r.2)
  else
    let r := readuntilVector input encoded keep
    (out ++ r.1, r.2.1)

/-- Generic `copyuntil`, `base/io.jl:1128-1131`. -/
def copyuntilGeneric {alpha : Type} [DecidableEq alpha]
    (out input : List alpha) (delim : alpha) (keep : Bool) : List alpha × List alpha :=
  copyuntilScalar out input delim keep

/-- String-target `copyuntil`, `base/io.jl:1232-1248`. -/
def copyuntilString (out input target : B) (keep : Bool) : B × B :=
  if target.isEmpty then (out, input)
  else
    let r := readuntilVector input target keep
    (out ++ r.1, r.2.1)

/-- Vector-target `readuntil`, `base/io.jl:1253-1260`. -/
def readuntilVectorMethod {alpha : Type} [DecidableEq alpha]
    (input target : List alpha) (keep : Bool) : List alpha × List alpha :=
  let r := readuntilVector input target keep
  (r.1, r.2.1)

/-- Vector-target `copyuntil`, `base/io.jl:1261-1267`. -/
def copyuntilVectorMethod {alpha : Type} [DecidableEq alpha]
    (out input target : List alpha) (keep : Bool) : List alpha × List alpha :=
  let r := readuntilVector input target keep
  (out ++ r.1, r.2.1)

def stripLineEnding (line : B) : B :=
  if line.getLast? = some 0x0a then
    let line := line.dropLast
    if line.getLast? = some 0x0d then line.dropLast else line
  else line

/-- `readline(s::IO; keep)`, `base/io.jl:714-716`. -/
def readlineStream (s : St) (keep : Bool) : B × St :=
  let r := copyUntilByte s 0x0a true
  (if keep then r.1 else stripLineEnding r.1, r.2)

def readlinesLoop : Nat -> St -> Bool -> List B × St
  | 0, s, _ => ([], s)
  | fuel + 1, s, keep =>
      if eof s then ([], s)
      else
        let r := readlineStream s keep
        let rest := readlinesLoop fuel r.2 keep
        (r.1 :: rest.1, rest.2)

/-- `readlines(s) = collect(eachline(s))`, `base/io.jl:812-813`. -/
def readlinesStream (s : St) (keep : Bool) : List B × St :=
  readlinesLoop (s.inp.length + 1) s keep

/-- `readchomp(x)`, `base/io.jl:1285-1290`. -/
def readchompBytes (xs : B) : B := stripLineEnding xs

/-! ## Buffered byte reads -/

def replacePrefix (old new : B) : B := new ++ old.drop new.length

/-- `readbytes!`, `base/io.jl:1301-1319`. -/
def readbytesBang (s : St) (buffer : B) (nb : Nat) : Nat × B × St :=
  let nr := min nb s.inp.length
  let got := s.inp.take nr
  let buffer := if buffer.length < nr then replacePrefix (buffer ++ List.replicate (nr - buffer.length) 0) got
    else replacePrefix buffer got
  (nr, buffer, consume s nr)

/-- `read(s, nb::Integer)`, `base/io.jl:1326-1335`. -/
def readCount (s : St) (nb : Int) : RR (B × St) :=
  if nb < 0 then .error (.argumentError "invalid Array dimensions")
  else
    let r := readbytesBang s [] nb.toNat
    .ok (r.2.1.take r.1, r.2.2)

/-- `read(s, String)`, `base/io.jl:1337-1344`, represented by its bytes. -/
def readString (s : St) : B × St := (s.inp, consume s s.inp.length)

/-! ## Byte order -/

def byteSwap (nbytes value : Nat) : Nat :=
  (List.range nbytes).foldl (fun out k =>
    out ||| (((value >>> (8 * k)) % 256) <<< (8 * (nbytes - 1 - k)))) 0

/-- Big-endian host definitions at `base/io.jl:821-824`. -/
def ntohBig (x : Nat) : Nat := x
def htonBig (x : Nat) : Nat := x
def ltohBig (nbytes x : Nat) : Nat := byteSwap nbytes x
def htolBig (nbytes x : Nat) : Nat := byteSwap nbytes x
/-- Little-endian host definitions at `base/io.jl:827-830`. -/
def ntohLittle (nbytes x : Nat) : Nat := byteSwap nbytes x
def htonLittle (nbytes x : Nat) : Nat := byteSwap nbytes x
def ltohLittle (x : Nat) : Nat := x
def htolLittle (x : Nat) : Nat := x

/-! ## Forward and read-each iterators -/

structure EachLineM where
  stream : St
  keep : Bool
  doneCalled : Bool := false
  deriving DecidableEq

/-- `EachLine(stream; ondone, keep, cancel)`, `base/io.jl:1354-1356`. -/
def eachLineCtor (stream : St) (keep : Bool) : EachLineM := ⟨stream, keep, false⟩
/-- `eachline(stream)`, `base/io.jl:1392-1394`. -/
def eachlineStream (stream : St) (keep : Bool) : EachLineM := eachLineCtor stream keep
/-- `eachline(filename)`, `base/io.jl:1396-1399`, after `open`. -/
def eachlineFilename (openFile : String -> St) (filename : String) (keep : Bool) : EachLineM :=
  eachLineCtor (openFile filename) keep

/-- `iterate(itr::EachLine)`, `base/io.jl:1401-1409`. -/
def iterateEachLine (itr : EachLineM) : Option (B × EachLineM) :=
  if eof itr.stream then none
  else
    let r := readlineStream itr.stream itr.keep
    some (r.1, { itr with stream := r.2 })

/-- `eltype(::Type{<:EachLine})`, `base/io.jl:1411`. -/
def eachLineEltype : String := "String"
/-- `IteratorSize(::Type{<:EachLine})`, `base/io.jl:1413`. -/
def eachLineIteratorSize : String := "SizeUnknown"
/-- `isdone(itr::EachLine, state...)`, `base/io.jl:1415`. -/
def eachLineIsdone (itr : EachLineM) : Bool := eof itr.stream

structure ReadEachM where
  stream : St
  width : Nat
  deriving DecidableEq

/-- `readeach(stream, T)`, `base/io.jl:1551`. -/
def readeachCtor (stream : St) (width : Nat) : ReadEachM := ⟨stream, width⟩
/-- `iterate(::ReadEachIterator)`, `base/io.jl:1553-1554`. -/
def iterateReadEach (itr : ReadEachM) : Option (B × ReadEachM) :=
  if eof itr.stream then none
  else
    let n := min itr.width itr.stream.inp.length
    some (itr.stream.inp.take n, { itr with stream := consume itr.stream n })
/-- Typed `eltype`, `base/io.jl:1556`. -/
def readEachEltype (name : String) : String := name
/-- Untyped `eltype`, `base/io.jl:1557`. -/
def readEachAny : String := "Any"
/-- `IteratorSize`, `base/io.jl:1559`. -/
def readEachIteratorSize : String := "SizeUnknown"
/-- `isdone`, `base/io.jl:1561`. -/
def readEachIsdone (itr : ReadEachM) : Bool := eof itr.stream

/-! ## Line counting -/

/-- `countlines(io; eol)`, `base/io.jl:1700-1715`. -/
def countlines (input : B) (eol : UInt32) : RR Nat :=
  if eol.toNat > 0x7f then .error (.argumentError "only ASCII line terminators are supported")
  else
    let b := eol.toNat.toUInt8
    let n := input.count b
    .ok (if !input.isEmpty && input.getLast? != some b then n + 1 else n)


end JuliaLean.IOCov.IOText

namespace JuliaLean.MissingChar

open JuliaLean.Strings (clo32)

/-- The continuation loop of `read(io::IO, ::Type{Char})`, `base/io.jl:1097-1103`.
Bound: at most 3 continuation bytes. -/
def readCharCont : Nat → UInt32 → Nat → Nat → List UInt8 → UInt32 × List UInt8
  | 0, c, _, _, rest => (c, rest)
  | fuel + 1, c, s, l, rest =>
    if s ≥ l then
      match rest with
      | b :: rest' =>
        if b &&& 0xc0 = 0x80 then readCharCont fuel (c ||| (b.toUInt32 <<< UInt32.ofNat s)) (s - 8) l rest'
        else (c, rest)
      | [] => (c, rest)
    else (c, rest)

/-- `read(io::IO, ::Type{Char})`, `base/io.jl:1091-1105`, on a nonempty byte list:
the Char and the unread bytes. -/
def readChar : List UInt8 → Option (UInt32 × List UInt8)
  | [] => none
  | b0 :: rest =>
    let lo := clo32 (b0.toUInt32 <<< 24)
    let c := b0.toUInt32 <<< 24
    if 2 ≤ lo ∧ lo ≤ 4 then some (readCharCont 3 c 16 (8 * (4 - lo)) rest)
    else some (c, rest)

end JuliaLean.MissingChar

namespace JuliaLean.Show

open JuliaLean.Strings

/-- `write(io, c::Char)`, `base/io.jl:973-980`: writes `u % UInt8` for
`u = bswap(c)` and stops once `u >>= 8` is zero. Four rounds exhaust a `UInt32`,
so the fuel never runs out. -/
def writeCharAux : Nat → UInt32 → List UInt8
  | 0, _ => []
  | k + 1, u => u.toUInt8 :: (if u >>> 8 = 0 then [] else writeCharAux k (u >>> 8))

/-- `write(io, c)` and `print(io, c)` for `c::Char` (`base/char.jl:305`). -/
def writeChar (c : UInt32) : List UInt8 := writeCharAux 4 (bswap32 c)

end JuliaLean.Show
