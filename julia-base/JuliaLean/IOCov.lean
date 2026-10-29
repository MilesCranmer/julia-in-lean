import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.IOCov.Common
import JuliaLean.IOCov.Env
import JuliaLean.IOCov.Libc
import JuliaLean.IOCov.Libdl
import JuliaLean.IOCov.Path
import JuliaLean.IOCov.Secret
import JuliaLean.IOCov.Util
import JuliaLean.IOCov.Io
import JuliaLean.IOCov.IOBuf
import JuliaLean.IOCov.Cmd
import JuliaLean.IOCov.IOBufferRemaining
import JuliaLean.IOCov.LibcRemaining
import JuliaLean.IOCov.IOText
import JuliaLean.IOCov.EnvFaithful
import JuliaLean.IOCov.SecretFaithful
import JuliaLean.IOCov.UtilFaithful
import JuliaLean.IOCov.LibdlFaithful
import JuliaLean.IOCov.PathFaithful

namespace JuliaLean.IOCov

open JuliaLean.Registry

/-- Registry entries of this area. -/
def existingEntries : List Entry := [
  { id := "iocov-io-systemerror3", juliaFile := "base/io.jl"
    juliaFns := ["SystemError(p, e, extrainfo)"]
    statement := "SystemError(p, e, extrainfo) stores its fields with errnum as Int32, throwing InexactError when e is out of range."
    source := "base/io.jl:18-28 (SystemError docstring)"
    status := .proven, prop := ``Io.SystemError3Correct, thm := some ``Io.systemError3Correct },
  { id := "iocov-io-systemerror2", juliaFile := "base/io.jl"
    juliaFns := ["SystemError(p, e)"]
    statement := "SystemError(p, e) has no extra information."
    source := "base/io.jl:29"
    status := .proven, prop := ``Io.SystemError2Correct, thm := some ``Io.systemError2Correct },
  { id := "iocov-io-systemerror1", juliaFile := "base/io.jl"
    juliaFns := ["SystemError(p)"]
    statement := "SystemError(p) records the current errno."
    source := "base/io.jl:18-30 (SystemError docstring)"
    status := .proven, prop := ``Io.SystemError1Correct, thm := some ``Io.systemError1Correct },
  { id := "iocov-io-buffer-writes", juliaFile := "base/io.jl"
    juliaFns := ["buffer_writes(x::IO, bufsize)"]
    statement := "buffer_writes on a generic IO returns the stream unchanged."
    source := "base/io.jl:48"
    status := .proven, prop := ``Io.BufferWritesIdentity, thm := some ``Io.bufferWritesIdentity },
  { id := "iocov-io-isreadable", juliaFile := "base/io.jl"
    juliaFns := ["isreadable(io::IO)"]
    statement := "isreadable(io) is isopen(io) for a generic stream."
    source := "base/io.jl:160-183 (isreadable docstring)"
    status := .proven, prop := ``Io.IsreadableOpen, thm := some ``Io.isreadableOpen },
  { id := "iocov-io-iswritable", juliaFile := "base/io.jl"
    juliaFns := ["iswritable(io::IO)"]
    statement := "iswritable(io) is isopen(io) for a generic stream."
    source := "base/io.jl:186-206 (iswritable docstring)"
    status := .proven, prop := ``Io.IswritableOpen, thm := some ``Io.iswritableOpen },
  { id := "iocov-io-read-union", juliaFile := "base/io.jl"
    juliaFns := ["read(stream, ::Type{Union{}})"]
    statement := "Reading a Union{} throws."
    source := "base/io.jl:263"
    status := .proven, prop := ``Io.ReadUnionThrows, thm := some ``Io.readUnionThrows },
  { id := "iocov-io-writepartial", juliaFile := "base/io.jl"
    juliaFns := ["writepartial(io::IO, x)"]
    statement := "writepartial is write for generic streams."
    source := "base/io.jl:332-343 (writepartial docstring)"
    status := .proven, prop := ``Io.WritepartialIsWrite, thm := some ``Io.writepartialIsWrite },
  { id := "iocov-io-byte-fallback", juliaFile := "base/io.jl"
    juliaFns := ["read(s::IO, ::Type{UInt8})", "write(s::IO, ::UInt8)"]
    statement := "Types without byte I/O throw an error naming the type."
    source := "base/io.jl:346-347"
    status := .proven, prop := ``Io.ByteIOFallbackThrows, thm := some ``Io.byteIOFallbackThrows },
  { id := "iocov-io-unsafe-write", juliaFile := "base/io.jl"
    juliaFns := ["unsafe_write(s::IO, p::Ptr{UInt8}, n::UInt)"]
    statement := "unsafe_write appends the n bytes and returns n."
    source := "base/io.jl:349-364 (unsafe_write docstring)"
    status := .proven, prop := ``Io.UnsafeWriteAppends, thm := some ``Io.unsafeWriteAppends },
  { id := "iocov-io-unsafe-read", juliaFile := "base/io.jl"
    juliaFns := ["unsafe_read(s::IO, p::Ptr{UInt8}, n::UInt)"]
    statement := "unsafe_read stores the next n bytes or throws EOFError."
    source := "base/io.jl:366-380 (unsafe_read docstring)"
    status := .proven, prop := ``Io.UnsafeReadNext, thm := some ``Io.unsafeReadNext },
  { id := "iocov-io-peek-union", juliaFile := "base/io.jl"
    juliaFns := ["peek(s::IO, ::Type{Union{}})"]
    statement := "peek of Union{} throws MethodError."
    source := "base/io.jl:389"
    status := .proven, prop := ``Io.PeekUnionThrows, thm := some ``Io.peekUnionThrows },
  { id := "iocov-io-peek-byte", juliaFile := "base/io.jl"
    juliaFns := ["peek(s)"]
    statement := "peek(s) returns the next byte without consuming it."
    source := "base/io.jl:382-391 (peek docstring)"
    status := .proven, prop := ``Io.PeekByteCorrect, thm := some ``Io.peekByteCorrect },
  { id := "iocov-io-open-do", juliaFile := "base/io.jl"
    juliaFns := ["open(f::Function, args...)"]
    statement := "open(f, args...) returns f(io) and closes io even when f throws."
    source := "base/io.jl:433-456 (open docstring)"
    status := .proven, prop := ``Io.OpenDoCloses, thm := some ``Io.openDoCloses },
  { id := "iocov-io-pipe-getproperty", juliaFile := "base/io.jl"
    juliaFns := ["getproperty(pipe::AbstractPipe, name)"]
    statement := "getproperty returns the field and type-asserts stream fields as IO."
    source := "base/io.jl:478-484"
    status := .proven, prop := ``Io.PipeGetpropertyCorrect, thm := some ``Io.pipeGetpropertyCorrect },
  { id := "iocov-io-pipe-iswritable", juliaFile := "base/io.jl"
    juliaFns := ["iswritable(io::AbstractPipe)"]
    statement := "iswritable of a pipe is that of its writer."
    source := "base/io.jl:489"
    status := .proven, prop := ``Io.PipeIswritable, thm := some ``Io.pipeIswritable_eq },
  { id := "iocov-io-pipe-flush", juliaFile := "base/io.jl"
    juliaFns := ["flush(io::AbstractPipe)", "closewrite(io::AbstractPipe)"]
    statement := "flush and closewrite of a pipe act on its writer only."
    source := "base/io.jl:496-498"
    status := .proven, prop := ``Io.PipeFlushWriter, thm := some ``Io.pipeFlushWriter },
  { id := "iocov-io-pipe-write-byte", juliaFile := "base/io.jl"
    juliaFns := ["write(io::AbstractPipe, byte::UInt8)"]
    statement := "write(pipe, b) appends b to the writer."
    source := "base/io.jl:500"
    status := .proven, prop := ``Io.PipeWriteByte, thm := some ``Io.pipeWriteByte_eq },
  { id := "iocov-io-pipe-writepartial", juliaFile := "base/io.jl"
    juliaFns := ["writepartial(io::AbstractPipe, x)"]
    statement := "writepartial(pipe, x) writes to the writer."
    source := "base/io.jl:501"
    status := .proven, prop := ``Io.PipeWritepartial, thm := some ``Io.pipeWritepartial_eq },
  { id := "iocov-io-write-from-pipe", juliaFile := "base/io.jl"
    juliaFns := ["write(to::IO, from::AbstractPipe)"]
    statement := "write(to, pipe) copies from the pipe reader."
    source := "base/io.jl:502"
    status := .proven, prop := ``Io.WriteFromPipeReader, thm := some ``Io.writeFromPipeReader },
  { id := "iocov-io-pipe-unsafe-write", juliaFile := "base/io.jl"
    juliaFns := ["unsafe_write(io::AbstractPipe, p, nb)"]
    statement := "unsafe_write(pipe, p, n) appends n bytes to the writer."
    source := "base/io.jl:503-505"
    status := .proven, prop := ``Io.PipeUnsafeWrite, thm := some ``Io.pipeUnsafeWrite_eq },
  { id := "iocov-io-pipe-buffer-writes", juliaFile := "base/io.jl"
    juliaFns := ["buffer_writes(io::AbstractPipe, args...)"]
    statement := "buffer_writes(pipe) is buffer_writes of its writer."
    source := "base/io.jl:506"
    status := .proven, prop := ``Io.PipeBufferWrites, thm := some ``Io.pipeBufferWrites_eq },
  { id := "iocov-io-pipe-reader-ops", juliaFile := "base/io.jl"
    juliaFns := ["mark, unmark, reset, ismarked, read, bytesavailable, reseteof, isreadable (io::AbstractPipe)"]
    statement := "The generated reader methods of a pipe act on its reader only."
    source := "base/io.jl:508-514"
    status := .proven, prop := ``Io.PipeReaderOps, thm := some ``Io.pipeReaderOps },
  { id := "iocov-io-pipe-readavailable", juliaFile := "base/io.jl"
    juliaFns := ["readavailable(io::AbstractPipe)"]
    statement := "readavailable(pipe) reads from the reader."
    source := "base/io.jl:517-519"
    status := .proven, prop := ``Io.PipeReadavailable, thm := some ``Io.pipeReadavailable_eq },
  { id := "iocov-io-pipe-read-byte", juliaFile := "base/io.jl"
    juliaFns := ["read(io::AbstractPipe, ::Type{UInt8})"]
    statement := "read(pipe, UInt8) reads the reader’s next byte."
    source := "base/io.jl:520-522"
    status := .proven, prop := ``Io.PipeReadByte, thm := some ``Io.pipeReadByte_eq },
  { id := "iocov-io-pipe-unsafe-read", juliaFile := "base/io.jl"
    juliaFns := ["unsafe_read(io::AbstractPipe, p, nb)"]
    statement := "unsafe_read(pipe, p, n) reads n bytes of the reader."
    source := "base/io.jl:523"
    status := .proven, prop := ``Io.PipeUnsafeRead, thm := some ``Io.pipeUnsafeRead_eq },
  { id := "iocov-io-pipe-forward", juliaFile := "base/io.jl"
    juliaFns := ["copyuntil(out, io::AbstractPipe, arg)", "readuntil_vector!(io::AbstractPipe, ...)", "readbytes!(io::AbstractPipe, ...)", "peek(io::AbstractPipe, T)", "wait_readnb(io::AbstractPipe, nb)"]
    statement := "These pipe methods forward their arguments to the pipe reader."
    source := "base/io.jl:524-535"
    status := .proven, prop := ``Io.PipeForwardReader, thm := some ``Io.pipeForwardReader },
  { id := "iocov-io-pipe-eof", juliaFile := "base/io.jl"
    juliaFns := ["eof(io::AbstractPipe)"]
    statement := "eof(pipe) is eof of its reader."
    source := "base/io.jl:536-538"
    status := .proven, prop := ``Io.PipeEof, thm := some ``Io.pipeEof_eq },
  { id := "iocov-io-pipe-isopen", juliaFile := "base/io.jl"
    juliaFns := ["isopen(io::AbstractPipe)"]
    statement := "A pipe is open while either side is open."
    source := "base/io.jl:540"
    status := .proven, prop := ``Io.PipeIsopen, thm := some ``Io.pipeIsopen_iff },
  { id := "iocov-io-pipe-close", juliaFile := "base/io.jl"
    juliaFns := ["close(io::AbstractPipe)"]
    statement := "close(pipe) closes both sides."
    source := "base/io.jl:541"
    status := .proven, prop := ``Io.PipeCloseBoth, thm := some ``Io.pipeCloseBoth },
  { id := "iocov-io-pipe-wait-close", juliaFile := "base/io.jl"
    juliaFns := ["wait_close(io::AbstractPipe)"]
    statement := "wait_close(pipe) waits for the writer, then the reader."
    source := "base/io.jl:542"
    status := .proven, prop := ``Io.PipeWaitClose, thm := some ``Io.pipeWaitClose_eq },
  { id := "iocov-io-isreadonly", juliaFile := "base/io.jl"
    juliaFns := ["isreadonly(s)"]
    statement := "isreadonly holds exactly for readable non-writable streams."
    source := "base/io.jl:893"
    status := .proven, prop := ``Io.IsreadonlyCorrect, thm := some ``Io.isreadonlyCorrect },
  { id := "iocov-io-write-fallback", juliaFile := "base/io.jl"
    juliaFns := ["write(io::IO, x)"]
    statement := "write of an unsupported value throws MethodError."
    source := "base/io.jl:897"
    status := .proven, prop := ``Io.WriteFallbackThrows, thm := some ``Io.writeFallbackThrows },
  { id := "iocov-io-write-many", juliaFile := "base/io.jl"
    juliaFns := ["write(io::IO, x1, xs...)"]
    statement := "write(io, x1, xs...) writes each argument in order and returns the total."
    source := "base/io.jl:875-905 (write docstring)"
    status := .proven, prop := ``Io.WriteManyCorrect, thm := some ``Io.writeManyCorrect },
  { id := "iocov-io-unsafe-write-ptr", juliaFile := "base/io.jl"
    juliaFns := ["unsafe_write(s::IO, p::Ref{T}, n::Integer)", "unsafe_write(s::IO, p::Ptr, n::Integer)"]
    statement := "unsafe_write converts n to UInt and writes n bytes."
    source := "base/io.jl:907-909"
    status := .proven, prop := ``Io.UnsafeWritePtrCorrect, thm := some ``Io.unsafeWritePtrCorrect },
  { id := "iocov-io-write-ref", juliaFile := "base/io.jl"
    juliaFns := ["write(s::IO, x::Ref{T})"]
    statement := "write(s, ::Ref) throws for Ptr, writes isbits contents, and otherwise writes x[]."
    source := "base/io.jl:910-917"
    status := .proven, prop := ``Io.WriteRefCorrect, thm := some ``Io.writeRefCorrect },
  { id := "iocov-io-write-read-int8", juliaFile := "base/io.jl"
    juliaFns := ["write(s::IO, x::Int8)", "read(s::IO, ::Type{Int8})"]
    statement := "An Int8 written and read back is unchanged."
    source := "base/io.jl:918,1009 (invariant)"
    status := .proven, prop := ``Io.WriteReadInt8, thm := some ``Io.writeReadInt8 },
  { id := "iocov-io-write-read-int", juliaFile := "base/io.jl"
    juliaFns := ["write(s::IO, x::Union{Int16,...})", "read(s::IO, T::Union{Type{Int16},...})"]
    statement := "Integers are written as their little-endian bytes and read back unchanged."
    source := "base/io.jl:919-921,1010-1014 (invariant)"
    status := .proven, prop := ``Io.WriteReadInt, thm := some ``Io.writeReadInt },
  { id := "iocov-io-write-read-float", juliaFile := "base/io.jl"
    juliaFns := ["write(s::IO, x::Union{Float16,Float32,Float64})", "read(s::IO, T::Union{Type{Float16},...})"]
    statement := "Float bit patterns are written little-endian and read back unchanged."
    source := "base/io.jl:919-921,1010-1014 (invariant)"
    status := .proven, prop := ``Io.WriteReadFloat, thm := some ``Io.writeReadFloat },
  { id := "iocov-io-write-read-bool", juliaFile := "base/io.jl"
    juliaFns := ["write(s::IO, x::Bool)"]
    statement := "A Bool written as 0 or 1 reads back unchanged."
    source := "base/io.jl:923"
    status := .proven, prop := ``Io.WriteReadBool, thm := some ``Io.writeReadBool },
  { id := "iocov-io-read-bool", juliaFile := "base/io.jl"
    juliaFns := ["read(s::IO, ::Type{Bool})"]
    statement := "read(s, Bool) is true for a nonzero byte."
    source := "base/io.jl:1016"
    status := .proven, prop := ``Io.ReadBoolNonzero, thm := some ``Io.readBoolNonzero },
  { id := "iocov-io-write-read-ptr", juliaFile := "base/io.jl"
    juliaFns := ["write(to::IO, p::Ptr)", "read(s::IO, ::Type{Ptr{T}})"]
    statement := "A pointer is written as UInt and read back unchanged."
    source := "base/io.jl:924,1017"
    status := .proven, prop := ``Io.WriteReadPtr, thm := some ``Io.writeReadPtr },
  { id := "iocov-io-write-array", juliaFile := "base/io.jl"
    juliaFns := ["write(s::IO, A::AbstractArray)"]
    statement := "write(s, A) writes each element’s bytes and throws for non-isbits elements."
    source := "base/io.jl:926-938"
    status := .proven, prop := ``Io.WriteArrayCorrect, thm := some ``Io.writeArrayCorrect },
  { id := "iocov-io-write-strided", juliaFile := "base/io.jl"
    juliaFns := ["write(s::IO, A::StridedArray)"]
    statement := "Strided write dispatch: contiguous is one write, other strides fall back, contiguous columns are written per column."
    source := "base/io.jl:940-971"
    status := .proven, prop := ``Io.WriteStridedCorrect, thm := some ``Io.writeStridedCorrect },
  { id := "iocov-io-write-symbol", juliaFile := "base/io.jl"
    juliaFns := ["write(io::IO, s::Symbol)"]
    statement := "write(io, s::Symbol) writes the name bytes."
    source := "base/io.jl:984-987"
    status := .proven, prop := ``Io.WriteSymbolCorrect, thm := some ``Io.writeSymbolCorrect },
  { id := "iocov-io-write-from-io", juliaFile := "base/io.jl"
    juliaFns := ["write(to::IO, from::IO)"]
    statement := "write(to, from) copies all of from and returns the count."
    source := "base/io.jl:989-995"
    status := .proven, prop := ``Io.WriteFromIOCorrect, thm := some ``Io.writeFromIOCorrect },
  { id := "iocov-io-unsafe-read-ptr", juliaFile := "base/io.jl"
    juliaFns := ["unsafe_read(s::IO, p::Ref{T}, n)", "unsafe_read(s::IO, p::Ptr, n)"]
    statement := "unsafe_read converts n to UInt and reads n bytes."
    source := "base/io.jl:997-998"
    status := .proven, prop := ``Io.UnsafeReadPtrCorrect, thm := some ``Io.unsafeReadPtrCorrect },
  { id := "iocov-io-read-ref", juliaFile := "base/io.jl"
    juliaFns := ["read!(s::IO, x::Ref{T})"]
    statement := "read!(s, ::Ref) throws for Ptr, reads isbits contents, and otherwise stores read(s, T)."
    source := "base/io.jl:999-1007"
    status := .proven, prop := ``Io.ReadRefCorrect, thm := some ``Io.readRefCorrect },
  { id := "iocov-io-read-array", juliaFile := "base/io.jl"
    juliaFns := ["read!(s::IO, A::AbstractArray)"]
    statement := "read! fills consecutive elements; the contiguous path agrees with the element loop."
    source := "base/io.jl:1019-1037"
    status := .proven, prop := ``Io.ReadArrayCorrect, thm := some ``Io.readArrayCorrect },
  { id := "iocov-io-write-bitarray", juliaFile := "base/io.jl"
    juliaFns := ["write(s::IO, B::BitArray)"]
    statement := "write(s, B::BitArray) writes its 64-bit chunks."
    source := "base/io.jl:1043-1046"
    status := .proven, prop := ``Io.WriteBitArrayChunks, thm := some ``Io.writeBitArrayChunks },
  { id := "iocov-io-read-bitarray", juliaFile := "base/io.jl"
    juliaFns := ["read!(s::IO, B::BitArray)"]
    statement := "read! of a BitArray throws when bits past length(B) are set and returns the chunks otherwise."
    source := "base/io.jl:1047-1057"
    status := .proven, prop := ``Io.ReadBitArrayCorrect, thm := some ``Io.readBitArrayCorrect },
  { id := "iocov-io-read-strided", juliaFile := "base/io.jl"
    juliaFns := ["read!(s::IO, A::StridedArray)"]
    statement := "Strided read! dispatch: non-isbits and contiguous use the generic method, stride-1 vectors one read."
    source := "base/io.jl:1059-1089"
    status := .proven, prop := ``Io.ReadStridedCorrect, thm := some ``Io.readStridedCorrect },
  { id := "iocov-io-char-roundtrip", juliaFile := "base/io.jl"
    juliaFns := ["write(io::IO, c::Char)", "read(io::IO, ::Type{Char})"]
    statement := "write(io, c) emits the UTF-8 bytes of c and read(io, Char) decodes them back."
    source := "base/io.jl:973-980,1091-1106 (invariant)"
    status := .proven, prop := ``Io.CharRoundTrip, thm := some ``Io.charRoundTrip },
  { id := "iocov-io-read-type-fallback", juliaFile := "base/io.jl"
    juliaFns := ["read(s::IO, T::Type)"]
    statement := "Reading an unsupported type throws."
    source := "base/io.jl:1345"
    status := .proven, prop := ``Io.ReadTypeFallbackThrows, thm := some ``Io.readTypeFallbackThrows },
  { id := "iocov-io-mark", juliaFile := "base/io.jl"
    juliaFns := ["mark(io::IO)"]
    statement := "mark returns the position and marks the stream."
    source := "base/io.jl:1567-1577 (mark docstring)"
    status := .proven, prop := ``Io.MarkCorrect, thm := some ``Io.markCorrect },
  { id := "iocov-io-unmark", juliaFile := "base/io.jl"
    juliaFns := ["unmark(io::IO)"]
    statement := "unmark returns whether the stream was marked and removes the mark."
    source := "base/io.jl:1579-1590 (unmark docstring)"
    status := .proven, prop := ``Io.UnmarkCorrect, thm := some ``Io.unmarkCorrect },
  { id := "iocov-io-reset", juliaFile := "base/io.jl"
    juliaFns := ["reset(io::T)"]
    statement := "reset returns to the marked position and removes the mark, throwing when unmarked."
    source := "base/io.jl:1592-1606 (reset docstring)"
    status := .proven, prop := ``Io.ResetCorrect, thm := some ``Io.resetCorrect },
  { id := "iocov-io-ismarked", juliaFile := "base/io.jl"
    juliaFns := ["ismarked(io::IO)"]
    statement := "ismarked holds exactly when mark >= 0."
    source := "base/io.jl:1608-1615 (ismarked docstring)"
    status := .proven, prop := ``Io.IsmarkedCorrect, thm := some ``Io.ismarkedCorrect },
  { id := "iocov-copyline-cr-crlf", juliaFile := "base/io.jl"
    juliaFns := ["copyline(::IO, ::IO)"]
    statement := "copyline(out, s) copies the same line as readline(s) returns, for any output stream."
    source := "base/io.jl:725-728 (copyline docstring)"
    status := .refuted, prop := ``Io.CopylineConsistent, thm := some ``Io.copylineConsistent_refuted
    issue := "none found (queries: copyline, copyline CRLF, readline carriage return)"
    notes := "After a carriage return the next byte is written without being checked for the start of CRLF, so x CR CR LF gives x CR CR. Same on 1.13.2." },
  { id := "iocov-io-copyline-plain", juliaFile := "base/io.jl"
    juliaFns := ["copyline(::IO, ::IO)"]
    statement := "On a line without carriage returns, copyline copies the bytes before the newline and consumes the newline."
    source := "base/io.jl:719-779 (copyline docstring)"
    status := .proven, prop := ``Io.CopylinePlain, thm := some ``Io.copylinePlain },
  { id := "iocov-libc-rawfd-int", juliaFile := "base/libc.jl"
    juliaFns := ["RawFD(::Integer)"]
    statement := "RawFD(fd) accepts exactly the Int32 range and throws InexactError otherwise."
    source := "base/libc.jl:24-35 (RawFD docstring)"
    status := .proven, prop := ``Libc.RawFDCorrect_1, thm := some ``Libc.rawFDCorrect_1 },
  { id := "iocov-libc-rawfd-id", juliaFile := "base/libc.jl"
    juliaFns := ["RawFD(::RawFD)", "cconvert(::Type{Cint}, ::RawFD)"]
    statement := "RawFD(fd::RawFD) returns fd and cconvert(Cint, fd) gives back the same descriptor number."
    source := "base/libc.jl:36-37 (invariant)"
    status := .proven, prop := ``Libc.RawFDCorrect_2, thm := some ``Libc.rawFDCorrect_2 },
  { id := "iocov-libc-dup-ok", juliaFile := "base/libc.jl"
    juliaFns := ["dup(::RawFD)"]
    statement := "dup(x) returns the result of the C dup call."
    source := "base/libc.jl:40-46 (dup docstring)"
    status := .proven, prop := ``Libc.RawFDCorrect_3, thm := some ``Libc.rawFDCorrect_3 },
  { id := "iocov-dup-unchecked", juliaFile := "base/libc.jl"
    juliaFns := ["dup(::RawFD)"]
    statement := "dup(fd) reports failure of the dup system call instead of returning RawFD(-1)."
    source := "base/libc.jl:40-43 (dup docstring)"
    status := .refuted, prop := ``Libc.DupChecked, thm := some ``Libc.dupChecked_refuted
    issue := "none found (queries: Libc.dup, dup RawFD)"
    notes := "dup(x::RawFD) has no systemerror check, unlike dup(src, target). Same on 1.13.2." },
  { id := "iocov-libc-dup2", juliaFile := "base/libc.jl"
    juliaFns := ["dup(::RawFD, ::RawFD)"]
    statement := "dup(src, target) throws SystemError exactly when dup2 returns -1."
    source := "base/libc.jl:40-49 (dup docstring)"
    status := .proven, prop := ``Libc.RawFDCorrect_4, thm := some ``Libc.rawFDCorrect_4 },
  { id := "iocov-libc-show-rawfd", juliaFile := "base/libc.jl"
    juliaFns := ["show(::IO, ::RawFD)"]
    statement := "show prints RawFD(n) with the descriptor number."
    source := "base/libc.jl:51 (invariant)"
    status := .proven, prop := ``Libc.RawFDCorrect_5, thm := some ``Libc.rawFDCorrect_5 },
  { id := "iocov-libc-modestr", juliaFile := "base/libc.jl"
    juliaFns := ["modestr(::Bool, ::Bool)"]
    statement := "modestr gives r, r+ or w and throws when neither readable nor writable."
    source := "base/libc.jl:124"
    status := .proven, prop := ``Libc.FileCorrect_1, thm := some ``Libc.fileCorrect_1 },
  { id := "iocov-libc-modestr-io", juliaFile := "base/libc.jl"
    juliaFns := ["modestr(::IO)"]
    statement := "modestr(s) uses isreadable(s) and iswritable(s)."
    source := "base/libc.jl:123"
    status := .proven, prop := ``Libc.FileCorrect_2, thm := some ``Libc.fileCorrect_2 },
  { id := "iocov-libc-file-fd", juliaFile := "base/libc.jl"
    juliaFns := ["FILE(::RawFD, mode)"]
    statement := "FILE(fd, mode) throws SystemError when fdopen returns NULL and wraps the pointer otherwise."
    source := "base/libc.jl:115-130 (FILE docstring)"
    status := .proven, prop := ``Libc.FileCorrect_3, thm := some ``Libc.fileCorrect_3 },
  { id := "iocov-libc-seek-file", juliaFile := "base/libc.jl"
    juliaFns := ["seek(::FILE, ::Integer)"]
    statement := "seek(h, offset) throws SystemError when fseek fails and returns h otherwise."
    source := "base/libc.jl:141-145"
    status := .proven, prop := ``Libc.FileCorrect_4, thm := some ``Libc.fileCorrect_4 },
  { id := "iocov-libc-file-io", juliaFile := "base/libc.jl"
    juliaFns := ["FILE(::IO)"]
    statement := "FILE(s) of a stream that is neither readable nor writable throws ArgumentError."
    source := "base/libc.jl:132-136"
    status := .proven, prop := ``Libc.FileCorrect_5, thm := some ``Libc.fileCorrect_5 },
  { id := "iocov-libc-unsafe-convert-file", juliaFile := "base/libc.jl"
    juliaFns := ["unsafe_convert(::Type{Ptr{FILE}}, ::FILE)"]
    statement := "unsafe_convert returns the FILE pointer."
    source := "base/libc.jl:138"
    status := .proven, prop := ``Libc.FileCorrect_6, thm := some ``Libc.fileCorrect_6 },
  { id := "iocov-libc-close-file", juliaFile := "base/libc.jl"
    juliaFns := ["close(::FILE)"]
    statement := "close(f) throws SystemError exactly when fclose fails."
    source := "base/libc.jl:139"
    status := .proven, prop := ``Libc.FileCorrect_7, thm := some ``Libc.fileCorrect_7 },
  { id := "iocov-libc-position-file", juliaFile := "base/libc.jl"
    juliaFns := ["position(::FILE)"]
    statement := "position(h) returns ftell(h)."
    source := "base/libc.jl:147"
    status := .proven, prop := ``Libc.FileCorrect_8, thm := some ``Libc.fileCorrect_8 },
  { id := "iocov-libc-flush-cstdio", juliaFile := "base/libc.jl"
    juliaFns := ["flush_cstdio()"]
    statement := "flush_cstdio calls jl_flush_cstdio once."
    source := "base/libc.jl:150-156 (flush_cstdio docstring)"
    status := .proven, prop := ``Libc.FileCorrect_9, thm := some ``Libc.fileCorrect_9 },
  { id := "iocov-libc-systemsleep", juliaFile := "base/libc.jl"
    juliaFns := ["systemsleep(::Real)"]
    statement := "systemsleep passes an in-range microsecond count to usleep."
    source := "base/libc.jl:162"
    status := .proven, prop := ``Libc.TimeCorrect_1, thm := some ``Libc.timeCorrect_1 },
  { id := "iocov-systemsleep-large", juliaFile := "base/libc.jl"
    juliaFns := ["systemsleep(::Real)"]
    statement := "systemsleep(s) sleeps for any nonnegative number of seconds s."
    source := "base/libc.jl:172-174 (sleep docstring)"
    status := .refuted, prop := ``Libc.SystemsleepAny, thm := some ``Libc.systemsleepAny_refuted
    issue := "none found (queries: systemsleep InexactError)"
    notes := "UInt32(round(s*1e6)) throws InexactError for s >= 4295. Same on 1.13.2." },
  { id := "iocov-libc-timeval", juliaFile := "base/libc.jl"
    juliaFns := ["TimeVal()"]
    statement := "TimeVal() returns the time of day or throws when jl_gettimeofday fails."
    source := "base/libc.jl:187-192"
    status := .proven, prop := ``Libc.TimeCorrect_3, thm := some ``Libc.timeCorrect_3 },
  { id := "iocov-libc-tmstruct9", juliaFile := "base/libc.jl"
    juliaFns := ["TmStruct(sec, min, hour, mday, month, year, wday, yday, isdst)", "TmStruct()"]
    statement := "The field constructor stores Int32 fields and zeroes the rest; TmStruct() has 14 zero fields."
    source := "base/libc.jl:217-219"
    status := .proven, prop := ``Libc.TimeCorrect_4, thm := some ``Libc.timeCorrect_4 },
  { id := "iocov-libc-tmstruct0", juliaFile := "base/libc.jl"
    juliaFns := ["TmStruct()"]
    statement := "TmStruct() has all fields zero."
    source := "base/libc.jl:219"
    status := .proven, prop := ``Libc.TimeCorrect_5, thm := some ``Libc.timeCorrect_5 },
  { id := "iocov-libc-tmstruct-time", juliaFile := "base/libc.jl"
    juliaFns := ["TmStruct(::Real)"]
    statement := "TmStruct(t) is localtime_r of the Int64 floor of t."
    source := "base/libc.jl:220-226"
    status := .proven, prop := ``Libc.TimeCorrect_6, thm := some ``Libc.timeCorrect_6 },
  { id := "iocov-strftime-long", juliaFile := "base/libc.jl"
    juliaFns := ["strftime(::AbstractString, ::TmStruct)"]
    statement := "strftime(fmt, tm) returns the formatted time for every format, including results of 128 characters or more."
    source := "base/libc.jl:229-245 (strftime docstring)"
    status := .refuted, prop := ``Libc.StrftimeFormats, thm := some ``Libc.strftimeFormats_refuted
    issue := "none found (queries: strftime long, strftime empty, strftime buffer)"
    notes := "The buffer holds 128 Cwchar_t and n == 0 returns \"\"; longer results silently become \"\". Same on 1.13.2." },
  { id := "iocov-libc-strftime", juliaFile := "base/libc.jl"
    juliaFns := ["strftime(::AbstractString, ::TmStruct)"]
    statement := "strftime returns the C output for results shorter than 128 characters."
    source := "base/libc.jl:229-245 (strftime docstring)"
    status := .proven, prop := ``Libc.StrftimeWrappers_1, thm := some ``Libc.strftimeWrappers_1 },
  { id := "iocov-libc-strftime-real", juliaFile := "base/libc.jl"
    juliaFns := ["strftime(::AbstractString, ::Real)"]
    statement := "strftime(fmt, t) formats TmStruct(t)."
    source := "base/libc.jl:237"
    status := .proven, prop := ``Libc.StrftimeWrappers_2, thm := some ``Libc.strftimeWrappers_2 },
  { id := "iocov-libc-strftime-default", juliaFile := "base/libc.jl"
    juliaFns := ["strftime(t)"]
    statement := "strftime(t) uses the format %c."
    source := "base/libc.jl:236"
    status := .proven, prop := ``Libc.StrftimeWrappers_3, thm := some ``Libc.strftimeWrappers_3 },
  { id := "iocov-libc-strptime", juliaFile := "base/libc.jl"
    juliaFns := ["strptime(::AbstractString, ::AbstractString)", "shouldcallmktime"]
    statement := "strptime returns the parsed TmStruct or throws ArgumentError when parsing fails."
    source := "base/libc.jl:248-307 (strptime docstring)"
    status := .proven, prop := ``Libc.StrptimeCorrect_1, thm := some ``Libc.strptimeCorrect_1 },
  { id := "iocov-libc-strptime-default", juliaFile := "base/libc.jl"
    juliaFns := ["strptime(::AbstractString)"]
    statement := "strptime(timestr) parses with %c."
    source := "base/libc.jl:257"
    status := .proven, prop := ``Libc.StrptimeCorrect_2, thm := some ``Libc.strptimeCorrect_2 },
  { id := "iocov-libc-time-tm", juliaFile := "base/libc.jl"
    juliaFns := ["time(::TmStruct)"]
    statement := "time(tm) is mktime(tm)."
    source := "base/libc.jl:310-316 (time docstring)"
    status := .proven, prop := ``Libc.StrptimeCorrect_3, thm := some ``Libc.strptimeCorrect_3 },
  { id := "iocov-libc-time-now", juliaFile := "base/libc.jl"
    juliaFns := ["time()"]
    statement := "time() returns jl_clock_now."
    source := "base/libc.jl:319-325 (time docstring)"
    status := .proven, prop := ``Libc.StrptimeCorrect_4, thm := some ``Libc.strptimeCorrect_4 },
  { id := "iocov-libc-getpid", juliaFile := "base/libc.jl"
    juliaFns := ["getpid()"]
    statement := "getpid returns uv_os_getpid."
    source := "base/libc.jl:328-334 (getpid docstring)"
    status := .proven, prop := ``Libc.ProcessQueriesCorrect_1, thm := some ``Libc.processQueriesCorrect_1 },
  { id := "iocov-libc-gethostname", juliaFile := "base/libc.jl"
    juliaFns := ["gethostname()"]
    statement := "gethostname returns the NUL-terminated name or throws SystemError."
    source := "base/libc.jl:337-352 (gethostname docstring)"
    status := .proven, prop := ``Libc.ProcessQueriesCorrect_2, thm := some ``Libc.processQueriesCorrect_2 },
  { id := "iocov-libc-errno", juliaFile := "base/libc.jl"
    juliaFns := ["errno()"]
    statement := "errno() returns the current errno."
    source := "base/libc.jl:360-366 (errno docstring)"
    status := .proven, prop := ``Libc.ProcessQueriesCorrect_3, thm := some ``Libc.processQueriesCorrect_3 },
  { id := "iocov-libc-errno-set", juliaFile := "base/libc.jl"
    juliaFns := ["errno(::Integer)"]
    statement := "errno(e) sets e converted to Cint, throwing InexactError when out of range."
    source := "base/libc.jl:360-367 (errno docstring)"
    status := .proven, prop := ``Libc.ProcessQueriesCorrect_4, thm := some ``Libc.processQueriesCorrect_4 },
  { id := "iocov-libc-strerror", juliaFile := "base/libc.jl"
    juliaFns := ["strerror(::Integer)"]
    statement := "strerror(e) returns the C message for e."
    source := "base/libc.jl:369-374 (strerror docstring)"
    status := .proven, prop := ``Libc.ProcessQueriesCorrect_5, thm := some ``Libc.processQueriesCorrect_5 },
  { id := "iocov-libc-strerror0", juliaFile := "base/libc.jl"
    juliaFns := ["strerror()"]
    statement := "strerror() is strerror(errno())."
    source := "base/libc.jl:375"
    status := .proven, prop := ``Libc.ProcessQueriesCorrect_6, thm := some ``Libc.processQueriesCorrect_6 },
  { id := "iocov-libc-free", juliaFile := "base/libc.jl"
    juliaFns := ["free(::Ptr)", "free(::Cstring)", "free(::Cwstring)"]
    statement := "free passes the pointer to the C free."
    source := "base/libc.jl:414-425 (free docstring)"
    status := .proven, prop := ``Libc.MemoryCorrect_1, thm := some ``Libc.memoryCorrect_1 },
  { id := "iocov-libc-malloc", juliaFile := "base/libc.jl"
    juliaFns := ["malloc(::Integer)"]
    statement := "malloc passes a Csize_t size to the C malloc."
    source := "base/libc.jl:427-432 (malloc docstring)"
    status := .proven, prop := ``Libc.MemoryCorrect_2, thm := some ``Libc.memoryCorrect_2 },
  { id := "iocov-libc-realloc", juliaFile := "base/libc.jl"
    juliaFns := ["realloc(::Ptr, ::Integer)"]
    statement := "realloc passes the pointer and a Csize_t size to the C realloc."
    source := "base/libc.jl:435-442 (realloc docstring)"
    status := .proven, prop := ``Libc.MemoryCorrect_4, thm := some ``Libc.memoryCorrect_4 },
  { id := "iocov-libc-calloc", juliaFile := "base/libc.jl"
    juliaFns := ["calloc(::Integer, ::Integer)"]
    statement := "calloc passes Csize_t counts to the C calloc."
    source := "base/libc.jl:445-449 (calloc docstring)"
    status := .proven, prop := ``Libc.MemoryCorrect_5, thm := some ``Libc.memoryCorrect_5 },
  { id := "iocov-libc-getrandom", juliaFile := "base/libc.jl"
    juliaFns := ["getrandom!", "_make_uint64_seed()"]
    statement := "getrandom! throws on libuv failure and fills the buffer otherwise."
    source := "base/libc.jl:456-462"
    status := .proven, prop := ``Libc.RandomCorrect_1, thm := some ``Libc.randomCorrect_1 },
  { id := "iocov-libc-rand", juliaFile := "base/libc.jl"
    juliaFns := ["rand()", "rand(::Type{UInt32})"]
    statement := "rand() returns a UInt32 and rand(UInt32) is rand()."
    source := "base/libc.jl:465-473 (rand docstring)"
    status := .proven, prop := ``Libc.RandomCorrect_2, thm := some ``Libc.randomCorrect_2 },
  { id := "iocov-libc-rand-float", juliaFile := "base/libc.jl"
    juliaFns := ["rand(::Type{Float64})"]
    statement := "rand(Float64) lies in [0, 1)."
    source := "base/libc.jl:465-474 (rand docstring)"
    status := .proven, prop := ``Libc.RandomCorrect_3, thm := some ``Libc.randomCorrect_3 },
  { id := "iocov-libc-srand", juliaFile := "base/libc.jl"
    juliaFns := ["srand"]
    statement := "srand seeds with the seed wrapped to UInt64."
    source := "base/libc.jl:476-483 (srand docstring)"
    status := .proven, prop := ``Libc.RandomCorrect_4, thm := some ``Libc.randomCorrect_4 },
  { id := "iocov-libc-mkfifo", juliaFile := "base/libc.jl"
    juliaFns := ["mkfifo", "Cpasswd()", "Cgroup()"]
    statement := "mkfifo returns the path or throws SystemError; Cpasswd() and Cgroup() are empty."
    source := "base/libc.jl:486-525 (mkfifo docstring)"
    status := .proven, prop := ``Libc.UsersCorrect_1, thm := some ``Libc.usersCorrect_1 },
  { id := "iocov-libc-getpw", juliaFile := "base/libc.jl"
    juliaFns := ["getpw()"]
    statement := "getpw throws on libuv failure and converts the entry otherwise."
    source := "base/libc.jl:543-559"
    status := .proven, prop := ``Libc.UsersCorrect_2, thm := some ``Libc.usersCorrect_2 },
  { id := "iocov-libc-getpwuid", juliaFile := "base/libc.jl"
    juliaFns := ["getpwuid"]
    statement := "getpwuid returns nothing on failure when throw_error is false."
    source := "base/libc.jl:561-579"
    status := .proven, prop := ``Libc.UsersCorrect_4, thm := some ``Libc.usersCorrect_4 },
  { id := "iocov-libc-getgrgid", juliaFile := "base/libc.jl"
    juliaFns := ["getgrgid"]
    statement := "getgrgid throws on failure when throw_error is true."
    source := "base/libc.jl:581-604"
    status := .proven, prop := ``Libc.UsersCorrect_6, thm := some ``Libc.usersCorrect_6 },
  { id := "iocov-libc-ids", juliaFile := "base/libc.jl"
    juliaFns := ["getuid()", "geteuid()", "getegid()"]
    statement := "getuid, geteuid and getegid return their C call."
    source := "base/libc.jl:606-608"
    status := .proven, prop := ``Libc.UsersCorrect_8, thm := some ``Libc.usersCorrect_8 },
  { id := "iocov-libdl-dlsym-null", juliaFile := "base/libdl.jl"
    juliaFns := ["dlsym"]
    statement := "dlsym throws for a NULL handle."
    source := "base/libdl.jl:50-72 (dlsym docstring)"
    status := .proven, prop := ``Libdl.DlsymCorrect_1, thm := some ``Libdl.dlsymCorrect_1 },
  { id := "iocov-libdl-dlsym-found", juliaFile := "base/libdl.jl"
    juliaFns := ["dlsym"]
    statement := "dlsym returns the pointer of a found symbol."
    source := "base/libdl.jl:50-72 (dlsym docstring)"
    status := .proven, prop := ``Libdl.DlsymCorrect_3, thm := some ``Libdl.dlsymCorrect_3 },
  { id := "iocov-libdl-dlsym-missing", juliaFile := "base/libdl.jl"
    juliaFns := ["dlsym"]
    statement := "dlsym returns nothing for a missing symbol with throw_error=false."
    source := "base/libdl.jl:50-72 (dlsym docstring)"
    status := .proven, prop := ``Libdl.DlsymCorrect_2, thm := some ``Libdl.dlsymCorrect_2 },
  { id := "iocov-libdl-dlsym-e", juliaFile := "base/libdl.jl"
    juliaFns := ["dlsym_e"]
    statement := "dlsym_e returns C_NULL on lookup failure."
    source := "base/libdl.jl:74-82 (dlsym_e docstring)"
    status := .proven, prop := ``Libdl.DlsymCorrect_4, thm := some ``Libdl.dlsymCorrect_4 },
  { id := "iocov-libdl-dlopen-missing", juliaFile := "base/libdl.jl"
    juliaFns := ["dlopen(::AbstractString, flags)"]
    statement := "dlopen returns nothing when loading fails with throw_error=false."
    source := "base/libdl.jl:84-127 (dlopen docstring)"
    status := .proven, prop := ``Libdl.DlopenCorrect_1, thm := some ``Libdl.dlopenCorrect_1 },
  { id := "iocov-libdl-dlopen-sym", juliaFile := "base/libdl.jl"
    juliaFns := ["dlopen(::Symbol, flags)"]
    statement := "dlopen(::Symbol) is dlopen(string(s))."
    source := "base/libdl.jl:118-119"
    status := .proven, prop := ``Libdl.DlopenCorrect_4, thm := some ``Libdl.dlopenCorrect_4 },
  { id := "iocov-libdl-dlclose", juliaFile := "base/libdl.jl"
    juliaFns := ["dlclose(::Ptr)"]
    statement := "dlclose returns whether jl_dlclose returned 0."
    source := "base/libdl.jl:164-171 (dlclose docstring)"
    status := .proven, prop := ``Libdl.DlopenCorrect_6, thm := some ``Libdl.dlopenCorrect_6 },
  { id := "iocov-libdl-dlclose-nothing", juliaFile := "base/libdl.jl"
    juliaFns := ["dlclose(::Nothing)"]
    statement := "dlclose(nothing) does nothing."
    source := "base/libdl.jl:173-190 (dlclose docstring)"
    status := .proven, prop := ``Libdl.DlopenCorrect_5, thm := some ``Libdl.dlopenCorrect_5 },
  { id := "iocov-libdl-dlopen-do", juliaFile := "base/libdl.jl"
    juliaFns := ["dlopen(f::Function, name, args...)"]
    statement := "The do-block dlopen applies f to the handle and closes it."
    source := "base/libdl.jl:129-154 (dlopen docstring)"
    status := .proven, prop := ``Libdl.DlopenCorrect_8, thm := some ``Libdl.dlopenCorrect_8 },
  { id := "iocov-libdl-dlopen-e", juliaFile := "base/libdl.jl"
    juliaFns := ["dlopen_e"]
    statement := "dlopen_e returns C_NULL when loading fails."
    source := "base/libdl.jl:156-162 (dlopen_e docstring)"
    status := .proven, prop := ``Libdl.DlopenCorrect_9, thm := some ``Libdl.dlopenCorrect_9 },
  { id := "iocov-libdl-find-library", juliaFile := "base/libdl.jl"
    juliaFns := ["find_library(libnames, extrapaths)"]
    statement := "find_library returns \"\" only when no name opens, directly or under an extra path, and otherwise an openable candidate."
    source := "base/libdl.jl:193-218 (find_library docstring)"
    status := .proven, prop := ``Libdl.FindLibraryDoc, thm := some ``Libdl.findLibraryDoc },
  { id := "iocov-libdl-find-library-one", juliaFile := "base/libdl.jl"
    juliaFns := ["find_library(libname, extrapaths)"]
    statement := "find_library(name, extrapaths) is find_library([name], extrapaths)."
    source := "base/libdl.jl:219-220"
    status := .proven, prop := ``Libdl.FindLibraryWrapper, thm := some ``Libdl.findLibraryWrapper },
  { id := "iocov-libdl-dlpath-handle", juliaFile := "base/libdl.jl"
    juliaFns := ["dlpath(::Ptr{Cvoid})"]
    statement := "dlpath(handle) returns the path of a non-NULL handle."
    source := "base/libdl.jl:222-233 (dlpath docstring)"
    status := .proven, prop := ``Libdl.DlpathCorrect_2, thm := some ``Libdl.dlpathCorrect_2 },
  { id := "iocov-libdl-dlpath-name", juliaFile := "base/libdl.jl"
    juliaFns := ["dlpath(::Union{AbstractString,Symbol})"]
    statement := "dlpath(name) opens the library and returns its path."
    source := "base/libdl.jl:235-250 (dlpath docstring)"
    status := .proven, prop := ``Libdl.DlpathCorrect_3, thm := some ``Libdl.dlpathCorrect_3 },
  { id := "iocov-libdl-dllist", juliaFile := "base/libdl.jl"
    juliaFns := ["dllist()"]
    statement := "dllist returns the loaded-library list."
    source := "base/libdl.jl:253-294 (dllist docstring)"
    status := .proven, prop := ``Libdl.DlpathCorrect_4, thm := some ``Libdl.dlpathCorrect_4 },
  { id := "iocov-libdl-llp-ctor", juliaFile := "base/libdl.jl"
    juliaFns := ["LazyLibraryPath(pieces...)"]
    statement := "LazyLibraryPath stores its pieces."
    source := "base/libdl.jl:297-317 (LazyLibraryPath docstring)"
    status := .proven, prop := ``Libdl.LazyLibraryPathCorrect_1, thm := some ``Libdl.lazyLibraryPathCorrect_1 },
  { id := "iocov-libdl-llp-string", juliaFile := "base/libdl.jl"
    juliaFns := ["string(::LazyLibraryPath)"]
    statement := "string joins the evaluated pieces with joinpath."
    source := "base/libdl.jl:297-319 (LazyLibraryPath docstring)"
    status := .proven, prop := ``Libdl.LazyLibraryPathCorrect_3, thm := some ``Libdl.lazyLibraryPathCorrect_3 },
  { id := "iocov-libdl-llp-cconvert", juliaFile := "base/libdl.jl"
    juliaFns := ["cconvert(::Type{Cstring}, ::LazyLibraryPath)"]
    statement := "cconvert gives the string of the path."
    source := "base/libdl.jl:320"
    status := .proven, prop := ``Libdl.LazyLibraryPathCorrect_7, thm := some ``Libdl.lazyLibraryPathCorrect_7 },
  { id := "iocov-libdl-llp-print", juliaFile := "base/libdl.jl"
    juliaFns := ["print(::IO, ::LazyLibraryPath)"]
    statement := "print writes string(llp)."
    source := "base/libdl.jl:322"
    status := .proven, prop := ``Libdl.LazyLibraryPathCorrect_2, thm := some ``Libdl.lazyLibraryPathCorrect_2 },
  { id := "iocov-libdl-bundled", juliaFile := "base/libdl.jl"
    juliaFns := ["BundledLazyLibraryPath", "string(::PrivateShlibdirGetter)"]
    statement := "BundledLazyLibraryPath(sub) stringifies as joinpath(private_shlibdir(), sub)."
    source := "base/libdl.jl:338-356"
    status := .proven, prop := ``Libdl.LazyLibraryPathCorrect_4, thm := some ``Libdl.lazyLibraryPathCorrect_4 },
  { id := "iocov-libdl-llp-show", juliaFile := "base/libdl.jl"
    juliaFns := ["show(::IO, ::LazyLibraryPath)"]
    statement := "show prints LazyLibraryPath(...) around the shown pieces."
    source := "base/libdl.jl:358-369"
    status := .proven, prop := ``Libdl.LazyLibraryPathCorrect_6, thm := some ``Libdl.lazyLibraryPathCorrect_6 },
  { id := "iocov-libdl-initdeps", juliaFile := "base/libdl.jl"
    juliaFns := ["(::InitialDependencies)()"]
    statement := "InitialDependencies returns a copy of its dependencies."
    source := "base/libdl.jl:396"
    status := .proven, prop := ``Libdl.LazyLibraryCorrect_1, thm := some ``Libdl.lazyLibraryCorrect_1 },
  { id := "iocov-libdl-lazylibrary", juliaFile := "base/libdl.jl"
    juliaFns := ["LazyLibrary(path; flags, dependencies, on_load_callback)"]
    statement := "LazyLibrary stores its arguments with UInt32 flags and no handle."
    source := "base/libdl.jl:399-476 (LazyLibrary docstring)"
    status := .proven, prop := ``Libdl.LazyLibraryCorrect_2, thm := some ``Libdl.lazyLibraryCorrect_2 },
  { id := "iocov-libdl-onload", juliaFile := "base/libdl.jl"
    juliaFns := ["_invoke_on_load_callback"]
    statement := "_invoke_on_load_callback calls the callback."
    source := "base/libdl.jl:480"
    status := .proven, prop := ``Libdl.LazyLibraryCorrect_3, thm := some ``Libdl.lazyLibraryCorrect_3 },
  { id := "iocov-libdl-llp-path-string", juliaFile := "base/libdl.jl"
    juliaFns := ["_lazy_library_path_string"]
    statement := "_lazy_library_path_string is string(path)."
    source := "base/libdl.jl:481"
    status := .proven, prop := ``Libdl.LazyLibraryCorrect_4, thm := some ``Libdl.lazyLibraryCorrect_4 },
  { id := "iocov-libdl-ll-show", juliaFile := "base/libdl.jl"
    juliaFns := ["show(::IO, ::LazyLibrary)"]
    statement := "show prints LazyLibrary(path)."
    source := "base/libdl.jl:484-488"
    status := .proven, prop := ``Libdl.LazyLibraryCorrect_5, thm := some ``Libdl.lazyLibraryCorrect_5 },
  { id := "iocov-libdl-add-dependency", juliaFile := "base/libdl.jl"
    juliaFns := ["add_dependency!"]
    statement := "add_dependency! appends the dependency."
    source := "base/libdl.jl:490-513 (add_dependency! docstring)"
    status := .proven, prop := ``Libdl.LazyLibraryCorrect_6, thm := some ``Libdl.lazyLibraryCorrect_6 },
  { id := "iocov-libdl-ll-cached", juliaFile := "base/libdl.jl"
    juliaFns := ["dlopen(::LazyLibrary, flags)"]
    statement := "A loaded LazyLibrary returns its cached handle without loading or running the callback."
    source := "base/libdl.jl:399-558 (LazyLibrary docstring)"
    status := .proven, prop := ``Libdl.LazyLibraryCorrect_7, thm := some ``Libdl.lazyLibraryCorrect_7 },
  { id := "iocov-libdl-ll-dlopen-any", juliaFile := "base/libdl.jl"
    juliaFns := ["dlopen(::Any)"]
    statement := "A failing dependency stops the load; dlopen(x::Any) throws TypeError."
    source := "base/libdl.jl:519-559"
    status := .proven, prop := ``Libdl.LazyLibraryCorrect_9, thm := some ``Libdl.lazyLibraryCorrect_9 },
  { id := "iocov-libdl-ll-dlsym", juliaFile := "base/libdl.jl"
    juliaFns := ["dlsym(::LazyLibrary, args...)"]
    statement := "dlsym(ll) looks the symbol up in the loaded handle."
    source := "base/libdl.jl:560"
    status := .proven, prop := ``Libdl.LazyLibraryCorrect_10, thm := some ``Libdl.lazyLibraryCorrect_10 },
  { id := "iocov-libdl-ll-dlpath", juliaFile := "base/libdl.jl"
    juliaFns := ["dlpath(::LazyLibrary)"]
    statement := "dlpath(ll) is the path of the loaded handle."
    source := "base/libdl.jl:561"
    status := .proven, prop := ``Libdl.LazyLibraryCorrect_11, thm := some ``Libdl.lazyLibraryCorrect_11 },
  { id := "iocov-lazylibrary-throw-error", juliaFile := "base/libdl.jl"
    juliaFns := ["dlopen(::LazyLibrary; throw_error=false)"]
    statement := "dlopen(ll::LazyLibrary; throw_error=false) returns nothing when the library cannot be loaded."
    source := "base/libdl.jl:84-127 (dlopen docstring)"
    status := .refuted, prop := ``LibdlFaithful.LazyDlopenNothing, thm := some ``LibdlFaithful.lazyDlopenNothing_refuted
    issue := "none found (queries: LazyLibrary throw_error, LazyLibrary dlopen nothing)"
    notes := "nothing is stored with @atomic into the Ptr{Cvoid} handle field, which throws MethodError. Same on 1.13.2." },
  { id := "iocov-env-getenv", juliaFile := "base/env.jl"
    juliaFns := ["_getenv", "get(::EnvDict, k, def)", "access_env"]
    statement := "get(ENV, k, def) returns the variable or the default."
    source := "base/env.jl:55-180 (ENV docstring)"
    status := .proven, prop := ``Env.EnvDictCorrect_4, thm := some ``Env.envDictCorrect_4 },
  { id := "iocov-env-hasenv", juliaFile := "base/env.jl"
    juliaFns := ["_hasenv", "in(k, keys(ENV))"]
    statement := "haskey(ENV, k) holds exactly when the variable is set."
    source := "base/env.jl:56-186"
    status := .proven, prop := ``Env.EnvDictCorrect_6, thm := some ``Env.envDictCorrect_6 },
  { id := "iocov-env-environ", juliaFile := "base/env.jl"
    juliaFns := ["_environ()"]
    statement := "_environ returns the process environment array."
    source := "base/env.jl:70"
    status := .proven, prop := ``Env.EnvDictCorrect_13, thm := some ``Env.envDictCorrect_13 },
  { id := "iocov-env-setindex", juliaFile := "base/env.jl"
    juliaFns := ["setindex!(::EnvDict, v, k)", "_setenv", "getindex(::EnvDict, k)"]
    statement := "After ENV[k] = v with a valid name, ENV[k] returns v."
    source := "base/env.jl:92-190 (ENV docstring)"
    status := .proven, prop := ``Env.EnvDictCorrect_1, thm := some ``Env.envDictCorrect_1 },
  { id := "iocov-env-setenv-invalid", juliaFile := "base/env.jl"
    juliaFns := ["_setenv"]
    statement := "Setting an invalid variable name throws SystemError."
    source := "base/env.jl:78-81"
    status := .proven, prop := ``Env.EnvDictCorrect_9, thm := some ``Env.envDictCorrect_9 },
  { id := "iocov-env-delete", juliaFile := "base/env.jl"
    juliaFns := ["delete!(::EnvDict, k)", "_unsetenv"]
    statement := "delete!(ENV, k) removes the variable."
    source := "base/env.jl:83-189"
    status := .proven, prop := ``Env.EnvDictCorrect_2, thm := some ``Env.envDictCorrect_2 },
  { id := "iocov-env-keyerror", juliaFile := "base/env.jl"
    juliaFns := ["getindex(::EnvDict, k)"]
    statement := "ENV[k] throws KeyError for an unset variable."
    source := "base/env.jl:179"
    status := .proven, prop := ``Env.EnvDictCorrect_3, thm := some ``Env.envDictCorrect_3 },
  { id := "iocov-env-get-f", juliaFile := "base/env.jl"
    juliaFns := ["get(f, ::EnvDict, k)"]
    statement := "get(f, ENV, k) calls f for an unset variable."
    source := "base/env.jl:181"
    status := .proven, prop := ``Env.EnvDictCorrect_5, thm := some ``Env.envDictCorrect_5 },
  { id := "iocov-env-get-bang", juliaFile := "base/env.jl"
    juliaFns := ["get!(default, ::EnvDict, k)"]
    statement := "get!(f, ENV, k) returns a set variable without calling f."
    source := "base/env.jl:182-185"
    status := .proven, prop := ``Env.EnvDictCorrect_12, thm := some ``Env.envDictCorrect_12 },
  { id := "iocov-env-pop", juliaFile := "base/env.jl"
    juliaFns := ["pop!(::EnvDict, k)"]
    statement := "pop!(ENV, k) returns the value and unsets the variable."
    source := "base/env.jl:187"
    status := .proven, prop := ``Env.EnvDictCorrect_10, thm := some ``Env.envDictCorrect_10 },
  { id := "iocov-env-pop-default", juliaFile := "base/env.jl"
    juliaFns := ["pop!(::EnvDict, k, def)"]
    statement := "pop!(ENV, k, def) returns def for an unset variable and changes nothing."
    source := "base/env.jl:188"
    status := .proven, prop := ``Env.EnvDictCorrect_11, thm := some ``Env.envDictCorrect_11 },
  { id := "iocov-env-push", juliaFile := "base/env.jl"
    juliaFns := ["push!(::EnvDict, kv)"]
    statement := "push!(ENV, k => v) is ENV[k] = v."
    source := "base/env.jl:191"
    status := .proven, prop := ``Env.EnvDictCorrect_7, thm := some ``Env.envDictCorrect_7 },
  { id := "iocov-env-bool-truthy", juliaFile := "base/env.jl"
    juliaFns := ["parse_bool_env"]
    statement := "The documented true spellings parse as true."
    source := "base/env.jl:135-177 (get_bool_env docstring)"
    status := .proven, prop := ``Env.BoolEnvDoc_1, thm := some ``Env.boolEnvDoc_1 },
  { id := "iocov-env-bool-default", juliaFile := "base/env.jl"
    juliaFns := ["get_bool_env(name, default)"]
    statement := "get_bool_env returns the default for an unset variable."
    source := "base/env.jl:135-157 (get_bool_env docstring)"
    status := .proven, prop := ``Env.BoolEnvDoc_4, thm := some ``Env.boolEnvDoc_4 },
  { id := "iocov-env-bool-f", juliaFile := "base/env.jl"
    juliaFns := ["get_bool_env(f_default, name)"]
    statement := "For a set nonempty variable get_bool_env parses its value."
    source := "base/env.jl:158-166"
    status := .proven, prop := ``Env.BoolEnvDoc_6, thm := some ``Env.boolEnvDoc_6 },
  { id := "iocov-env-iterate", juliaFile := "base/env.jl"
    juliaFns := ["iterate(::EnvDict, i)"]
    statement := "Iteration yields key => value pairs split at the first =."
    source := "base/env.jl:231-246 (invariant)"
    status := .proven, prop := ``Env.EnvIterationCorrect_1, thm := some ``Env.envIterationCorrect_1 },
  { id := "iocov-env-length", juliaFile := "base/env.jl"
    juliaFns := ["length(::EnvDict)"]
    statement := "length(ENV) counts the entries containing =."
    source := "base/env.jl:250-256"
    status := .proven, prop := ``Env.EnvIterationCorrect_2, thm := some ``Env.envIterationCorrect_2 },
  { id := "iocov-env-show", juliaFile := "base/env.jl"
    juliaFns := ["show(::IO, ::EnvDict)"]
    statement := "show prints one k=v line per pair."
    source := "base/env.jl:258-262"
    status := .proven, prop := ``Env.EnvIterationCorrect_4, thm := some ``Env.envIterationCorrect_4 },
  { id := "iocov-withenv-duplicate-key", juliaFile := "base/env.jl"
    juliaFns := ["withenv(f, keyvals::Pair...)"]
    statement := "When withenv returns, the original environment has been restored, for any list of pairs."
    source := "base/env.jl:265-276 (withenv docstring)"
    status := .refuted, prop := ``EnvFaithful.WithenvRestores, thm := some ``EnvFaithful.withenvRestores_refuted
    issue := "none found (queries: withenv duplicate, withenv restore); related #28283"
    notes := "old[key] is recorded after earlier pairs were applied, so a key given twice is restored to its first new value. Same on 1.13.2." },
  { id := "iocov-env-withenv-single", juliaFile := "base/env.jl"
    juliaFns := ["withenv(f, keyvals::Pair...)"]
    statement := "withenv with one pair restores that variable afterwards."
    source := "base/env.jl:265-289 (withenv docstring)"
    status := .proven, prop := ``Env.WithenvSingle_2, thm := some ``Env.withenvSingle_2 },
  { id := "iocov-env-withenv0", juliaFile := "base/env.jl"
    juliaFns := ["withenv(f)"]
    statement := "withenv(f) leaves the environment unchanged."
    source := "base/env.jl:290"
    status := .proven, prop := ``Env.WithenvSingle_1, thm := some ``Env.withenvSingle_1 },
  { id := "iocov-secret-create", juliaFile := "base/secretbuffer.jl"
    juliaFns := ["SecretBuffer(; sizehint)"]
    statement := "SecretBuffer(; sizehint) is empty with sizehint zeroed bytes."
    source := "base/secretbuffer.jl:5-40 (SecretBuffer docstring)"
    status := .proven, prop := ``Secret.Shredding_5, thm := some ``Secret.shredding_5 },
  { id := "iocov-secret-ofstring", juliaFile := "base/secretbuffer.jl"
    juliaFns := ["SecretBuffer(::String)", "write(::SecretBuffer, ::UInt8)"]
    statement := "SecretBuffer(str) holds the bytes of str at position 0."
    source := "base/secretbuffer.jl:43-63 (SecretBuffer docstring)"
    status := .proven, prop := ``Secret.RoundTrip_1, thm := some ``Secret.roundTrip_1 },
  { id := "iocov-secret-read", juliaFile := "base/secretbuffer.jl"
    juliaFns := ["read(::SecretBuffer, ::Type{UInt8})"]
    statement := "Reading a SecretBuffer built from str returns the bytes of str."
    source := "base/secretbuffer.jl:183-188 (invariant)"
    status := .proven, prop := ``Secret.RoundTrip_2, thm := some ``Secret.roundTrip_2 },
  { id := "iocov-secret-convert", juliaFile := "base/secretbuffer.jl"
    juliaFns := ["SecretBuffer(::AbstractString)", "convert(::Type{SecretBuffer}, ::AbstractString)"]
    statement := "SecretBuffer(::AbstractString) and convert equal SecretBuffer(String(s))."
    source := "base/secretbuffer.jl:54-64"
    status := .proven, prop := ``Secret.RoundTrip_3, thm := some ``Secret.roundTrip_3 },
  { id := "iocov-secret-bang", juliaFile := "base/secretbuffer.jl"
    juliaFns := ["SecretBuffer!(d)"]
    statement := "SecretBuffer!(d) copies d and zeroes it."
    source := "base/secretbuffer.jl:66-80 (SecretBuffer! docstring)"
    status := .proven, prop := ``Secret.RoundTrip_4, thm := some ``Secret.roundTrip_4 },
  { id := "iocov-secret-unsafe-ptr", juliaFile := "base/secretbuffer.jl"
    juliaFns := ["unsafe_SecretBuffer!(::Ptr{UInt8}, len)"]
    statement := "unsafe_SecretBuffer!(p, len) copies and zeroes the len bytes."
    source := "base/secretbuffer.jl:82-100"
    status := .proven, prop := ``Secret.RoundTrip_5, thm := some ``Secret.roundTrip_5 },
  { id := "iocov-secret-unsafe-cstring", juliaFile := "base/secretbuffer.jl"
    juliaFns := ["unsafe_SecretBuffer!(::Cstring)"]
    statement := "unsafe_SecretBuffer!(s::Cstring) copies the bytes before the NUL."
    source := "base/secretbuffer.jl:82-88"
    status := .proven, prop := ``Secret.RoundTrip_6, thm := some ``Secret.roundTrip_6 },
  { id := "iocov-secret-show", juliaFile := "base/secretbuffer.jl"
    juliaFns := ["show(::IO, ::SecretBuffer)"]
    statement := "show never prints the contents."
    source := "base/secretbuffer.jl:103"
    status := .proven, prop := ``Secret.Comparisons_5, thm := some ``Secret.comparisons_5 },
  { id := "iocov-secret-eq", juliaFile := "base/secretbuffer.jl"
    juliaFns := ["==(::SecretBuffer, ::SecretBuffer)", "_bufcmp"]
    statement := "== is reflexive."
    source := "base/secretbuffer.jl:106-115 (invariant)"
    status := .proven, prop := ``Secret.Comparisons_1, thm := some ``Secret.comparisons_1 },
  { id := "iocov-secret-hash", juliaFile := "base/secretbuffer.jl"
    juliaFns := ["hash(::SecretBuffer, h)"]
    statement := "Equal SecretBuffers hash equally."
    source := "base/secretbuffer.jl:118 (hash contract)"
    status := .proven, prop := ``Secret.Comparisons_4, thm := some ``Secret.comparisons_4 },
  { id := "iocov-secret-copy", juliaFile := "base/secretbuffer.jl"
    juliaFns := ["copy(::SecretBuffer)"]
    statement := "A copy equals the original."
    source := "base/secretbuffer.jl:120"
    status := .proven, prop := ``Secret.Comparisons_2, thm := some ``Secret.comparisons_2 },
  { id := "iocov-secret-copy-bang", juliaFile := "base/secretbuffer.jl"
    juliaFns := ["copy!(dest, src)"]
    statement := "copy!(dest, src) makes dest equal to src."
    source := "base/secretbuffer.jl:121-131"
    status := .proven, prop := ``Secret.Comparisons_3, thm := some ``Secret.comparisons_3 },
  { id := "iocov-secret-write-io", juliaFile := "base/secretbuffer.jl"
    juliaFns := ["write(::IO, ::SecretBuffer)"]
    statement := "write(io, s) writes the contents and returns their size."
    source := "base/secretbuffer.jl:147-153"
    status := .proven, prop := ``Secret.Comparisons_6, thm := some ``Secret.comparisons_6 },
  { id := "iocov-secret-cconvert", juliaFile := "base/secretbuffer.jl"
    juliaFns := ["cconvert(::Type{Cstring}, ::SecretBuffer)"]
    statement := "cconvert NUL-terminates the contents without moving the pointer."
    source := "base/secretbuffer.jl:155-167"
    status := .proven, prop := ``Secret.Comparisons_7, thm := some ``Secret.comparisons_7 },
  { id := "iocov-secret-seek", juliaFile := "base/secretbuffer.jl"
    juliaFns := ["seek(::SecretBuffer, n)"]
    statement := "seek(s, n) sets the position to n within 0:size."
    source := "base/secretbuffer.jl:171"
    status := .proven, prop := ``Secret.Positioning_1, thm := some ``Secret.positioning_1 },
  { id := "iocov-secret-seekend", juliaFile := "base/secretbuffer.jl"
    juliaFns := ["seekend(::SecretBuffer)"]
    statement := "seekend reaches the end: position size and eof."
    source := "base/secretbuffer.jl:172"
    status := .proven, prop := ``Secret.Positioning_4, thm := some ``Secret.positioning_4 },
  { id := "iocov-secret-skip", juliaFile := "base/secretbuffer.jl"
    juliaFns := ["skip(::SecretBuffer, n)"]
    statement := "skip(s, n) seeks to position(s) + n."
    source := "base/secretbuffer.jl:173"
    status := .proven, prop := ``Secret.Positioning_5, thm := some ``Secret.positioning_5 },
  { id := "iocov-secret-eof", juliaFile := "base/secretbuffer.jl"
    juliaFns := ["eof(::SecretBuffer)", "bytesavailable(::SecretBuffer)", "position(::SecretBuffer)"]
    statement := "eof holds exactly when no bytes are available."
    source := "base/secretbuffer.jl:175-177"
    status := .proven, prop := ``Secret.Positioning_6, thm := some ``Secret.positioning_6 },
  { id := "iocov-secret-isempty", juliaFile := "base/secretbuffer.jl"
    juliaFns := ["isempty(::SecretBuffer)"]
    statement := "isempty holds exactly for an empty buffer."
    source := "base/secretbuffer.jl:178"
    status := .proven, prop := ``Secret.Positioning_7, thm := some ``Secret.positioning_7 },
  { id := "iocov-secret-peek", juliaFile := "base/secretbuffer.jl"
    juliaFns := ["peek(::SecretBuffer, ::Type{UInt8})"]
    statement := "peek returns the byte read would return, without moving."
    source := "base/secretbuffer.jl:179-188"
    status := .proven, prop := ``Secret.Positioning_9, thm := some ``Secret.positioning_9 },
  { id := "iocov-secretbuffer-peek", juliaFile := "base/secretbuffer.jl"
    juliaFns := ["peek(::IO, ::Type{T})"]
    statement := "peek(s::SecretBuffer, Char) returns the next character, as for any IOBuffer-like object."
    source := "base/secretbuffer.jl:6"
    status := .refuted, prop := ``Secret.PeekChar, thm := some ``Secret.peekChar_refuted
    issue := "none found (queries: SecretBuffer peek, SecretBuffer mark)"
    notes := "The generic peek calls mark(s), which reads the missing field mark and throws FieldError. Same on 1.13.2." },
  { id := "iocov-secret-final-shred", juliaFile := "base/secretbuffer.jl"
    juliaFns := ["final_shred!"]
    statement := "final_shred! warns only for unshredded buffers and shreds them."
    source := "base/secretbuffer.jl:190-193"
    status := .proven, prop := ``Secret.Shredding_3, thm := some ``Secret.shredding_3 },
  { id := "iocov-secret-shred", juliaFile := "base/secretbuffer.jl"
    juliaFns := ["shred!(::SecretBuffer)", "isshredded"]
    statement := "After shred! the buffer is empty and isshredded holds."
    source := "base/secretbuffer.jl:195-217 (shred! docstring)"
    status := .proven, prop := ``Secret.Shredding_1, thm := some ``Secret.shredding_1 },
  { id := "iocov-secret-shred-f", juliaFile := "base/secretbuffer.jl"
    juliaFns := ["shred!(f, x)"]
    statement := "shred!(f, x) returns f(x) and shreds x even if f throws."
    source := "base/secretbuffer.jl:219-232 (shred! docstring)"
    status := .proven, prop := ``Secret.Shredding_4, thm := some ``Secret.shredding_4 },
  { id := "iocov-util-with-output-color", juliaFile := "base/util.jl"
    juliaFns := ["with_output_color"]
    statement := "Without color, with_output_color prints the text unchanged."
    source := "base/util.jl:66-84"
    status := .proven, prop := ``Util.ColorCorrect_1, thm := some ``Util.colorCorrect_1 },
  { id := "iocov-util-output-color-string", juliaFile := "base/util.jl"
    juliaFns := ["output_color_string"]
    statement := "A nonempty line is wrapped in the enable and disable sequences."
    source := "base/util.jl:86-117"
    status := .proven, prop := ``Util.ColorCorrect_3, thm := some ``Util.colorCorrect_3 },
  { id := "iocov-util-printstyled", juliaFile := "base/util.jl"
    juliaFns := ["printstyled(io, msg...)"]
    statement := "printstyled(io, ...) is with_output_color of print."
    source := "base/util.jl:119-144 (printstyled docstring)"
    status := .proven, prop := ``Util.ColorCorrect_2, thm := some ``Util.colorCorrect_2 },
  { id := "iocov-util-printstyled-stdout", juliaFile := "base/util.jl"
    juliaFns := ["printstyled(msg...)"]
    statement := "printstyled(msg...) styles text as printing to stdout."
    source := "base/util.jl:145-146"
    status := .proven, prop := ``Util.PrintstyledStdout, thm := some ``Util.printstyledStdout_correct },
  { id := "iocov-util-julia-cmd", juliaFile := "base/util.jl"
    juliaFns := ["julia_cmd"]
    statement := "julia_cmd starts with the executable, -C cpu_target and -J image."
    source := "base/util.jl:148-258 (julia_cmd docstring)"
    status := .proven, prop := ``Util.JuliaCmdCorrect_1, thm := some ``Util.juliaCmdCorrect_1 },
  { id := "iocov-util-julia-exename", juliaFile := "base/util.jl"
    juliaFns := ["julia_exename()"]
    statement := "julia_exename is julia-debug for debug builds and julia otherwise."
    source := "base/util.jl:260-266"
    status := .proven, prop := ``Util.JuliaCmdCorrect_6, thm := some ``Util.juliaCmdCorrect_6 },
  { id := "iocov-util-securezero", juliaFile := "base/util.jl"
    juliaFns := ["securezero!(::AbstractArray)"]
    statement := "securezero! zeroes every element."
    source := "base/util.jl:268-277 (securezero! docstring)"
    status := .proven, prop := ``Util.SecurezeroCorrect_1, thm := some ``Util.securezeroCorrect_1 },
  { id := "iocov-util-unsafe-securezero", juliaFile := "base/util.jl"
    juliaFns := ["unsafe_securezero!(::Ptr{T}, len)"]
    statement := "unsafe_securezero! zeroes exactly len*sizeof(T) bytes at p."
    source := "base/util.jl:278-279"
    status := .proven, prop := ``Util.SecurezeroCorrect_2, thm := some ``Util.securezeroCorrect_2 },
  { id := "iocov-util-unsafe-securezero-void", juliaFile := "base/util.jl"
    juliaFns := ["unsafe_securezero!(::Ptr{Cvoid}, len)"]
    statement := "For Ptr{Cvoid} len counts bytes."
    source := "base/util.jl:280"
    status := .proven, prop := ``Util.SecurezeroCorrect_3, thm := some ``Util.securezeroCorrect_3 },
  { id := "iocov-util-getch", juliaFile := "base/util.jl"
    juliaFns := ["_getch()"]
    statement := "_getch returns the next key and throws EOFError at the end."
    source := "base/util.jl:310-316"
    status := .proven, prop := ``Util.GetchCorrect, thm := some ``Util.getchCorrect },
  { id := "iocov-util-make-termios", juliaFile := "base/util.jl"
    juliaFns := ["make_termios()"]
    statement := "make_termios allocates termios_size zero bytes."
    source := "base/util.jl:319"
    status := .proven, prop := ``Util.GetpassAscii_4, thm := some ``Util.getpassAscii_4 },
  { id := "iocov-util-tcgetattr", juliaFile := "base/util.jl"
    juliaFns := ["tcgetattr"]
    statement := "tcgetattr succeeds exactly when the C call returns 0."
    source := "base/util.jl:325-330"
    status := .proven, prop := ``Util.TcgetattrCorrect, thm := some ``Util.tcgetattrCorrect },
  { id := "iocov-util-tcsetattr", juliaFile := "base/util.jl"
    juliaFns := ["tcsetattr"]
    statement := "tcsetattr succeeds exactly when the C call returns 0."
    source := "base/util.jl:331-336"
    status := .proven, prop := ``Util.TcsetattrCorrect, thm := some ``Util.tcsetattrCorrect },
  { id := "iocov-util-cfmakeraw", juliaFile := "base/util.jl"
    juliaFns := ["cfmakeraw"]
    statement := "cfmakeraw applies the C function to the termios bytes."
    source := "base/util.jl:337"
    status := .proven, prop := ``Util.GetpassAscii_6, thm := some ``Util.getpassAscii_6 },
  { id := "iocov-util-with-raw-tty", juliaFile := "base/util.jl"
    juliaFns := ["with_raw_tty"]
    statement := "with_raw_tty runs f and restores the terminal mode."
    source := "base/util.jl:339-363"
    status := .proven, prop := ``Util.GetpassAscii_7, thm := some ``Util.getpassAscii_7 },
  { id := "iocov-util-getpass", juliaFile := "base/util.jl"
    juliaFns := ["getpass(::TTY, ::IO, ::AbstractString)"]
    statement := "getpass returns printable ASCII input up to RETURN."
    source := "base/util.jl:294-388 (getpass docstring)"
    status := .proven, prop := ``Util.GetpassAscii_1, thm := some ``Util.getpassAscii_1 },
  { id := "iocov-getpass-backspace", juliaFile := "base/util.jl"
    juliaFns := ["getpass(::TTY, ::IO, ::AbstractString)"]
    statement := "Backspace in getpass deletes the last typed character."
    source := "base/util.jl:381"
    status := .refuted, prop := ``Util.GetpassBackspace, thm := some ``Util.getpassBackspace_refuted
    issue := "none found (queries: getpass backspace, getpass)"
    notes := "Raw terminals send DEL (0x7f) for Backspace, which is ignored; only 0x08 deletes. Same on 1.13.2." },
  { id := "iocov-getpass-utf8", juliaFile := "base/util.jl"
    juliaFns := ["getpass(::TTY, ::IO, ::AbstractString)"]
    statement := "getpass returns the typed secret, including non-ASCII characters."
    source := "base/util.jl:294-307 (getpass docstring)"
    status := .refuted, prop := ``Util.GetpassBytes, thm := some ``Util.getpassBytes_refuted
    issue := "none found (queries: getpass unicode); related #44399"
    notes := "Bytes >= 128 are dropped and 0xe0 ends input. Same on 1.13.2." },
  { id := "iocov-util-getpass-stdin", juliaFile := "base/util.jl"
    juliaFns := ["getpass(::AbstractString)"]
    statement := "getpass(prompt) reads stdin."
    source := "base/util.jl:392"
    status := .proven, prop := ``Util.GetpassAscii_2, thm := some ``Util.getpassAscii_2 },
  { id := "iocov-util-prompt", juliaFile := "base/util.jl"
    juliaFns := ["prompt(input, output, message; default)"]
    statement := "An empty line selects the default."
    source := "base/util.jl:394-420 (prompt docstring)"
    status := .proven, prop := ``Util.PromptDoc_1, thm := some ``Util.promptDoc_1 },
  { id := "iocov-util-prompt-stdin", juliaFile := "base/util.jl"
    juliaFns := ["prompt(message; default)"]
    statement := "prompt(message) uses stdin and stdout."
    source := "base/util.jl:424"
    status := .proven, prop := ``Util.PromptDoc_4, thm := some ``Util.promptDoc_4 },
  { id := "iocov-util-unsafe-crc32c", juliaFile := "base/util.jl"
    juliaFns := ["unsafe_crc32c"]
    statement := "unsafe_crc32c checksums the first n bytes."
    source := "base/util.jl:515"
    status := .proven, prop := ``Util.UnsafeCrc32cPrefix, thm := some ``Util.unsafeCrc32cPrefix },
  { id := "iocov-util-crc32c-tuple", juliaFile := "base/util.jl"
    juliaFns := ["_crc32c(::NTuple)"]
    statement := "_crc32c of a tuple checksums all its bytes and composes over concatenation."
    source := "base/util.jl:517-518"
    status := .proven, prop := ``Util.Crc32cTupleCorrect, thm := some ``Util.crc32cTupleCorrect },
  { id := "iocov-util-crc32c-dense", juliaFile := "base/util.jl"
    juliaFns := ["_crc32c(::DenseUInt8OrInt8)"]
    statement := "_crc32c of an array checksums all its bytes and composes over concatenation."
    source := "base/util.jl:520-522"
    status := .proven, prop := ``Util.Crc32cDenseCorrect, thm := some ``Util.crc32cDenseCorrect },
  { id := "iocov-util-crc32c-string", juliaFile := "base/util.jl"
    juliaFns := ["_crc32c(::Union{String,SubString{String}})"]
    statement := "_crc32c of a string checksums its code units and composes over concatenation."
    source := "base/util.jl:524-526"
    status := .proven, prop := ``Util.Crc32cStringCorrect, thm := some ``Util.crc32cStringCorrect },
  { id := "iocov-util-crc32c-u128", juliaFile := "base/util.jl"
    juliaFns := ["_crc32c(::UInt128)"]
    statement := "_crc32c(x::UInt128) checksums the 16 bytes of x."
    source := "base/util.jl:542-543"
    status := .proven, prop := ``Util.Crc32cU128Bytes, thm := some ``Util.crc32cU128Bytes },
  { id := "iocov-util-crc32c-u64", juliaFile := "base/util.jl"
    juliaFns := ["_crc32c(::UInt64)"]
    statement := "_crc32c(x::UInt64) checksums the 8 bytes of x."
    source := "base/util.jl:544-545"
    status := .proven, prop := ``Util.Crc32cU64Bytes, thm := some ``Util.crc32cU64Bytes },
  { id := "iocov-util-crc32c-u32", juliaFile := "base/util.jl"
    juliaFns := ["_crc32c(::UInt32)"]
    statement := "_crc32c(x::UInt32) checksums the 4 bytes of x."
    source := "base/util.jl:546-547"
    status := .proven, prop := ``Util.Crc32cU32Bytes, thm := some ``Util.crc32cU32Bytes },
  { id := "iocov-util-crc32c-u16", juliaFile := "base/util.jl"
    juliaFns := ["_crc32c(::UInt16)"]
    statement := "_crc32c(x::UInt16) checksums the 2 bytes of x."
    source := "base/util.jl:548-549"
    status := .proven, prop := ``Util.Crc32cU16Bytes, thm := some ``Util.crc32cU16Bytes },
  { id := "iocov-util-crc32c-u8", juliaFile := "base/util.jl"
    juliaFns := ["_crc32c(::UInt8)"]
    statement := "_crc32c(x::UInt8) checksums the byte x."
    source := "base/util.jl:550-551"
    status := .proven, prop := ``Util.Crc32cU8Bytes, thm := some ``Util.crc32cU8Bytes },
  { id := "iocov-util-kwdef", juliaFile := "base/util.jl"
    juliaFns := ["kwdef(expr)"]
    statement := "The generated keyword constructor has the collected names and defaults."
    source := "base/util.jl:554-642 (@kwdef docstring)"
    status := .proven, prop := ``Util.KwdefCorrect_7, thm := some ``Util.kwdefCorrect_7 },
  { id := "iocov-util-kwdef-extract", juliaFile := "base/util.jl"
    juliaFns := ["extract_names_and_defvals_from_kwdef_fieldblock!"]
    statement := "Every field definition contributes its name and default."
    source := "base/util.jl:646-665"
    status := .proven, prop := ``Util.KwdefCorrect_6, thm := some ``Util.kwdefCorrect_6 },
  { id := "iocov-util-kwdef-field", juliaFile := "base/util.jl"
    juliaFns := ["def_name_defval_from_kwdef_fielddef"]
    statement := "a = v gives the field a with default v."
    source := "base/util.jl:667-684"
    status := .proven, prop := ``Util.KwdefCorrect_3, thm := some ``Util.kwdefCorrect_3 },
  { id := "iocov-util-runtests", juliaFile := "base/util.jl"
    juliaFns := ["runtests"]
    statement := "runtests passes --exit-on-error when requested."
    source := "base/util.jl:686-739 (runtests docstring)"
    status := .proven, prop := ``Util.RuntestsCorrect_2, thm := some ``Util.runtestsCorrect_2 },
  { id := "iocov-runtests-propagate-doc", juliaFile := "base/util.jl"
    juliaFns := ["runtests"]
    statement := "runtests propagates the current project by default, as its documented signature states."
    source := "base/util.jl:688-698 (runtests docstring)"
    status := .refuted, prop := ``UtilFaithful.RuntestsDefaultPropagates, thm := some ``UtilFaithful.runtestsDefaultPropagates_refuted
    issue := "none found (queries: runtests propagate_project); related #56716"
    notes := "The docstring says propagate_project=true; the default is false. Same on 1.13.2." },
  { id := "iocov-open-flags-append-doc", juliaFile := "base/io.jl"
    juliaFns := ["open_flags"]
    statement := "open_flags follows the documented open keyword table, including append=true."
    source := "base/iostream.jl:292-300 (open docstring table)"
    status := .refuted, prop := ``Io.OpenFlagsDoc, thm := some ``Io.openFlagsDoc_refuted
    issue := "none found (queries: open_flags, open append truncate)"
    notes := "For append=true the table gives truncate=true; open_flags gives false. Same on 1.13.2." },
  { id := "iocov-io-open-flags", juliaFile := "base/io.jl"
    juliaFns := ["open_flags"]
    statement := "Without append, open_flags follows the documented defaults."
    source := "base/iostream.jl:292-300 (open docstring table)"
    status := .proven, prop := ``Io.OpenFlagsTable, thm := some ``Io.openFlagsTable },
  { id := "iocov-skipchars-nonseekable", juliaFile := "base/io.jl"
    juliaFns := ["skipchars(predicate, io::IO)"]
    statement := "skipchars works on any IO stream."
    source := "base/io.jl:1625-1626 (skipchars docstring)"
    status := .refuted, prop := ``Io.SkipcharsStreams, thm := some ``Io.skipcharsStreams_refuted
    issue := "none found (queries: skipchars, skipchars seek); related #21354"
    notes := "The pushback uses skip(io, -n), which non-seekable streams reject. Same on 1.13.2." },
  { id := "iocov-io-skipchars", juliaFile := "base/io.jl"
    juliaFns := ["skipchars(predicate, io::IO)"]
    statement := "On a seekable stream skipchars stops before the first character failing the predicate."
    source := "base/io.jl:1622-1653 (skipchars docstring)"
    status := .proven, prop := ``Io.SkipcharsSeekable, thm := some ``Io.skipcharsSeekable }
]

def entries : List Entry := existingEntries ++ Cmd.entries ++ IOBufferRemaining.entries ++
  LibcRemaining.entries ++ IOText.entries ++ IoLines.entries ++ EnvFaithful.entries ++
  SecretFaithful.entries ++ UtilFaithful.entries ++ LibdlFaithful.entries ++ PathFaithful.entries

end JuliaLean.IOCov
