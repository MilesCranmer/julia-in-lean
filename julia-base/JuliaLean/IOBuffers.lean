import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.IOBuffers.Model
import JuliaLean.IOBuffers.Ops
import JuliaLean.IOBuffers.Props
import JuliaLean.IOBuffers.Refuted
import JuliaLean.IOBuffers.Inv
import JuliaLean.IOBuffers.Proven

namespace JuliaLean.IOBuffers

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  -- proven
  { id := "iobuffers-invariant", juliaFile := "base/iobuffer.jl"
    juliaFns := ["position", "bytesavailable", "eof", "filesize", "ensureroom", "compact!", "IOBuffer", "PipeBuffer"]
    statement := "After any sequence of operations, position >= 0, bytesavailable >= 0, eof == (bytesavailable == 0), position + bytesavailable == filesize for seekable buffers, and at most maxsize bytes are stored."
    source := "invariant base/iobuffer.jl:55-93 (field comments)", status := .proven
    prop := ``InvariantHolds, thm := some ``invariantHolds },
  { id := "iobuffers-no-out-of-bounds", juliaFile := "base/iobuffer.jl"
    juliaFns := ["unsafe_write", "unsafe_read", "read(::GenericIOBuffer, ::Type{UInt8})", "peek", "compact!", "_resize!"]
    statement := "Every operation on a reachable buffer reads or writes only within its allocated memory."
    source := "invariant base/iobuffer.jl:55-70", status := .proven
    prop := ``NoOutOfBounds, thm := some ``noOutOfBounds },
  { id := "iobuffers-write-at-position", juliaFile := "base/iobuffer.jl"
    juliaFns := ["unsafe_write(::GenericIOBuffer, ::Ptr{UInt8}, ::UInt)", "ensureroom"]
    statement := "write on a seekable non-append IOBuffer overwrites from the position, writes min(n, maxsize - position) bytes and advances the position by that much."
    source := "base/iobuffer.jl:173-180 (IOBuffer docstring: maxsize), 67-69", status := .proven
    prop := ``WriteAtPosition, thm := some ``writeAtPosition },
  { id := "iobuffers-append-at-end", juliaFile := "base/iobuffer.jl"
    juliaFns := ["unsafe_write(::GenericIOBuffer, ::Ptr{UInt8}, ::UInt)", "PipeBuffer"]
    statement := "write on an append buffer adds min(n, maxsize - retained bytes) bytes at the end and leaves the position alone, also across compaction."
    source := "base/iobuffer.jl:52-53 (append writes to size+1), 278 (PipeBuffer performs writes by appending)", status := .proven
    prop := ``AppendWritesAtEnd, thm := some ``appendWritesAtEnd },
  { id := "iobuffers-write-read-roundtrip", juliaFile := "base/iobuffer.jl"
    juliaFns := ["IOBuffer(; maxsize)", "write", "seekstart", "read(::GenericIOBuffer)"]
    statement := "IOBuffer(maxsize=m), any writes, seekstart, read returns the first m bytes written."
    source := "base/iobuffer.jl:180, 214-221 (maxsize docstring and example)", status := .proven
    prop := ``WriteReadRoundtrip, thm := some ``writeReadRoundtrip },
  { id := "iobuffers-pipe-fifo", juliaFile := "base/iobuffer.jl"
    juliaFns := ["PipeBuffer", "write", "read(::GenericIOBuffer, ::Type{UInt8})", "read(::GenericIOBuffer, nb)", "read(::GenericIOBuffer)"]
    statement := "For a PipeBuffer, the bytes read plus the bytes available equal the bytes written, in order, for any interleaving of writes and reads (including compaction)."
    source := "base/iobuffer.jl:272-283 (PipeBuffer behaves like a Unix pipe)", status := .proven
    prop := ``PipeFIFO, thm := some ``pipeFIFO },
  { id := "iobuffers-pipe-mark-reset", juliaFile := "base/iobuffer.jl"
    juliaFns := ["mark", "reset", "compact!", "get_used_span", "PipeBuffer"]
    statement := "On a PipeBuffer, reset after mark and any writes and reads returns the marked position and makes every byte since the mark available again."
    source := "base/io.jl:1569-1606 (mark/reset docstrings); base/iobuffer.jl:44-46", status := .proven
    prop := ``PipeMarkReset, thm := some ``pipeMarkReset },
  { id := "iobuffers-seek", juliaFile := "base/iobuffer.jl"
    juliaFns := ["seek(::GenericIOBuffer, ::Integer)", "seekstart"]
    statement := "seek(io, n) on a seekable buffer moves to clamp(n, 0, filesize); on a pipe it throws unless n == mark, and then moves to the mark."
    source := "base/iostream.jl:144-146 (seek docstring), base/iobuffer.jl:512-524", status := .proven
    prop := ``SeekSpec, thm := some ``seekSpec },
  { id := "iobuffers-skip", juliaFile := "base/iobuffer.jl"
    juliaFns := ["skip(::GenericIOBuffer, ::Integer)"]
    statement := "skip(io, n) moves by min(n, bytesavailable) for n >= 0 and to max(0, position + n) for n < 0 on seekable buffers, for every Int n including typemin/typemax."
    source := "base/iostream.jl skip docstring (seek relative to the current position), base/iobuffer.jl:475-494", status := .proven
    prop := ``SkipSpec, thm := some ``skipSpec },
  { id := "iobuffers-truncate", juliaFile := "base/iobuffer.jl"
    juliaFns := ["truncate(::GenericIOBuffer, ::Integer)"]
    statement := "truncate(io, n) throws ArgumentError exactly when not writable, not seekable, n < 0 or n > maxsize; otherwise the buffer holds its old bytes cut or zero-padded to n and position <= n."
    source := "base/iobuffer.jl:558-593; truncate docstring (base/iostream.jl)", status := .proven
    prop := ``TruncateSpec, thm := some ``truncateSpec
    notes := "The size claim is stated for n <= 2^60; larger n is OutOfMemoryError in Julia, which the model lacks." },
  { id := "iobuffers-take", juliaFile := "base/iobuffer.jl"
    juliaFns := ["take!(::IOBuffer)"]
    statement := "take! on a writable IOBuffer returns all bytes (the unread bytes of a pipe) and leaves position, bytesavailable and filesize 0 and no mark."
    source := "base/iobuffer.jl:716-718 (take! docstring)", status := .proven
    prop := ``TakeSpec, thm := some ``takeSpec },
  { id := "iobuffers-read", juliaFile := "base/iobuffer.jl"
    juliaFns := ["read(::GenericIOBuffer, nb)", "readbytes!", "read(::GenericIOBuffer, ::Type{UInt8})", "peek(::GenericIOBuffer, ::Type{UInt8})"]
    statement := "read(io, n) and readbytes! return the next min(n, bytesavailable) bytes and advance by that much; read(io, UInt8) returns the next byte or throws EOFError; peek does not move."
    source := "base/io.jl:1295-1330 (read and readbytes! docstrings)", status := .proven
    prop := ``ReadSpec, thm := some ``readSpec },
  { id := "iobuffers-readuntil", juliaFile := "base/iobuffer.jl"
    juliaFns := ["readuntil(::IO, ::UInt8)", "copyuntil(::IO, ::GenericIOBuffer, ::UInt8)", "readline", "_copyline"]
    statement := "readuntil(io, d; keep) and readline(io; keep) return the bytes up to the delimiter (with it iff keep; readline also strips \\r\\n) and consume through the delimiter."
    source := "base/io.jl:640-648 (copyuntil docstring), 719-728 (copyline docstring)", status := .proven
    prop := ``ReadUntilSpec, thm := some ``readUntilSpec },
  { id := "iobuffers-occursin", juliaFile := "base/iobuffer.jl"
    juliaFns := ["occursin(::UInt8, ::GenericIOBuffer)"]
    statement := "occursin(d, io) tells whether d is among the bytes available."
    source := "invariant (base/iobuffer.jl:984-986)", status := .proven
    prop := ``OccursinSpec, thm := some ``occursinSpec },
  -- refuted
  { id := "iobuffers-take-closewrite", juliaFile := "base/iobuffer.jl"
    juliaFns := ["take!(::IOBuffer)", "closewrite(::GenericIOBuffer)"]
    statement := "take! on a readable IOBuffer that is not writable returns its contents (the unread bytes of a pipe)."
    source := "base/iobuffer.jl:716-718 (take! docstring)", status := .refuted
    prop := ``TakeReadOnly, thm := some ``takeReadOnly_refuted
    issue := "none found (queries: Unreachable IOBuffer state, Unreachable IOBuffer, closewrite PipeBuffer take!, closewrite PipeBuffer)"
    notes := "PipeBuffer(); write(pb, \"abc\"); closewrite(pb); take!(pb) throws ErrorException(\"Unreachable IOBuffer state\")." },
  { id := "iobuffers-take-readonly-reset", juliaFile := "base/iobuffer.jl"
    juliaFns := ["take!(::IOBuffer)"]
    statement := "After take!(io) the IOBuffer is reset to its initial state (position 0)."
    source := "base/iobuffer.jl:716-718 (take! docstring: Afterwards, the IOBuffer is reset to its initial state)", status := .refuted
    prop := ``TakeResets, thm := some ``takeResets_refuted
    issue := "none found (queries: take! read-only IOBuffer, take! reset initial state)"
    notes := "io = IOBuffer(\"abc\"); read(io, UInt8); take!(io): position stays 1. Arguably intended for read-only buffers; documentation issue." },
  { id := "iobuffers-takestring-mark", juliaFile := "base/iobuffer.jl"
    juliaFns := ["takestring!(::IOBuffer)"]
    statement := "takestring!(io) returns the same bytes as String(take!(io))."
    source := "base/iobuffer.jl:812-817 (takestring! docstring)", status := .refuted
    prop := ``TakestringEqTake, thm := some ``takestringEqTake_refuted
    issue := "none found (queries: takestring!, takestring! mark, takestring PipeBuffer, takestring PipeBuffer mark)"
    notes := "Marked PipeBuffer after write \"abcdef\", mark, read 2: takestring! gives \"abcdef\", String(take!) \"cdef\"." },
  { id := "iobuffers-readuntil-unreadable", juliaFile := "base/iobuffer.jl"
    juliaFns := ["copyuntil(::IO, ::GenericIOBuffer, ::UInt8)", "_copyline(::IO, ::GenericIOBuffer)"]
    statement := "readuntil and readline on an IOBuffer that is not readable throw ArgumentError, like read."
    source := "base/iobuffer.jl:178 (read keyword restricts operations), 344-350", status := .refuted
    prop := ``ReadUntilUnreadable, thm := some ``readUntilUnreadable_refuted
    issue := "none found (queries: IOBuffer not readable readline, readuntil not readable IOBuffer, _throw_not_readable, IOBuffer readable readline, readuntil readable)"
    notes := "IOBuffer(read=false, write=true) with \"ab\\ncd\": readuntil(io, 0x0a) returns UInt8[0x61, 0x62]." },
  { id := "iobuffers-peek-clears-mark", juliaFile := "base/io.jl"
    juliaFns := ["peek(::IO, ::Type{T})"]
    statement := "peek(io, T) leaves the stream's mark unchanged."
    source := "base/essentials.jl:1539 (peek docstring: without advancing the current position)", status := .refuted
    prop := ``PeekKeepsMark, thm := some ``peekKeepsMark_refuted
    issue := "none found (queries: peek mark reset, peek clobbers mark, peek Char mark, peek resets mark, peek unmark, peek mark IOBuffer)"
    notes := "Generic peek = mark; read; reset. IOBuffer(\"abc\"); mark; read UInt8; peek(io, Char) or peek(io, Int8) unmarks io." },
  { id := "iobuffers-copyline-middle", juliaFile := "base/iobuffer.jl"
    juliaFns := ["copyline(::GenericIOBuffer, ::IO)"]
    statement := "copyline(out::IOBuffer, s; keep=false) into the middle of out writes the line without its newline."
    source := "base/io.jl:724-728 (copyline docstring)", status := .refuted
    prop := ``CopylineMiddle, thm := some ``copylineMiddle_refuted
    issue := "none found (queries: copyline, copyline IOBuffer, copyline keep, copyline keep false, copyline CRLF)"
    notes := "length(v) > 1 tests: an empty line \"\\n\" is written as \"\\n\", \"\\r\\n\" as \"\\r\"." },
  { id := "iobuffers-copyline-prior", juliaFile := "base/iobuffer.jl"
    juliaFns := ["copyline(::GenericIOBuffer, ::IO)"]
    statement := "copyline(out::IOBuffer, s; keep=false) at the end of out leaves the bytes already in out untouched."
    source := "base/io.jl:718-728 (copyline docstring)", status := .refuted
    prop := ``CopylineAtEnd, thm := some ``copylineAtEnd_refuted
    issue := "none found (queries: copyline, copyline IOBuffer, copyline keep, copyline keep false, copyline CRLF)"
    notes := "out = \"a\\n\", exhausted stream: copyline deletes the \"\\n\"; over a vector with memory offset, position becomes -1." },
  { id := "iobuffers-view-grow", juliaFile := "base/iobuffer.jl"
    juliaFns := ["ensureroom_slowpath", "get_used_span(::IOBuffer)", "_similar_data(::GenericIOBuffer, ::Int)"]
    statement := "write to a writable buffer over any AbstractVector{UInt8} does not throw MethodError."
    source := "base/iobuffer.jl:173-193 (IOBuffer docstring)", status := .refuted
    prop := ``WriteNoMethodError, thm := some ``writeNoMethodError_refuted
    issue := "none found (queries: get_used_span, IOBuffer view write MethodError, IOBuffer SubArray, IOBuffer view)"
    notes := "IOBuffer(view(zeros(UInt8, 4), 1:4); write=true); write(io, \"hello\") throws MethodError(get_used_span)." },
  { id := "iobuffers-pipebuffer-maxsize-type", juliaFile := "base/iobuffer.jl"
    juliaFns := ["PipeBuffer(data; maxsize)", "PipeBuffer(maxsize::Integer)"]
    statement := "PipeBuffer accepts maxsize of any Integer type, as documented."
    source := "base/iobuffer.jl:276 (PipeBuffer docstring: maxsize::Integer)", status := .refuted
    prop := ``PipeBufferMaxsizeInteger, thm := some ``pipeBufferMaxsizeInteger_refuted
    issue := "none found (queries: PipeBuffer maxsize Integer, PipeBuffer maxsize)"
    notes := "PipeBuffer(UInt8[]; maxsize=UInt(10)) and PipeBuffer(UInt(10)) throw TypeError." },
  { id := "iobuffers-truncate-mark", juliaFile := "base/iobuffer.jl"
    juliaFns := ["truncate(::GenericIOBuffer, ::Integer)"]
    statement := "truncate(io, n) keeps a mark at a position <= n."
    source := "base/iobuffer.jl:578 (comment: clear the mark if it points to data that has now been deleted)", status := .refuted
    prop := ``TruncateKeepsMark, thm := some ``truncateKeepsMark_refuted
    issue := "none found (queries: truncate mark IOBuffer, truncate IOBuffer mark)"
    notes := "write \"abcdef\", seek 3, mark, truncate(io, 3): ismarked false." }
]

end JuliaLean.IOBuffers
