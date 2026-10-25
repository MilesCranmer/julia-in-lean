import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.Base64Uuid.DecodeProofs
import JuliaLean.Base64Uuid.EncodeProofs
import JuliaLean.Base64Uuid.UuidStringProofs
import JuliaLean.Base64Uuid.Props
import JuliaLean.Base64Uuid.Refutations
import JuliaLean.Base64Uuid.UuidBitsProofs
import JuliaLean.Base64Uuid.CrcProofs

namespace JuliaLean.Base64Uuid

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  -- refuted
  { id := "base64uuid-decodepipe-eof-buffered", juliaFile := "stdlib/Base64/src/decode.jl"
    juliaFns := ["eof(::Base64DecodePipe)", "readbytes!(::Base64DecodePipe, ::AbstractVector{UInt8}, ::Integer)"]
    statement := "Reading a Base64DecodePipe with read(pipe, k1), ..., read(pipe) yields the bytes base64decode returns for its source."
    source := "invariant; base/io.jl:211-214 (eof docstring: false while buffered data is available)", status := .refuted
    prop := ``DecodeStreamSplit, thm := some ``decodeStreamSplit_refuted
    issue := "related #44619 (closed); none found for partial reads (queries: Base64DecodePipe eof, Base64DecodePipe readbytes, base64decode truncated, Base64 eof)"
    notes := "Source \"SGVsbG8hSGVs\": read(pipe, 6) leaves 4 characters in pipe.buffer, eof(pipe) is true and read(pipe) returns []. Same in 1.13.2." },
  { id := "base64uuid-decodepipe-eof-ignored-tail", juliaFile := "stdlib/Base64/src/decode.jl"
    juliaFns := ["eof(::Base64DecodePipe)", "read(::Base64DecodePipe, ::Type{UInt8})"]
    statement := "After eof(pipe) returns false, read(pipe, UInt8) returns a byte."
    source := "base/io.jl:211-213 (eof docstring)", status := .refuted
    prop := ``EofThenReadByte, thm := some ``eofThenReadByte_refuted
    issue := "none found (queries: Base64DecodePipe EOFError, base64 EOFError, Base64 readline, Base64DecodePipe eof)"
    notes := "Source \"QQ==\\n\": after one byte only the ignored newline remains; eof is false and read throws EOFError. readline on newline-terminated base64 throws too." },
  { id := "base64uuid-readbytes-empty-hang", juliaFile := "stdlib/Base64/src/decode.jl"
    juliaFns := ["readbytes!(::Base64DecodePipe, ::AbstractVector{UInt8}, ::Integer)"]
    statement := "readbytes!(pipe, data, nb) returns for every source, destination and nb."
    source := "base/io.jl:1295-1300 (readbytes! docstring)", status := .refuted
    prop := ``ReadbytesTerminates, thm := some ``readbytesTerminates_refuted
    issue := "none found (queries: Base64DecodePipe readbytes, Base64DecodePipe hang, Base64 readbytes!)"
    notes := "readbytes!(Base64DecodePipe(IOBuffer(\"QQ==\")), UInt8[], 1) loops forever: resize!(data, 2*0) keeps the buffer empty." },
  { id := "base64uuid-readbytes-shrinks", juliaFile := "stdlib/Base64/src/decode.jl"
    juliaFns := ["readbytes!(::Base64DecodePipe, ::AbstractVector{UInt8}, ::Integer)"]
    statement := "readbytes!(pipe, data, nb) never decreases length(data)."
    source := "base/io.jl:1298-1299 (readbytes! docstring)", status := .refuted
    prop := ``ReadbytesNoShrink, thm := some ``readbytesNoShrink_refuted
    issue := "none found (queries: readbytes! decreased, readbytes! resize shrink, Base64 readbytes!)"
    notes := "A 4-byte buffer becomes 1 byte long after reading \"QQ==\"." },
  { id := "base64uuid-decode-padding-midstream", juliaFile := "stdlib/Base64/src/decode.jl"
    juliaFns := ["base64decode", "Base64DecodePipe"]
    statement := "base64decode throws ArgumentError when padding occurs outside the last two positions of the last group of four."
    source := "stdlib/Base64/docs/src/index.md (master, added in #60260)", status := .refuted
    prop := ``DecodeRejectsMidPadding, thm := some ``decodeRejectsMidPadding_refuted
    issue := "related #44619 (closed), #60260 (merged docs); none found (queries: base64 padding, base64decode padding middle, base64 concatenated)"
    notes := "base64decode(\"QQ==QQ==\") == [0x41, 0x41]. The manual text is not in 1.13.2." },
  { id := "base64uuid-uuid5-unescape", juliaFile := "stdlib/UUIDs/src/UUIDs.jl"
    juliaFns := ["uuid5(::UUID, ::String)"]
    statement := "uuid5(ns, name) hashes the namespace bytes followed by the code units of name (RFC 4122 section 4.3)."
    source := "stdlib/UUIDs/src/UUIDs.jl:124-127 (uuid5 docstring citing RFC 4122)", status := .refuted
    prop := ``Uuid5HashesName, thm := some ``uuid5HashesName_refuted
    issue := "none found (queries: uuid5 unescape_string, uuid5 escape, UUIDs uuid5 backslash, uuid5 RFC 4122)"
    notes := "The name \"\\\\n\" is hashed as the single byte 0x0a; \"C:\\\\Users\" throws ArgumentError." },
  { id := "base64uuid-crc32c-iostream-filesize", juliaFile := "base/util.jl"
    juliaFns := ["crc32c(::IOStream, ::UInt32)"]
    statement := "crc32c(io::IOStream, crc) checksums all remaining bytes of the file."
    source := "stdlib/CRC32c/src/CRC32c.jl:25-28, 63-65 (crc32c docstrings)", status := .refuted
    prop := ``Crc32cStreamAll, thm := some ``crc32cStreamAll_refuted
    issue := "none found (queries: crc32c filesize, crc32c IOStream, crc32c proc, crc32c open file)"
    notes := "A file whose stat size is 0 (/proc, FIFOs) checksums to the seed; seeking past the end throws ArgumentError." },
  -- proven
  { id := "base64uuid-encode-decode-roundtrip", juliaFile := "stdlib/Base64/src/decode.jl"
    juliaFns := ["base64encode", "base64decode"]
    statement := "base64decode(base64encode(x)) == x for every byte vector x."
    source := "invariant; base64encode/base64decode docstrings", status := .proven
    prop := ``EncodeDecodeRoundtrip, thm := some ``encodeDecodeRoundtrip_proven
    notes := "Covers inputs below 2^48 bytes. The read loop stops only when the pipe has no unread source and nothing pending in pipe.rest; it cannot stop early with characters still in pipe.buffer (the eof-buffered bug) because the buffer sizes 1024 * 2^j are never multiples of 3, while a stop inside clean full groups needs a multiple of 3 bytes decoded." },
  { id := "base64uuid-encode-stream-split", juliaFile := "stdlib/Base64/src/encode.jl"
    juliaFns := ["Base64EncodePipe", "write(::Base64EncodePipe, ::UInt8)", "unsafe_write(::Base64EncodePipe, ::Ptr{UInt8}, ::UInt)", "close(::Base64EncodePipe)"]
    statement := "Writing x to a Base64EncodePipe in any sequence of byte and vector writes, then closing it, produces base64encode(x)."
    source := "stdlib/Base64/src/encode.jl:8-33 (Base64EncodePipe docstring)", status := .proven
    prop := ``EncodeStreamSplit, thm := some ``encodeStreamSplit_proven },
  { id := "base64uuid-uuid-string-roundtrip", juliaFile := "base/uuid.jl"
    juliaFns := ["string(::UUID)", "UUID(::AbstractString)", "parse(::Type{UUID}, ::AbstractString)"]
    statement := "UUID(string(u)) == u for every UUID u."
    source := "base/uuid.jl:3-7 (UUID docstring: conversion from a string checks validity)", status := .proven
    prop := ``UuidStringRoundtrip, thm := some ``uuidStringRoundtrip_proven
    notes := "Includes the SWAR checks: Parsers.ishexdigits8 accepts and Parsers.hexdigits8 converts every word of eight lowercase hex digits (HexProofs). 1.13.2 parses with a different, per-character implementation." },
  { id := "base64uuid-uuid4-bits", juliaFile := "stdlib/UUIDs/src/UUIDs.jl"
    juliaFns := ["uuid4", "uuid_version"]
    statement := "uuid4 returns a UUID with version 4 and the RFC 4122 variant for every random value."
    source := "stdlib/UUIDs/src/UUIDs.jl:91-115 (uuid4 docstring), RFC 4122 section 4.4", status := .proven
    prop := ``Uuid4Bits, thm := some ``uuid4Bits_proven },
  { id := "base64uuid-uuid1-bits", juliaFile := "stdlib/UUIDs/src/UUIDs.jl"
    juliaFns := ["uuid1", "_build_uuid1", "uuid_version"]
    statement := "uuid1 returns a UUID with version 1 and the RFC 4122 variant for every random value and timestamp."
    source := "stdlib/UUIDs/src/UUIDs.jl:38-63 (uuid1 docstring), RFC 4122 section 4.2", status := .proven
    prop := ``Uuid1Bits, thm := some ``uuid1Bits_proven },
  { id := "base64uuid-uuid7-bits", juliaFile := "stdlib/UUIDs/src/UUIDs.jl"
    juliaFns := ["uuid7", "_build_uuid7", "uuid_version"]
    statement := "uuid7 returns a UUID with version 7 and the RFC variant for every random value and every timestamp below 2^48 ms."
    source := "stdlib/UUIDs/src/UUIDs.jl:164-188 (uuid7 docstring), RFC 9562 section 5.7", status := .proven
    prop := ``Uuid7Bits, thm := some ``uuid7Bits_proven
    notes := "Timestamps of 2^48 ms (year 10889) or more would spill into the version bits." },
  { id := "base64uuid-uuid5-bits", juliaFile := "stdlib/UUIDs/src/UUIDs.jl"
    juliaFns := ["uuid5", "uuid_version"]
    statement := "uuid5 returns a UUID with version 5 and the RFC 4122 variant whatever the digest."
    source := "stdlib/UUIDs/src/UUIDs.jl:123-144 (uuid5 docstring), RFC 4122 section 4.3", status := .proven
    prop := ``Uuid5Bits, thm := some ``uuid5Bits_proven },
  { id := "base64uuid-crc32c-chunks", juliaFile := "stdlib/CRC32c/src/CRC32c.jl"
    juliaFns := ["crc32c(::AbstractVector{UInt8}, ::UInt32)", "crc32c(::DenseUInt8OrInt8, ::UInt32)", "crc32c(::String, ::UInt32)"]
    statement := "crc32c(b, crc32c(a, c)) == crc32c([a; b], c), for dense and generic vectors, and the 24576-byte blocks of the generic method give the dense result."
    source := "stdlib/CRC32c/src/CRC32c.jl:20-22 (crc32c docstring)", status := .proven
    prop := ``Crc32cChunks, thm := some ``crc32cChunks_proven
    notes := "jl_crc32c is modelled by the byte loop of jl_crc32c_sw (src/crc32c.c)." },
  { id := "base64uuid-crc32c-io", juliaFile := "base/util.jl"
    juliaFns := ["crc32c(::IO, ::Integer, ::UInt32)", "crc32c(::IO, ::UInt32)"]
    statement := "crc32c(io, nb, crc) checksums and consumes the next min(nb, bytesavailable) bytes of an IOBuffer; crc32c(io, crc) checksums all of them."
    source := "stdlib/CRC32c/src/CRC32c.jl:60-68 (crc32c(io) docstring)", status := .proven
    prop := ``Crc32cIo, thm := some ``crc32cIo_proven }
]

end JuliaLean.Base64Uuid
