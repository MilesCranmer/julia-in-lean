import JuliaLean.Base64Uuid.Basic

/-!
Model of the CRC-32c wrappers: `stdlib/CRC32c/src/CRC32c.jl` and `base/util.jl:515-551`
(master `bbfa0ce4150`, identical in 1.13.2).

`jl_crc32c(crc, buf, len)` (`src/crc32c.c`) is modelled by the byte-at-a-time loop of
`jl_crc32c_sw` (`src/crc32c.c:400-440`, its final `while (len)` loop) with
`crc32c_table[0]` built as in `crc32c_init_sw` (`src/crc32c.c:466-479`). The
8-bytes-at-a-time table loop and the SSE4.2/ARMv8 instruction paths compute the same
function, as the comment at `src/crc32c.c:397-399` states.

A generic `IO` stream (an `IOBuffer`) is its list of unread bytes; `readbytes!(io, b, nb)`
reads `min(nb, bytesavailable(io))` bytes. An `IOStream` is a file: its content, the
read position, and the size `filesize(io)` reports from `stat`, which equals the
content length for regular files and is 0 for Linux `/proc` files and FIFOs.
-/

namespace JuliaLean.Base64Uuid

open JuliaLean JuliaLean.ParsePrint

abbrev U32 := JInt .u32

/-- `POLY`, `src/crc32c.c:56`. -/
def POLY : U32 := JInt.lit .u32 0x82f63b78

/-- One step of `crc = crc & 1 ? (crc >> 1) ^ POLY : crc >> 1`, `src/crc32c.c:463`. -/
def crcBit (c : U32) : U32 :=
  if (band c (JInt.lit .u32 1)).val == 1 then bxor (shr c 1) POLY else shr c 1

/-- `crc32c_table[0][n]`, `src/crc32c.c:460-471`. -/
def crcTable0 (n : Nat) : U32 := Nat.repeat crcBit 8 (JInt.lit .u32 n)

/-- `crc = crc32c_table[0][(crc ^ *buf++) & 0xff] ^ (crc >> 8)`, `src/crc32c.c:434-437`. -/
def crcByte (c : U32) (b : Byte) : U32 :=
  bxor (crcTable0 (band (bxor c (JInt.rem .u32 b)) (JInt.lit .u32 0xff)).val.toNat) (shr c 8)

/-- `jl_crc32c(crc, buf, len)` on the bytes `xs`: `crc ^ 0xffffffff`, the byte loop,
and `^ 0xffffffff` again. -/
def jl_crc32c (crc : U32) (xs : List Byte) : U32 :=
  bxor (xs.foldl crcByte (bxor crc (JInt.lit .u32 0xffffffff))) (JInt.lit .u32 0xffffffff)

/-- The block loop of `crc32c(a::AbstractVector{UInt8}, crc)`, `CRC32c.jl:39-52`: copy
`n = min(nb, 24576)` bytes into `buf` and checksum them, until `nb == 0`. `rem` holds the
`nb` bytes not yet checksummed; the fuel is the number of blocks. -/
def crcBlocks : Nat → U32 → List Byte → U32
  | 0, crc, _ => crc
  | fuel + 1, crc, rem =>
    if rem.length > 0 then
      let n := min rem.length 24576
      crcBlocks fuel (jl_crc32c crc (rem.take n)) (rem.drop n)
    else crc

/-- `crc32c(a::AbstractVector{UInt8}, crc)` for a non-dense vector, `CRC32c.jl:39-52`. -/
def crc32cVec (a : List Byte) (crc : U32) : U32 := crcBlocks (a.length + 1) crc a

/-- `crc32c(a::DenseUInt8OrInt8, crc)` and `crc32c(s::String, crc)`, `CRC32c.jl:54-58`,
`base/util.jl:520-526`: one `unsafe_crc32c` over all bytes (code units). -/
def crc32cDense (a : List Byte) (crc : U32) : U32 := jl_crc32c crc a

/-- The `while` loop of `_crc32c(io, nb, crc)`, `base/util.jl:533-537`, with
`length(buf) = blen`: `readbytes!(io, buf)` reads `min(blen, bytesavailable(io))`. -/
def crcIoLoop : Nat → Nat → List Byte → Int → U32 → List Byte × Int × U32
  | 0, _, io, nb, crc => (io, nb, crc)
  | fuel + 1, blen, io, nb, crc =>
    if !io.isEmpty && nb > 24576 then
      let n := min blen io.length
      crcIoLoop fuel blen (io.drop n) (nb - n) (jl_crc32c crc (io.take n))
    else (io, nb, crc)

/-- `_crc32c(io::IO, nb, crc)`, `base/util.jl:528-539`: the checksum and the unread rest. -/
def crc32cIoNb (io : List Byte) (nb : Int) (crc : U32) : Jle (U32 × List Byte) :=
  if nb < 0 then .error (argErr "number of bytes to checksum must be ≥ 0") else
  let blen := (min nb 24576).toNat
  let (io, nb, crc) := crcIoLoop (io.length + 1) blen io nb crc
  let n := min (min nb blen).toNat io.length
  .ok (jl_crc32c crc (io.take n), io.drop n)

/-- `typemax(Int64)`. -/
def typemaxI64 : Int := 2 ^ 63 - 1

/-- `crc32c(io::IO, crc)` = `_crc32c(io, typemax(Int64), crc)`, `base/util.jl:540`. -/
def crc32cIo (io : List Byte) (crc : U32) : Jle (U32 × List Byte) := crc32cIoNb io typemaxI64 crc

/-- An open `IOStream` on a file. -/
structure IOStreamF where
  content : List Byte
  pos : Nat
  /-- `filesize(io)`: the size `stat` reports. -/
  statSize : Nat
  deriving Repr, DecidableEq

/-- `crc32c(io::IOStream, crc)` = `_crc32c(io, filesize(io) - position(io), crc)`,
`base/util.jl:541`; reads go to the unread content. -/
def crc32cIOStream (f : IOStreamF) (crc : U32) : Jle U32 :=
  (crc32cIoNb (f.content.drop f.pos) ((f.statSize : Int) - f.pos) crc).map (·.1)

end JuliaLean.Base64Uuid
