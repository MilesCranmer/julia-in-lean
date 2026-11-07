import JuliaLean.base.util

namespace JuliaLean.Base64Uuid

open JuliaLean JuliaLean.ParsePrint

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

end JuliaLean.Base64Uuid
