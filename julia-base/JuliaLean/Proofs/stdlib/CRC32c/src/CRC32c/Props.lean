import JuliaLean.stdlib.CRC32c.src.CRC32c

namespace JuliaLean.Base64Uuid

open JuliaLean JuliaLean.ParsePrint

/-- `crc32c(data2, crc32c(data1)) == crc32c([data1; data2])` (`CRC32c.jl:21-22`) for the
dense and the generic vector methods, which agree. -/
def Crc32cChunks : Prop :=
  ∀ (a b : List Byte) (crc : U32),
    crc32cDense b (crc32cDense a crc) = crc32cDense (a ++ b) crc ∧
    crc32cVec b (crc32cVec a crc) = crc32cVec (a ++ b) crc ∧
    crc32cVec a crc = crc32cDense a crc

/-- `crc32c(io, nb, crc)` checksums the next `min(nb, bytesavailable)` bytes and
consumes them; `crc32c(io, crc)` checksums all remaining bytes (`CRC32c.jl:60-68`). -/
def Crc32cIo : Prop :=
  ∀ (io : List Byte) (nb : Int) (crc : U32), 0 ≤ nb →
    crc32cIoNb io nb crc = .ok (crc32cDense (io.take nb.toNat) crc, io.drop nb.toNat) ∧
    (io.length < 2 ^ 63 → crc32cIo io crc = .ok (crc32cDense io crc, []))

/-- `crc32c(io::IOStream, crc)` checksums all remaining bytes of the file
(`CRC32c.jl:25-28`: "`crc32c(io, crc)` to checksum all the remaining bytes. Hence you can
do `open(crc32c, filename)`"). -/
def Crc32cStreamAll : Prop :=
  ∀ (f : IOStreamF) (crc : U32), f.pos ≤ f.content.length →
    crc32cIOStream f crc = .ok (crc32cDense (f.content.drop f.pos) crc)

end JuliaLean.Base64Uuid
