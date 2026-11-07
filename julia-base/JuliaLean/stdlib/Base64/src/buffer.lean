import JuliaLean.stdlib.Base64.src.Base64

namespace JuliaLean.Base64Uuid

open JuliaLean JuliaLean.ParsePrint

/-- `read_to_buffer(io, buffer)`, `buffer.jl:29-39`: move the valid region to the front
(offset 0) and append `min(bytesavailable(io), capacity(buffer) - buffer.size)` bytes. -/
def readToBuffer (buf io : List Byte) : List Byte × List Byte :=
  if io.isEmpty then (buf, io)
  else
    let n := min io.length (512 - buf.length)
    (buf ++ io.take n, io.drop n)

end JuliaLean.Base64Uuid
