# Base._crc32c(io::IOStream, crc) = Base._crc32c(io, filesize(io) - position(io), crc)
# (base/util.jl:541).  The docstring promises that crc32c(io, crc) checksums "all the
# remaining bytes" and suggests open(crc32c, filename).  For files whose stat size is
# 0 (Linux /proc files, FIFOs) nothing is read; past the end it throws.
using CRC32c

path = "/proc/self/status"   # stat size 0 on Linux, nonempty content
c_stream, c_read = open(path) do io
    c = crc32c(io)
    seekstart(io)
    c, crc32c(read(io))
end
println("filesize(path)                  = ", filesize(path))
println("open(crc32c, path)              = ", repr(c_stream))
println("crc32c(read(io)) on same handle = ", repr(c_read))

f = tempname()
write(f, "hello")
r_past = try
    open(io -> (seek(io, 10); crc32c(io)), f)
catch e
    e
end
r_buf = (io = IOBuffer("hello"); seek(io, 10); crc32c(io))
println("IOStream seeked past end: crc32c(io) = ", repr(r_past))
println("IOBuffer seeked past end: crc32c(io) = ", repr(r_buf))
rm(f)

if c_stream == 0x00000000 && c_read != 0x00000000
    println("REPRODUCED base64uuid-crc32c-iostream-filesize")
end
