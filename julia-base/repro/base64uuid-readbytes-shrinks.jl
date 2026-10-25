# The readbytes! docstring (base/io.jl:1298-1299): "The size of b will be increased
# if needed ..., but it will never be decreased."  readbytes!(::Base64DecodePipe, ...)
# ends with resize!(data, filled) (stdlib/Base64/src/decode.jl:127).
using Base64

pipe = Base64DecodePipe(IOBuffer("SGVsbG8h"))   # decodes to the 6 bytes "Hello!"
data = zeros(UInt8, 100)
n = readbytes!(pipe, data)
println("Base64DecodePipe: readbytes! = ", n, ", length(data) after = ", length(data))

io = IOBuffer("Hello!")
data2 = zeros(UInt8, 100)
n2 = readbytes!(io, data2)
println("IOBuffer:         readbytes! = ", n2, ", length(data) after = ", length(data2))

if length(data) < 100 && length(data2) == 100
    println("REPRODUCED base64uuid-readbytes-shrinks")
end
