function stream(s)
    bs = Base.BufferStream(); write(bs, s); closewrite(bs); bs
end
s = "x\r\r\ny"
to_buffer = String(take!(copyline(IOBuffer(), stream(s))))
o = IOBuffer(); copyline(IOContext(o), stream(s)); to_other = String(take!(o))
println("readline(IOBuffer(s))          = ", repr(readline(IOBuffer(s))))
println("copyline(IOBuffer(), stream)   = ", repr(to_buffer))
println("copyline(IOContext(..), stream) = ", repr(to_other))
if to_other != to_buffer
    println("REPRODUCED iocov-copyline-cr-crlf")
end
