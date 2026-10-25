# eof(::Base64DecodePipe) = isempty(pipe.rest) && eof(pipe.io)
# (stdlib/Base64/src/decode.jl:131) ignores the characters already copied from
# pipe.io into pipe.buffer.  After a partial read has pulled the whole input into
# the buffer, eof reports true and read returns nothing, losing the rest.
using Base64

msg = "Hello, world! more text"
enc = base64encode(msg)
pipe = Base64DecodePipe(IOBuffer(enc))
head = String(read(pipe, 6))
at_end = eof(pipe)
tail = String(read(pipe))
println("encoded = ", repr(enc))
println("read(pipe, 6) = ", repr(head))
println("eof(pipe)     = ", at_end)
println("read(pipe)    = ", repr(tail))

if head * tail != msg
    println("REPRODUCED base64uuid-decodepipe-eof-buffered")
end
