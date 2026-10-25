# replace(io, s, r => s"\1") writes captures at the read position of an append-mode buffer.
io = PipeBuffer()               # append = true: writes go to the end
write(io, "head")
read(io, UInt8)                 # consume 'h'; the read position moves, the end does not
replace(io, "abc", r"(b)" => s"<\1>")
got = read(io, String)
expected = "ead" * replace("abc", r"(b)" => s"<\1>")
println("got      = ", repr(got))
println("expected = ", repr(expected))
got != expected && println("REPRODUCED regexunicode-replace-capture-append")
