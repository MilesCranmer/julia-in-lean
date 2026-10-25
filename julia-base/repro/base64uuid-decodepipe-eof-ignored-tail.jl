# eof(::Base64DecodePipe) is false while only ignored characters (here the final
# newline that base64 tools append) remain in the source, but the next
# read(pipe, UInt8) throws EOFError.  The eof docstring (base/io.jl:211-213) says
# "it is always safe to read one byte after seeing eof return false".
using Base64

pipe = Base64DecodePipe(IOBuffer("SGVsbG8h\n"))   # "Hello!" plus a newline
out = UInt8[]
err = nothing
try
    while !eof(pipe)
        push!(out, read(pipe, UInt8))
    end
catch e
    global err = e
end
got = String(copy(out))
println("bytes read before the error: ", repr(got))
println("error: ", repr(err))

line_err = try
    readline(Base64DecodePipe(IOBuffer("SGVsbG8h\n")))
catch e
    e
end
println("readline(pipe) = ", repr(line_err))

if err isa EOFError && got == "Hello!"
    println("REPRODUCED base64uuid-decodepipe-eof-ignored-tail")
end
