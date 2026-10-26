function stream(s)
    bs = Base.BufferStream(); write(bs, s); closewrite(bs); bs
end
println("IOBuffer: ", repr(read(skipchars(isspace, IOBuffer("  x")), String)))
failed = false
for (name, io) in (("BufferStream", stream("  x")), ("PipeBuffer", PipeBuffer(collect(codeunits("  x")))),
                   ("Process", open(`printf '  x'`)))
    try
        skipchars(isspace, io)
        println(name, ": ", repr(read(io, String)))
    catch e
        global failed = true
        println(name, ": threw ", typeof(e), ": ", first(sprint(showerror, e), 80))
    end
end
if failed
    println("REPRODUCED iocov-skipchars-nonseekable")
end
