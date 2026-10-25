# takestring! on a marked PipeBuffer returns bytes that were already read
function mk()
    pb = PipeBuffer()
    write(pb, "abcdef")
    mark(pb)
    read(pb, 2)
    pb
end
s1 = takestring!(mk())
s2 = String(take!(mk()))
println("takestring! = ", repr(s1), ", String(take!) = ", repr(s2))
s1 != s2 && println("REPRODUCED iobuffers-takestring-mark")
