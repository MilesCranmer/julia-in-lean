r = Libc.dup(Libc.RawFD(12345))
println("dup(RawFD(12345)) = ", r)
try
    Libc.dup(Libc.RawFD(12345), Libc.RawFD(12346))
catch e
    println("dup(RawFD(12345), RawFD(12346)) threw ", typeof(e))
end
if r == Libc.RawFD(-1)
    println("REPRODUCED iocov-dup-unchecked")
end
