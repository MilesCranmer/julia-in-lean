# readuntil/readline read from an IOBuffer opened with read=false
io = IOBuffer(read=false, write=true)
write(io, "ab\ncd")
seekstart(io)
r1 = try read(io, UInt8) catch e; e end
r2 = try readuntil(io, 0x0a) catch e; e end
seekstart(io)
r3 = try readline(io) catch e; e end
println("read(io, UInt8) = ", r1)
println("readuntil(io, 0x0a) = ", repr(r2), ", readline(io) = ", repr(r3))
r1 isa ArgumentError && !(r2 isa Exception) && println("REPRODUCED iobuffers-readuntil-unreadable")
