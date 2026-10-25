# truncate(io, n) removes a mark at position n, which is still inside the buffer
io = IOBuffer()
write(io, "abcdef")
seek(io, 3)
mark(io)
truncate(io, 3)
println("after truncate(io, 3): ismarked = ", ismarked(io), ", position = ", position(io))
!ismarked(io) && println("REPRODUCED iobuffers-truncate-mark")
