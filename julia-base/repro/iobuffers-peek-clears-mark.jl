# peek(io, T) for T other than UInt8 and multi-byte numbers removes the user's mark
io = IOBuffer("abc")
mark(io)
read(io, UInt8)
c = peek(io, Char)
println("peek(io, Char) = ", repr(c), ", ismarked(io) = ", ismarked(io))
io2 = IOBuffer("abc"); mark(io2); read(io2, UInt8); peek(io2, Int8)
println("after peek(io, Int8): ismarked = ", ismarked(io2))
!ismarked(io) && println("REPRODUCED iobuffers-peek-clears-mark")
