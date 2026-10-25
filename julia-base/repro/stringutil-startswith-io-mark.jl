io = IOBuffer("abc")
read(io, Char)           # consume 'a'
mark(io)                 # the caller marks position 1
r = startswith(io, "b")
println("startswith(io, \"b\") = ", r, ", ismarked(io) = ", ismarked(io))
io2 = IOBuffer("abc"); read(io2, Char); mark(io2)
startswith(io2, 'b')
println("after startswith(io, 'b'): ismarked(io) = ", ismarked(io2))
e = try reset(io); nothing catch err err end
println("reset(io) = ", e === nothing ? "ok" : sprint(showerror, e))
!ismarked(io) && !ismarked(io2) && e isa ArgumentError && println("REPRODUCED stringutil-startswith-io-mark")
