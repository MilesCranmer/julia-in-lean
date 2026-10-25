# take! on a read-only IOBuffer does not reset it to its initial state
io = IOBuffer("abc")
read(io, UInt8)
a = take!(io)
println("take! = ", repr(String(a)), ", position afterwards = ", position(io), ", second take! = ", repr(String(take!(io))))
position(io) != 0 && println("REPRODUCED iobuffers-take-readonly-reset")
