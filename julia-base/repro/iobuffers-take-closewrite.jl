# take! on a PipeBuffer after closewrite throws instead of returning the unread bytes
pb = PipeBuffer()
write(pb, "abc")
closewrite(pb)
r = try take!(pb) catch e; e end
println("take!(pb) = ", repr(r))
r isa ErrorException && println("REPRODUCED iobuffers-take-closewrite")
