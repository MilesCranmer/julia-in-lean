# .-r on an unsigned range containing zero, or an empty unsigned range, has the wrong length.
r = 0x00:0x02
a = .-r
b = .-collect(r)
println(".-(0x00:0x02) = ", repr(a), " with elements ", collect(a))
println(".-collect(0x00:0x02) = ", b)
e = .-(0x01:0x00)
println(".-(0x01:0x00) has length ", length(e), "; .-collect(0x01:0x00) has length ", length(.-collect(0x01:0x00)))
println("-(0x00:0x02) = ", -r)
if collect(a) != b || length(e) != 0
    println("REPRODUCED broadcastviews-range-negate-unsigned")
end
