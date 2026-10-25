# The first element of -0.0:s:b is +0.0.
r = -0.0:1.0:2.0
println("first(-0.0:1.0:2.0) = ", repr(first(r)), "   signbit = ", signbit(first(r)))
println("first(range(-0.0; step=1.0, length=3)) = ", repr(first(range(-0.0; step=1.0, length=3))))
!signbit(first(r)) && println("REPRODUCED floatranges-colon-signed-zero")
