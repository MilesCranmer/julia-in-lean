using Printf
lower = @sprintf("%#x", UInt32(0))
upper = @sprintf("%#X", UInt32(0))
println("%#x zero = ", repr(lower), "; C99 expected ", repr("0"))
println("%#X zero = ", repr(upper), "; C99 expected ", repr("0"))
lower == "0x0" && upper == "0X0" && println("REPRODUCED printf-hex-alternate-zero")
