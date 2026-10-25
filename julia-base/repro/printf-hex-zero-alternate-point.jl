using Printf
lower = @sprintf("%#a", 0.0)
upper = @sprintf("%#.0A", -0.0)
println("%#a 0.0 = ", repr(lower), "; C99 expected ", repr("0x0.p+0"))
println("%#.0A -0.0 = ", repr(upper), "; C99 expected ", repr("-0X0.P+0"))
lower == "0x0p+0" && upper == "-0X0P+0" && println("REPRODUCED printf-hex-zero-alternate-point")
