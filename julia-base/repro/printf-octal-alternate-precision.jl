using Printf
zero = @sprintf("%#o", UInt32(0))
padded = @sprintf("%#.5o", UInt32(1))
println("%#o zero = ", repr(zero), "; C99 expected ", repr("0"))
println("%#.5o one = ", repr(padded), "; C99 expected ", repr("00001"))
zero == "00" && padded == "000001" && println("REPRODUCED printf-octal-alternate-precision")
