using Printf
high = @sprintf("%.3g", 999.5)
low = @sprintf("%g", 9.999999e-5)
println("%.3g 999.5 = ", repr(high), "; C99 expected ", repr("1e+03"))
println("%g 9.999999e-5 = ", repr(low), "; C99 expected ", repr("0.0001"))
high == "1000" && low == "1e-04" && println("REPRODUCED printf-general-style-rounding")
