# round(x; digits) and round(x; sigdigits) should round to the nearest multiple of
# the step; a positive x at least as large as the step can never round to zero.
x = floatmax(Float64)
@assert 10.0^308 == 1e308 && x >= 1e308
a = round(x; digits=-308)
b = round(x; sigdigits=1)
c = round(-x; sigdigits=2)
println("round(floatmax(), digits=-308) = ", a)
println("round(floatmax(), sigdigits=1) = ", b)
println("round(-floatmax(), sigdigits=2) = ", c)
println("round(floatmax(), RoundUp, digits=-308) = ", round(x, RoundUp; digits=-308))
a == 0 && b == 0 && c == 0 && println("REPRODUCED parseprint-round-digits-overflow-zero")
