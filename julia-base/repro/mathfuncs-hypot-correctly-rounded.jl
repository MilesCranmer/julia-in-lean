x = 1.529780669165982e-308
y = 2.6715387816e-314
println("x bits              = ", string(reinterpret(UInt64, x), base=16))
println("y bits              = ", string(reinterpret(UInt64, y), base=16))
h = hypot(x, y)
println("hypot bits          = ", string(reinterpret(UInt64, h), base=16))
exact = sqrt(big(x)^2 + big(y)^2)
println("hypot(x, y)          = ", repr(h))
println("correctly rounded    = ", repr(Float64(exact)))
println("error in ulps        = ", Float64((big(h) - exact) / big(nextfloat(0.0))))
if h != Float64(exact)
    println("REPRODUCED mathfuncs-hypot-correctly-rounded")
end
