x = 1.529780669165982e-308
y = 2.6715387816e-314
h = hypot(x, y)
exact = sqrt(big(x)^2 + big(y)^2)
println("hypot(x, y)          = ", repr(h))
println("correctly rounded    = ", repr(Float64(exact)))
println("error in ulps        = ", Float64((big(h) - exact) / big(nextfloat(0.0))))
if h != Float64(exact)
    println("REPRODUCED mathfuncs-hypot-correctly-rounded")
end
