a, b = 0.7, 3.6999999999999997
r = UnitRange(a, b)
println("UnitRange(", a, ", ", b, ") = ", collect(r))
println("last(r) = ", last(r), " > stop: ", last(r) > b)
last(r) > b && println("REPRODUCED rangescov-unitrange-float-last")
