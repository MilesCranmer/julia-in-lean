# step(LinRange) overflows for large finite endpoints, so `in` misses elements.
r = LinRange(-1.0e308, 1.0e308, 3)
println("collect(r) = ", collect(r))
println("step(r) = ", step(r))
println("r[2] = ", r[2], "   r[2] in r = ", r[2] in r)
isinf(step(r)) && !(r[2] in r) && println("REPRODUCED floatranges-linrange-step-overflow")
