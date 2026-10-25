# A LinRange with an infinite endpoint indexes its first element as NaN.
r = LinRange(0.0, Inf, 3)
println("first(r) = ", first(r), "   r[1] = ", r[1])
println("collect(r) = ", collect(r))
isnan(r[1]) && first(r) == 0.0 && println("REPRODUCED floatranges-linrange-infinite-endpoint")
