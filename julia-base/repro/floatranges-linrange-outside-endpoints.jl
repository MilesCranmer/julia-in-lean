# A LinRange with equal endpoints has elements different from them.
r = LinRange(0.1, 0.1, 6)
println("collect(LinRange(0.1, 0.1, 6)) = ", collect(r))
println("LinRange(830.6, 830.6000000000012, 180)[2] = ", repr(LinRange(830.6, 830.6000000000012, 180)[2]))
r[2] > 0.1 && println("REPRODUCED floatranges-linrange-outside-endpoints")
