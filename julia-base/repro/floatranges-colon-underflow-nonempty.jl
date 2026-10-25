# a:s:b with a > b and a positive step is nonempty when (b - a)/s underflows to -0.0.
r = 1.0e-300:1.0e30:0.0
println("length(1.0e-300:1.0e30:0.0) = ", length(r))
println("collect(1.0e-300:1.0e30:0.0) = ", collect(r))
println("length(1.0e-300:1.0e10:0.0) = ", length(1.0e-300:1.0e10:0.0))
length(r) == 1 && first(r) > 0.0 && println("REPRODUCED floatranges-colon-underflow-nonempty")
