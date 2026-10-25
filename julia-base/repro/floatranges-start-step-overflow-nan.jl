# Elements of range(a; step, length) that overflow become NaN instead of Inf.
r = range(1.0; step=1.0e308, length=3)
println("collect(range(1.0; step=1.0e308, length=3)) = ", collect(r))
println("1.0 + 2 * 1.0e308 = ", 1.0 + 2 * 1.0e308)
isnan(r[3]) && println("REPRODUCED floatranges-start-step-overflow-nan")
