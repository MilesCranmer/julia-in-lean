# reverse(LinRange) does not reproduce the elements in reverse order.
r = LinRange(0.0, 1.0, 4)
println("collect(r)          = ", collect(r))
println("collect(reverse(r)) = ", collect(reverse(r)))
println("reverse(collect(r)) = ", reverse(collect(r)))
collect(reverse(r)) != reverse(collect(r)) && println("REPRODUCED floatranges-linrange-reverse")
