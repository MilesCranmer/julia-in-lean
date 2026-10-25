i = typemin(Int)
r = 1:3
y = mod(i, r)
expected = Int(mod(big(i) - first(r), big(length(r))) + first(r))
println("mod(typemin(Int), 1:3) = ", y)
println("expected = ", expected)
y == 2 && expected == 1 && println("REPRODUCED ranges-mod-congruence")
