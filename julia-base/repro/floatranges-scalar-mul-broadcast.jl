# 3.0 * r and 3.0 .* r give different elements for the same float range.
r = 0.0:0.1:0.3
println("collect(3.0 * r)  = ", collect(3.0 * r))
println("collect(3.0 .* r) = ", collect(3.0 .* r))
println("collect(r .* 3.0) = ", collect(r .* 3.0))
(3.0 * r)[4] != (3.0 .* r)[4] && println("REPRODUCED floatranges-scalar-mul-broadcast")
