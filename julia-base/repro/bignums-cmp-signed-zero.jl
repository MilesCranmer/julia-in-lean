# cmp must follow the isless total order. For BigFloat against Float64 or Integer, the
# specialized cmp methods use mpfr_cmp, so cmp(big(-0.0), 0.0) == 0 although
# isless(big(-0.0), 0.0) is true and cmp(-0.0, 0.0) == -1.
x = big(-0.0)
println("isless(big(-0.0), 0.0) = ", isless(x, 0.0), ", isless(big(-0.0), 0) = ", isless(x, 0))
println("cmp(big(-0.0), 0.0) = ", cmp(x, 0.0), ", cmp(0.0, big(-0.0)) = ", cmp(0.0, x))
println("cmp(big(-0.0), 0) = ", cmp(x, 0), ", cmp(big(-0.0), big(0)) = ", cmp(x, big(0)))
println("cmp(-0.0, 0.0) = ", cmp(-0.0, 0.0), ", cmp(-0.0, 0) = ", cmp(-0.0, 0), ", cmp(big(-0.0), big(0.0)) = ", cmp(x, big(0.0)))
if isless(x, 0.0) && cmp(x, 0.0) == 0 && cmp(x, 0) == 0 && cmp(-0.0, 0.0) == -1
    println("REPRODUCED bignums-cmp-signed-zero")
end
