# cmp(1//0, 1//2) must be 1 (positive infinity is the largest rational). For
# Rational{BigInt}, cmp passes the unnormalized 1//0 to GMP's mpq_cmp, which requires
# a positive denominator, and the sign comes out wrong.
inf = big(1) // 0
half = big(1) // 2
println("cmp(big(1)//0, big(1)//2)  = ", cmp(inf, half), "   (Rational{Int}: ", cmp(1 // 0, 1 // 2), ")")
println("cmp(big(1)//2, big(1)//0)  = ", cmp(half, inf), "   (Rational{Int}: ", cmp(1 // 2, 1 // 0), ")")
println("cmp(big(-1)//0, big(-3)//1) = ", cmp(-inf, big(-3) // 1), "   (Rational{Int}: ", cmp(-1 // 0, -3 // 1), ")")
println("big(1)//0 > big(1)//2: ", inf > half, ", isless(big(1)//2, big(1)//0): ", isless(half, inf))
if cmp(inf, half) == -1 && cmp(1 // 0, 1 // 2) == 1 && inf > half
    println("REPRODUCED bignums-rational-cmp-infinite")
end
