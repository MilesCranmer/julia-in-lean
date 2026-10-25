# BigFloat(q::Rational, r; precision) must round q once in direction r. It rounds the
# denominator first and then the quotient, so 1//5 at precision 2 comes out wrong in
# every mode. The representable neighbours of 0.2 at precision 2 are 0.1875 and 0.25.
q = 1 // 5
n = BigFloat(q; precision=2)
d = BigFloat(q, RoundDown; precision=2)
z = BigFloat(q, RoundToZero; precision=2)
println("BigFloat(1//5; precision=2)              = ", n, "  (nearest is 0.1875)")
println("BigFloat(1//5, RoundDown; precision=2)   = ", d, "  (largest <= 0.2 is 0.1875)")
println("BigFloat(1//5, RoundToZero; precision=2) = ", z)
println("BigFloat(\"0.2\"; precision=2)             = ", BigFloat("0.2"; precision=2))
println("abs(0.25 - 1//5) > abs(0.1875 - 1//5): ", abs(Rational{BigInt}(n) - q) > abs(3 // 16 - q))
if n == 0.25 && d == 0.125
    println("REPRODUCED bignums-bigfloat-rational-rounding")
end
