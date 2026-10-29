# Base.div12(x, y) scales the normalized quotient and residual with ldexp after
# canonicalize2, which double-rounds subnormal quotients and returns (Inf, -Inf)
# on overflow when rl < 0, so hi + lo != x / y.
x = reinterpret(Float64, 0x0030000000000000) # 2.0^-1020
y = 6.0
hi, lo = Base.div12(x, y)
q = x / y
println("div12(2.0^-1020, 6.0) = ", (hi, lo), ", hi + lo = ", hi + lo, ", x / y = ", q)
hi_ovf, lo_ovf = Base.div12(ldexp(1.0, 600), ldexp(5.0, -600))
println("div12(2.0^600, 5.0 * 2.0^-600) = ", (hi_ovf, lo_ovf), ", hi + lo = ", hi_ovf + lo_ovf)
if (hi + lo != q) && isnan(hi_ovf + lo_ovf)
    println("REPRODUCED twiceprecision-div12-rounded")
end
