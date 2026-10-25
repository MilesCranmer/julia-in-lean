# Ryu.writeshortest(x, plus, space, hash, precision) uses fixed notation when the
# decimal point position pt satisfies -4 < pt <= precision and x is a multiple of
# the power of ten its shortest digits omit.
W(x) = Base.Ryu.writeshortest(x, false, false, true, 30)
println("1e18 -> ", W(1e18))
println("1e19 -> ", W(1e19))
println("1e20 -> ", W(1e20))
!occursin('e', W(1e18)) && occursin('e', W(1e19)) && occursin('e', W(1e20)) &&
    println("REPRODUCED parseprint-ryu-precision-pow10-overflow")
