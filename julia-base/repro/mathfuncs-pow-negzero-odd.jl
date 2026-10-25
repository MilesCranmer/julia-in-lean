y = 24577.0
a = (-0.0)^y
b = (-0.0)^(-y)
println("(-0.0)^24577.0 = ", repr(a), "   (-0.0)^24577 = ", repr((-0.0)^24577))
println("(-0.0)^-24577.0 = ", repr(b), "   (-0.0)^-24577 = ", repr((-0.0)^-24577))
println("(-0.0)^3.0 = ", repr((-0.0)^3.0), "   (-0.0)^-3.0 = ", repr((-0.0)^-3.0))
if !signbit(a) || !signbit(b)
    println("REPRODUCED mathfuncs-pow-negzero-odd")
end
