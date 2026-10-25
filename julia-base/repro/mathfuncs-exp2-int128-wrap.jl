x = -(Int128(2)^64) - 1069
r = exp2(x)
println("exp2(", x, ") = ", repr(r), "   exp2(Float64(x)) = ", repr(exp2(Float64(x))))
y = -(Int128(2)^70) - 1022
println("exp2(", y, ") = ", repr(exp2(y)))
if r != 0.0 || exp2(y) != 0.0
    println("REPRODUCED mathfuncs-exp2-int128-wrap")
end
