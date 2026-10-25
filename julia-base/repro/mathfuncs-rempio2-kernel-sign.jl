x = -3.0e300
k, r = Base.Math.rem_pio2_kernel(x)
println("rem_pio2_kernel(", x, ") = (", k, ", ", r, ")")
y = 1.0e10
k2, _ = Base.Math.rem_pio2_kernel(y)
println("rem_pio2_kernel(", y, ")[1] = ", k2, "; round(y/(pi/2)) = ", round(Int, big(y) / (big(pi) / 2)))
if !(k < 0)
    println("REPRODUCED mathfuncs-rempio2-kernel-sign")
end
