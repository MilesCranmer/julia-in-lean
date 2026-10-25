z = complex(2.0^1000, 0.0)
w = complex(3 * nextfloat(0.0), 2.0)
q = z / w
setprecision(BigFloat, 4000) do
    a, b, c, d = big(real(z)), big(imag(z)), big(real(w)), big(imag(w))
    exact_re = (a * c + b * d) / (c^2 + d^2)
    println("z / w            = ", q)
    println("exact real part  = ", Float64(exact_re))
    println("relative error   = ", Float64(abs(real(q) - exact_re) / abs(exact_re)))
    if abs(real(q) - exact_re) > abs(exact_re) / 2^20
        println("REPRODUCED complex-div-subnormal-ratio")
    end
end
