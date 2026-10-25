x = -nextfloat(0.0f0)
m = mod2pi(x)
d = rem2pi(x, RoundDown)
u = rem2pi(-x, RoundUp)
twopi = 2 * big(pi)
println("mod2pi(", repr(x), ") = ", repr(m), "  >= 2pi: ", m >= twopi)
println("rem2pi(", repr(x), ", RoundDown) = ", repr(d), "  > 2pi: ", d > twopi)
println("rem2pi(", repr(-x), ", RoundUp) = ", repr(u), "  < -2pi: ", u < -twopi)
if m >= twopi || d > twopi || u < -twopi
    println("REPRODUCED mathfuncs-rem2pi-float32-range")
end
