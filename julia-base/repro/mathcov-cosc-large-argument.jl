# cosc(x) = cos(pi*x)/x - sin(pi*x)/(pi*x^2). For |x| >= maxintfloat every float is an
# even integer, so cos(pi*x) = 1, sin(pi*x) = 0 and cosc(x) == 1/x exactly.
# The generic branch divides by pi*x*x, which overflows: the result is 0.0 once
# pi*x^2 > floatmax and NaN once pi*x > floatmax.
xs = (1.0e154, 1.0e200, floatmax(Float64), 1.0f19, floatmax(Float32))
bad = false
for x in xs
    r = cosc(x)
    expected = inv(x)          # exact value 1/x rounded once
    println(typeof(x), " cosc(", x, ") = ", r, "   expected ", expected)
    if !(isfinite(r) && abs(r - expected) <= 2eps(expected))
        global bad = true
    end
end
bad && println("REPRODUCED mathcov-cosc-large-argument")
