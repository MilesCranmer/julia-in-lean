x = NaN
y = 1.0
m = min(x, y)
ref = isless(y, x) ? y : x
println("min(NaN, 1.0) = ", m, "; min with respect to isless = ", ref)
println("max(NaN, 1.0) = ", max(x, y), "; isless(1.0, NaN) = ", isless(y, x))
if !isequal(m, ref)
    println("REPRODUCED mathfuncs-min-isless-nan")
end
