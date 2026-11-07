x = NaN
y = 1.0
m = min(x, y)
ref = isless(y, x) ? y : x
println("min(NaN, 1.0) = ", m, "; min with respect to isless = ", ref)
println("max(NaN, 1.0) = ", max(x, y), "; isless(1.0, NaN) = ", isless(y, x))
if !isequal(m, ref)
    println("REPRODUCED mathfuncs-min-isless-nan")
end
setprecision(BigFloat, 64) do
    x, y = BigFloat(1), BigFloat(NaN)
    lo, hi = minmax(x, y)
    @assert isnan(lo) && isnan(hi)
    @assert isless(x, y) && isless(x, lo)
    @assert min(x, y) === lo
end
println("REPRODUCED mathfuncs-bigfloat-extrema-order")
