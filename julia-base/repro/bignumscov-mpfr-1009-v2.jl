# Constructible counterexample using only public Julia functions.
matched = try
    x = BigFloat(-0.0; precision=256)
    y = Float64(0.0)
    cmp(x, y) == 0 && isless(x, y)
catch
    false
end
println(matched ? "REPRODUCED bignumscov-mpfr-1009-v2" : "NOT_REPRODUCED bignumscov-mpfr-1009-v2")
