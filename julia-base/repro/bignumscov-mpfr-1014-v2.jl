# Constructible counterexample using only public Julia functions.
matched = try
    x = Float64(0.0)
    y = BigFloat(-0.0; precision=256)
    cmp(x, y) == 0 && isless(y, x)
catch
    false
end
println(matched ? "REPRODUCED bignumscov-mpfr-1014-v2" : "NOT_REPRODUCED bignumscov-mpfr-1014-v2")
