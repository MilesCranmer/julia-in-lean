# Constructible scalar inputs; only public Julia functions are called.
function reproduces()
    x = -nextfloat(0.0)
    y = 1.0
    r = rem(x, y, RoundDown)
    isfinite(x) && isfinite(y) && y > 0 && r == y && !(0 <= r < y)
end
matched = try
    reproduces()
catch
    false
end
println(matched ? "REPRODUCED float-rem-down-bound-v2" : "NOT_REPRODUCED float-rem-down-bound-v2")
