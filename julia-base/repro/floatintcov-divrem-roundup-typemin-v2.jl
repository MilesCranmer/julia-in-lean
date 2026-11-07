# Constructible scalar inputs; only public Julia functions are called.
function reproduces()
    x = Int8(-127)
    y = Int8(-128)
    p = divrem(x, y, RoundUp)
    s = (div(x, y, RoundUp), rem(x, y, RoundUp))
    p === (Int8(1), Int8(1)) && s === (Int8(1), Int8(-127)) && p !== s
end
matched = try
    reproduces()
catch
    false
end
println(matched ? "REPRODUCED floatintcov-divrem-roundup-typemin-v2" : "NOT_REPRODUCED floatintcov-divrem-roundup-typemin-v2")
