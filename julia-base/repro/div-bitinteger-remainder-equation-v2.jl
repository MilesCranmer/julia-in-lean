# Constructible scalar inputs; only public Julia functions are called.
function reproduces()
    x = Int8(-127)
    y = Int8(-128)
    q = div(x, y, RoundUp)
    r = rem(x, y, RoundUp)
    q === Int8(1) && r === Int8(-127) && BigInt(r) != BigInt(x) - BigInt(y) * BigInt(q)
end
matched = try
    reproduces()
catch
    false
end
println(matched ? "REPRODUCED div-bitinteger-remainder-equation-v2" : "NOT_REPRODUCED div-bitinteger-remainder-equation-v2")
