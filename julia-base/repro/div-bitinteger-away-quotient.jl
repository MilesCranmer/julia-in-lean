# Constructible scalar inputs; only public Julia functions are called.
function reproduces()
    x = UInt8(1)
    y = Int8(-2)
    q = div(x, y, RoundFromZero)
    q === UInt8(255) && div(BigInt(x), BigInt(y), RoundFromZero) == -1 && BigInt(q) != div(BigInt(x), BigInt(y), RoundFromZero)
end
matched = try
    reproduces()
catch
    false
end
println(matched ? "REPRODUCED div-bitinteger-away-quotient" : "NOT_REPRODUCED div-bitinteger-away-quotient")
