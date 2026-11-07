# Constructible scalar inputs; only public Julia functions are called.
function reproduces()
    x = UInt8(1)
    y = Int8(-2)
    f = fld(x, y)
    f === UInt8(255) && fld(BigInt(x), BigInt(y)) == -1 && BigInt(f) != fld(BigInt(x), BigInt(y))
end
matched = try
    reproduces()
catch
    false
end
println(matched ? "REPRODUCED div-bitinteger-directed-wrapper-correct-v2" : "NOT_REPRODUCED div-bitinteger-directed-wrapper-correct-v2")
