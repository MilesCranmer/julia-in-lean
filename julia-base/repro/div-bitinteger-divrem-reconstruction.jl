# Constructible scalar inputs; only public Julia functions are called.
function reproduces()
    x = UInt8(1)
    y = UInt8(2)
    q, r = divrem(x, y, RoundUp)
    q === UInt8(1) && r === UInt8(255) && BigInt(r) != BigInt(x) - BigInt(q) * BigInt(y)
end
matched = try
    reproduces()
catch
    false
end
println(matched ? "REPRODUCED div-bitinteger-divrem-reconstruction" : "NOT_REPRODUCED div-bitinteger-divrem-reconstruction")
