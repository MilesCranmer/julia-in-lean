# Constructible scalar inputs; only public Julia functions are called.
function reproduces()
    x = UInt8(1)
    y = Int8(-2)
    p = fldmod(x, y)
    s = (fld(x, y), mod(x, y))
    p === (UInt8(255), UInt8(255)) && s === (UInt8(255), Int8(-1)) && p !== s
end
matched = try
    reproduces()
catch
    false
end
println(matched ? "REPRODUCED intarith-division-fldmod-consistency-v2" : "NOT_REPRODUCED intarith-division-fldmod-consistency-v2")
