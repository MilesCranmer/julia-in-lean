x = UInt8(1) // UInt8(0)
y = UInt8(1) // UInt8(1)
@assert isinf(x) && x > 0 && isfinite(y)
@assert x - 1 == x
observed = try
    x - y
catch err
    err
end
@assert observed isa OverflowError
println("REPRODUCED intarith-rational-infinity-sub")
