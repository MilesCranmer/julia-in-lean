# A normalized, constructible positive infinity with UInt8 components.
x = UInt8(1) // UInt8(0)
reproduced = try
    round(Rational{UInt8}, x, RoundNearest)
    false
catch err
    err isa OverflowError
end
println(reproduced ? "REPRODUCED intarith-round-rational-unsigned-infinity" : "NOT_REPRODUCED intarith-round-rational-unsigned-infinity")
