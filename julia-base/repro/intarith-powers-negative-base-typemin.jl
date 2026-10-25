x = UInt8(1)
b = typemin(Int8)
@assert 0 < BigInt(x) < -BigInt(b)
@assert Base.ndigits0z(x, b) == 2
@assert ndigits(x, base=b) == 2
println("ndigits0z = ", Base.ndigits0z(x, b))
println("ndigits = ", ndigits(x, base=b))
println("REPRODUCED intarith-powers-negative-base-typemin")
