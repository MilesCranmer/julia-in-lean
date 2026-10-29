x, y = UInt8(1), UInt8(2)
q, r = divrem(x, y, RoundUp)
expected = big(x) - big(y) * big(q)
@assert (q, r) == (UInt8(1), UInt8(255))
@assert big(r) != expected
println("divrem = ", (q, r), ", exact x-y*q = ", expected)
println("REPRODUCED div-bitinteger-divrem-reconstruction")
