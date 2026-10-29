x, y = Int8(1), typemin(Int8)
q = div(x, y, RoundUp)
r = rem(x, y, RoundUp)
expected = big(x) - big(y) * big(q)
@assert r == Int8(-127)
@assert big(r) != expected
println("rem = ", r, ", exact x-y*q = ", expected)
println("REPRODUCED div-bitinteger-remainder-equation")
