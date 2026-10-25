x = Int8(65)
r = nextpow(2, x)
@assert r == Int8(-128) && r < x
@assert nextpow(2, typemax(UInt8)) == UInt8(0)
println("signed result = ", repr(r))
println("unsigned result = ", repr(nextpow(2, typemax(UInt8))))
println("REPRODUCED intarith-powers-nextpow-overflow")
