x = typemin(Int64)
r = copysign(x, 1)
println("copysign(typemin(Int64), 1) = ", r)
println("copysign(typemin(Int8), Int8(1)) = ", copysign(typemin(Int8), Int8(1)))
println("copysign(typemin(Int64), 1.0) = ", copysign(x, 1.0))
if signbit(r)
    println("REPRODUCED mathfuncs-copysign-typemin")
end
