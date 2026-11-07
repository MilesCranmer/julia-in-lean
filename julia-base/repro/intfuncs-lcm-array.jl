result = lcm(Int8[typemin(Int8)])
@assert result == typemin(Int8)
println("REPRODUCED intfuncs-lcm-array")
