x = 1.67772173e7                     # 16777217.3, between the Float32 integers 16777216 and 16777218
a = round(Float32, x)
println("round(Float32, 1.67772173e7) = ", a, "   Float32(x) = ", Float32(x))
println("distance to 16777216 = ", x - 16777216, ", to 16777218 = ", 16777218 - x)
b = round(Float16, 2845.343f0)
println("round(Float16, 2845.343f0) = ", b, "   Float16(2845.343f0) = ", Float16(2845.343f0))
c = round(Float32, 16777217.0, RoundNearestTiesAway)
d = round(Float32, 16777217.0, RoundNearestTiesUp)
println("round(Float32, 16777217.0, RoundNearestTiesAway) = ", c)
println("round(Float32, 16777217.0, RoundNearestTiesUp) = ", d)
if a == 16777216 && Float32(x) == 16777218
    println("REPRODUCED floatfuncs-round-float-type-double")
end
