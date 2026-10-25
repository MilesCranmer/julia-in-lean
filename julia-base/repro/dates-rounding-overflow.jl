using Dates

d = Date(-1)
p = Day(typemax(Int64))
f, c = floor(d, p), ceil(d, p)
println("input day value = ", Dates.value(d))
println("precision = ", Dates.value(p))
println("floor day value = ", Dates.value(f))
println("ceil day value = ", Dates.value(c))
println("floor <= input <= ceil = ", f <= d <= c)
f > d && println("REPRODUCED dates-rounding-overflow")
