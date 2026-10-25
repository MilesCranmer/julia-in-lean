using Dates

y = Int64(300_000_000)
validation = Dates.validargs(DateTime, y, Int64(1), Int64(1), Int64(0), Int64(0), Int64(0), Int64(0))
dt = DateTime(y, 1, 1)
println("requested year = ", y)
println("validargs = ", validation)
println("constructed = ", dt)
println("year = ", year(dt))
validation === nothing && year(dt) != y && println("REPRODUCED dates-constructor-overflow")
