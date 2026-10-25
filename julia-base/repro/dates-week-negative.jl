using Dates

d = Date(0, 12, 31)
thursday = d + Day(4 - dayofweek(d))
expected = div(dayofyear(thursday) - 1, 7) + 1
println("date = ", d)
println("week = ", week(d))
println("Thursday rule = ", expected)
println("weekday = ", dayofweek(d))
week(d) != expected && println("REPRODUCED dates-week-negative")
