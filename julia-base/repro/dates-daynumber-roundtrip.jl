using Dates

d = Date(Int64(252527349277666), 1, 1)
parts = yearmonthday(d)
rebuilt = Date(parts...)
parsed = Date(string(d))
println("input day value = ", Dates.value(d))
println("yearmonthday = ", parts)
println("rebuilt day value = ", Dates.value(rebuilt))
println("Date(yearmonthday(d)...) == d = ", rebuilt == d)
println("Date(string(d)) == d = ", parsed == d)
rebuilt != d && parsed != d && println("REPRODUCED dates-daynumber-roundtrip")
