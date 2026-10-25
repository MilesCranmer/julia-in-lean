using Dates

a = Date(0) + Day(Int64(-92233720368548195))
b = a + Day(1)
r = a:Month(1):b
println("start day value = ", Dates.value(a))
println("requested stop day value = ", Dates.value(b))
println("length = ", length(r))
println("stored last day value = ", Dates.value(last(r)))
println("last indexed day value = ", Dates.value(r[end]))
println("last(r) == r[end] = ", last(r) == r[end])
println("last(r) in r = ", last(r) in r)
last(r) != r[end] && println("REPRODUCED dates-range-last-iteration")
