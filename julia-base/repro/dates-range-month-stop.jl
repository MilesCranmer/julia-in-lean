using Dates

a = Date(2019, 1, 31)
b = Date(2019, 3, 29)
r = a:Month(1):b
println("requested stop = ", b)
println("length = ", length(r))
println("last = ", last(r))
println("elements = ", join(string.(collect(r)), ", "))
println("overshooting element is in range = ", Date(2019, 3, 31) in r)
last(r) > b && length(r) == 3 && println("REPRODUCED dates-range-month-stop")
