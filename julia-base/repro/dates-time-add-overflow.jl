using Dates

t = Time(1)
n = typemax(Int64)
actual = Dates.value(t + Nanosecond(n))
expected = mod(Int128(Dates.value(t)) + n, 86400000000000)
println("input nanoseconds = ", Dates.value(t))
println("added nanoseconds = ", n)
println("actual nanoseconds of day = ", actual)
println("exact modulo-day result = ", expected)
actual != expected && println("REPRODUCED dates-time-add-overflow")
