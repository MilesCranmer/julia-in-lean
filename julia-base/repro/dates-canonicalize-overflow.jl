using Dates

p = Dates.CompoundPeriod(Year(typemax(Int64)), Month(12))
q = canonicalize(p)
exactmonths(c) = sum((p isa Year ? Int128(12) * Dates.value(p) : Int128(Dates.value(p)) for p in Dates.periods(c)); init=Int128(0))
println("input = ", p)
println("canonicalized = ", q)
println("input exact months = ", exactmonths(p))
println("output exact months = ", exactmonths(q))
exactmonths(p) != exactmonths(q) && println("REPRODUCED dates-canonicalize-overflow")
