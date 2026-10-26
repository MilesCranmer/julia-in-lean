# The legacy 6-argument sort!(v, lo, hi, alg, order, scratch::Vector) throws for
# QuickSort and PartialQuickSort, while the 5-argument form and the same call with
# scratch=nothing sort.
using Base.Order: Forward
a = sort!([5, 4, 3, 2, 1], 2, 4, QuickSort, Forward)
b = sort!([5, 4, 3, 2, 1], 2, 4, QuickSort, Forward, nothing)
c = try
    sort!([5, 4, 3, 2, 1], 2, 4, QuickSort, Forward, Int[])
catch e
    e
end
println(a, " ", b, " ", c isa Exception ? typeof(c) : c)
if c isa ArgumentError && a == [5, 2, 3, 4, 1]
    println("REPRODUCED sorttuplescov-legacy-sort-scratch")
end
