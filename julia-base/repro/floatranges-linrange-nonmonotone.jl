# An increasing LinRange decreases between two consecutive elements.
r = LinRange(62.1443, 62.14430000000095, 283)
println("r[8] = ", repr(r[8]))
println("r[9] = ", repr(r[9]))
println("issorted(r) = ", issorted(collect(r)))
r[9] < r[8] && println("REPRODUCED floatranges-linrange-nonmonotone")
