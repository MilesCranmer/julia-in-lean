# searchsorted* on a float range computes (x - first(a)) / step(a), which overflows
# to Inf for ranges spanning more than floatmax, and round(Integer, Inf) throws.
r = range(-1e308, 1e308, length=3)   # [-1.0e308, 0.0, 1.0e308]
x = 9e307
want = searchsortedlast(collect(r), x)    # 2
got = try
    searchsortedlast(r, x)
catch e
    e
end
println(want, " ", got isa Exception ? typeof(got) : got)
if got != want
    println("REPRODUCED sorttuplescov-float-range-search-overflow")
end
