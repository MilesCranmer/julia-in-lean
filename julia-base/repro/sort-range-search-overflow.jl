r = Int8(-100):Int8(100)
x = Int8(50)
v = collect(r)
got = (searchsortedfirst(r, x), searchsortedlast(r, x), searchsorted(r, x))
want = (searchsortedfirst(v, x), searchsortedlast(v, x), searchsorted(v, x))
println("Int8 range:  ", got, "  collect: ", want)

r64 = typemin(Int):2:2^62
y = 2^62 - 1
got64 = searchsortedlast(r64, y)
want64 = fld(big(y) - first(r64), step(r64)) + 1
println("Int64 range: ", got64, "  expected: ", want64)

if got != want && got64 != want64
    println("REPRODUCED sort-range-search-overflow")
end
