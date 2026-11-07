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

let r = LinRange(-1.0e308, 1.0e308, 3), x = 9.0e307
    @assert collect(r) == [-1.0e308, 0.0, 1.0e308]
    @assert all(isfinite, r) && isfinite(x)
    @assert isinf(step(r)) && isinf(x - first(r))
    @assert isnan((x - first(r)) / step(r) + 1)
    for f in (searchsortedfirst, searchsortedlast, searchsorted)
        want = f(collect(r), x)
        got = try
            f(r, x)
        catch e
            e
        end
        println("LinRange ", f, " expected ", want, " got ", got isa Exception ? typeof(got) : got)
        @assert got isa InexactError
    end
    println("REPRODUCED exact-LinRange-all-searchsorted")
end
