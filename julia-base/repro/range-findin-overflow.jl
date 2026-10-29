# findall(in(span), r) for integer ranges goes through Base._findin (range.jl:1296), which
# computes cld(first(span) - first(r), step(r)) in the element type; the difference wraps.
r = Int8(-100):Int8(-90)
span = Int8(50):Int8(100)
idx = findall(in(span), r)
want = [i for (i, x) in pairs(r) if x in span]
println("findall(in(span), r) = ", idx, ", expected ", want)
if collect(idx) != want
    println("REPRODUCED range-findin-overflow")
else
    error("range-findin-overflow did not reproduce")
end
