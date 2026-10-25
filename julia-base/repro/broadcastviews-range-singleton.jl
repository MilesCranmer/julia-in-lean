# Broadcasting two ranges, one of length 1, throws instead of expanding the singleton.
r = 1:3
s = 5:5
v = try r .+ s catch e; e end
w = collect(r) .+ collect(s)
println("(1:3) .+ (5:5) = ", v)
println("collect(1:3) .+ collect(5:5) = ", w)
if v isa DimensionMismatch
    println("REPRODUCED broadcastviews-range-singleton")
end
