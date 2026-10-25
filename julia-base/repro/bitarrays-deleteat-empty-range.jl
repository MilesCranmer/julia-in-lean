res(f) = try
    f()
catch e
    typeof(e)
end
b1 = res(() -> deleteat!(BitVector([false, true, false]), 0:-1))
v1 = res(() -> deleteat!([false, true, false], 0:-1))
b2 = res(() -> splice!(BitVector([false, true, false]), 5:4))
v2 = res(() -> splice!([false, true, false], 5:4))
println(b1, " | ", v1)
println(b2, " | ", v2)
if b1 === BoundsError && v1 == [false, true, false] && b2 === BoundsError && v2 == Bool[]
    println("REPRODUCED bitarrays-deleteat-empty-range")
end
