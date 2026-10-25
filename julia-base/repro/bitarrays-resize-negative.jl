res(f) = try
    f()
catch e
    typeof(e)
end
b = res(() -> resize!(BitVector(), -1))
v = res(() -> resize!(Bool[], -1))
println(b, " | ", v)
if b === BoundsError && v === ArgumentError
    println("REPRODUCED bitarrays-resize-negative")
end
