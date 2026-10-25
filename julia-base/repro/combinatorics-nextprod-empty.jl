err = try
    nextprod((), 1)
    nothing
catch caught
    caught
end

println("nextprod((), 1): ", nameof(typeof(err)))
println("empty product:    1")

if err isa BoundsError
    println("REPRODUCED combinatorics-nextprod-empty")
end
