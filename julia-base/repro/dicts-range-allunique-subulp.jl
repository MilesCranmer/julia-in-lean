# allunique/allequal/unique of a range decide from step(r) != 0, but a float range
# whose step is below one ulp of its elements repeats values.
r = StepRangeLen(1.0, 1e-17, 3)
c = collect(r)
println("collect(StepRangeLen(1.0, 1e-17, 3)) = ", c)
println("allunique(r) = ", allunique(r), ", allunique(collect(r)) = ", allunique(c))
println("allequal(r) = ", allequal(r), ", allequal(collect(r)) = ", allequal(c))
println("length(unique(r)) = ", length(unique(r)), ", length(unique(collect(r))) = ", length(unique(c)))
l = LinRange(1.0, nextfloat(1.0), 5)
println("collect(LinRange(1.0, nextfloat(1.0), 5)) = ", collect(l))
println("allunique(l) = ", allunique(l), ", allunique(collect(l)) = ", allunique(collect(l)))
if allunique(r) && !allunique(c) && !allequal(r) && allequal(c) && allunique(l) && !allunique(collect(l))
    println("REPRODUCED dicts-range-allunique-subulp")
end
