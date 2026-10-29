short = isdisjoint([0.0], fill(-0.0, 69))
long = isdisjoint([0.0], fill(-0.0, 70))
println("isdisjoint([0.0], fill(-0.0, 69)) = ", short)
println("isdisjoint([0.0], fill(-0.0, 70)) = ", long)
if short != long
    println("REPRODUCED bitsetscov-abstractset-disjoint-filter")
else
    error("Disjointness did not change at the threshold")
end
