# isdisjoint(a, b) for two integer ranges with equal |step| compares
# mod(minimum(a), step(a)) with mod(minimum(b), step(a))
# (base/abstractset.jl:612-614). A StepRangeLen{Int} may have step 0, and then
# mod(x, 0) throws DivideError instead of returning false.
a = StepRangeLen(1, 0, 3)   # [1, 1, 1]
b = StepRangeLen(1, 0, 2)   # [1, 1]
println("collect(a) = ", collect(a), ", collect(b) = ", collect(b))
println("isdisjoint(collect(a), collect(b)) = ", isdisjoint(collect(a), collect(b)))
r = try
    isdisjoint(a, b)
catch e
    e
end
println("isdisjoint(a, b) = ", r)
if r isa DivideError && !isdisjoint(collect(a), collect(b))
    println("REPRODUCED bitsetscov-isdisjoint-zero-step")
end
