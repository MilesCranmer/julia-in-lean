# isdisjoint(a, b) with two vectors uses `in(b)` (==) while length(b) < 70 and
# `in(Set(b))` (isequal) otherwise (base/abstractset.jl:576-578), so the answer
# flips with the length of b for -0.0/0.0 and NaN.
r1 = isdisjoint([0.0], fill(-0.0, 69))
r2 = isdisjoint([0.0], fill(-0.0, 70))
r3 = isdisjoint([NaN], fill(NaN, 69))
r4 = isdisjoint([NaN], fill(NaN, 70))
println("isdisjoint([0.0], fill(-0.0, 69)) = ", r1)
println("isdisjoint([0.0], fill(-0.0, 70)) = ", r2)
println("isdisjoint([NaN], fill(NaN, 69)) = ", r3)
println("isdisjoint([NaN], fill(NaN, 70)) = ", r4)
if r1 != r2 && r3 != r4
    println("REPRODUCED bitsetscov-isdisjoint-threshold")
end
