# == for StepRangeLen{T,T} (range.jl:1171) compares first, step and last only; with step 0 two
# ranges of different lengths compare equal although their elements differ.
r = StepRangeLen(1, 0, 2)
s = StepRangeLen(1, 0, 3)
println(which(==, Tuple{typeof(r), typeof(s)}))
println("collect(r) = ", collect(r), ", collect(s) = ", collect(s), ", r == s: ", r == s)
if (r == s) != (collect(r) == collect(s))
    println("REPRODUCED range-srl-eq-length")
else
    error("range-srl-eq-length did not reproduce")
end
