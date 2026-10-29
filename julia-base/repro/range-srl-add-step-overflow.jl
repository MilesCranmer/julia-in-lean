# +(r1::StepRangeLen{T,S}, r2::StepRangeLen{T,S}) (range.jl:1527) builds
# StepRangeLen(first(r1)+first(r2), step(r1)+step(r2), len); the step sum wraps in T, so an element
# of the sum cannot be read although every elementwise sum r1[i] + r2[i] is representable.
r = StepRangeLen(Int8(-60), Int8(100), 2)
want = collect(r) .+ collect(r)
got = try
    collect(r + r)
catch e
    e
end
println("collect(r) = ", collect(r), ", collect(r) .+ collect(r) = ", want, ", collect(r + r) = ", got)
if got != want
    println("REPRODUCED range-srl-add-step-overflow")
else
    error("range-srl-add-step-overflow did not reproduce")
end
