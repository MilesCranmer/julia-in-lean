# getindex(r::StepRangeLen{T}, s::OrdinalRange{S}) (range.jl:1075) picks the offset of the result as
# 1 + round(L, (r.offset - first(s))/step(s)), computed in Float64. For an Int StepRangeLen whose
# offset is close to typemax(Int), typemax(Int) - 1 rounds to 2.0^63 in Float64 and round(Int, ...)
# throws InexactError, although r[1] and r[2] exist and 1:2 is in bounds.
r = StepRangeLen(0, 1, typemax(Int), typemax(Int))
println("r[1] = ", r[1], ", r[2] = ", r[2])
res = try
    r[1:2]
catch e
    e
end
println("r[1:2] = ", repr(res))
if res isa InexactError
    println("REPRODUCED range-srl-range-index-offset")
else
    error("range-srl-range-index-offset did not reproduce")
end
