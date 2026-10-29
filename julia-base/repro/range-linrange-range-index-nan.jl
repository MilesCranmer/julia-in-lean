# getindex(r::LinRange{T}, s::OrdinalRange{S}) (range.jl:1110) builds r[c:d] as
# LinRange{T}(r[c], r[d], length(s)). For a one-element index c:c the LinRange constructor
# (range.jl:597) requires start == stop, which fails when r[c] is NaN, so r[c:c] throws ArgumentError
# although r[c] itself is NaN and c:c is in bounds.
r = LinRange(-Inf, Inf, 3)
println("r[2] = ", r[2])
res = try
    r[2:2]
catch e
    e
end
println("r[2:2] = ", repr(res))
if isnan(r[2]) && res isa ArgumentError
    println("REPRODUCED range-linrange-range-index-nan")
else
    error("range-linrange-range-index-nan did not reproduce")
end
