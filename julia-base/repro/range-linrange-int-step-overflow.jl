# The inner constructor LinRange{T,L}(start, stop, len) (range.jl:597-611) rejects an integer
# LinRange whose step (stop - start)/(len - 1) is not an integer by testing mod(stop - start, len - 1).
# For Int endpoints stop - start wraps around, so LinRange{Int}(typemin(Int), typemax(Int), 4) throws
# "LinRange{<:Integer} cannot have non-integer step" although the step (2^64 - 1)/3 is the integer
# 6148914691236517205, which fits in Int. _linspace(Int, ...) (range.jl:632) calls this constructor.
a, b, n = typemin(Int), typemax(Int), 4
step = (big(b) - big(a)) / (n - 1)
println("exact step = ", step, ", isinteger = ", isinteger(step), ", fits Int = ", typemin(Int) <= step <= typemax(Int))
res = try
    LinRange{Int}(a, b, n)
catch e
    e
end
res2 = try
    Base._linspace(Int, a, b, n)
catch e
    e
end
println("LinRange{Int}(typemin(Int), typemax(Int), 4) = ", repr(res))
println("Base._linspace(Int, typemin(Int), typemax(Int), 4) = ", repr(res2))
if isinteger(step) && res isa ArgumentError && res2 isa ArgumentError
    println("REPRODUCED range-linrange-int-step-overflow")
else
    error("range-linrange-int-step-overflow did not reproduce")
end
