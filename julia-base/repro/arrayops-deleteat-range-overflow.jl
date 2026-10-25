a = [1, 2, 3]
err = try
    deleteat!(a, 1:typemax(Int))
    nothing
catch e
    e
end
println(repr(err))
println(a)
# expected: BoundsError, as for deleteat!(a, 1:4)
println(repr(try deleteat!([1, 2, 3], 1:4); nothing catch e; e end))
if err isa ArgumentError && occursin("_deletebeg!", err.msg)
    println("REPRODUCED arrayops-deleteat-range-overflow")
end
