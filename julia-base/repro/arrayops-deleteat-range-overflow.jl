a = [1, 2, 3]
err = try
    deleteat!(a, 1:typemax(Int))
    nothing
catch e
    e
end
println(repr(err))
println(a)
println("Original positive-start case now throws BoundsError: ", err isa BoundsError)

b = [1, 2, 3]
r = -1:typemax(Int)
surviving = try
    deleteat!(b, r)
    nothing
catch e
    e
end
println("length(-1:typemax(Int)) = ", length(r))
println(repr(surviving))
println(b)
if a == [1, 2, 3] && surviving isa ArgumentError && b == [1, 2, 3]
    println("REPRODUCED arrayops-deleteat-range-overflow")
else
    println("NOT REPRODUCED arrayops-deleteat-range-overflow")
end
