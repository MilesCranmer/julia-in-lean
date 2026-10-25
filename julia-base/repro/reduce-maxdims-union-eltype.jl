A = Union{Int,Float64}[1, 2.5]
whole = maximum(A)
r = try
    maximum(A; dims=1)
catch err
    err
end
println(repr(whole), " ", r isa Exception ? typeof(r) : repr(r))
if whole === 2.5 && r isa InexactError
    println("REPRODUCED reduce-maxdims-union-eltype")
end
