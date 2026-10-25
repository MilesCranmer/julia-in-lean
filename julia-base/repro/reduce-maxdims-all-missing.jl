A = [missing missing]
whole = maximum(vec(A))
r = try
    maximum(A; dims=1)
catch err
    err
end
println(typeof(A), " ", repr(whole), " ", r isa Exception ? typeof(r) : repr(r))
if whole === missing && r isa Exception
    println("REPRODUCED reduce-maxdims-all-missing")
end
