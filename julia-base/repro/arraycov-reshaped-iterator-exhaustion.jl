A = reshape(1:2, 2, 1)
R = Base.ReshapedArrayIterator(A)
result = try
    collect(R)
catch err
    err
end

println("Iterator length: ", length(R))
println("Result type: ", typeof(result))
println("Expected: collection succeeds with two ReshapedIndex values")

if result isa MethodError && result.f === iterate && result.args == (nothing,)
    println("REPRODUCED arraycov-reshaped-iterator-exhaustion")
else
    println("NOT REPRODUCED arraycov-reshaped-iterator-exhaustion")
end
