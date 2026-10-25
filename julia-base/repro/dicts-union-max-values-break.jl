# union!(s, itr) stops reading itr once length(s) == max_values(eltype(s)),
# so elements after that point are never converted and invalid ones pass.
a = try
    Set{Bool}([1, 0, 2])
catch e
    e
end
b = try
    Set{Bool}([1, 2, 0])
catch e
    e
end
c = try
    s = Set{Bool}()
    for x in [1, 0, 2]
        push!(s, x)
    end
    s
catch e
    e
end
println("Set{Bool}([1, 0, 2]) = ", a)
println("Set{Bool}([1, 2, 0]) = ", b)
println("push! of 1, 0, 2 into Set{Bool}() = ", c)
if a isa Set && b isa InexactError && c isa InexactError
    println("REPRODUCED dicts-union-max-values-break")
end
