vs = [Int[], Int[]]
c = sum(collect(Iterators.flatten(vs)))
r = try
    sum(Iterators.flatten(vs))
catch err
    err
end
println(eltype(Iterators.flatten(vs)), " ", repr(c), " ", r isa Exception ? typeof(r) : repr(r))
if c === 0 && r isa ArgumentError
    println("REPRODUCED reduce-flatten-sum-empty")
end
