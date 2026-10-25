a = cumsum([1, 2, 3]; dims=0)
r = try
    accumulate(+, [1, 2, 3]; dims=0)
catch err
    err
end
m = try
    cumsum([1 2 3]; dims=0)
catch err
    err
end
println(repr(a), " ", r isa Exception ? typeof(r) : repr(r), " ", m isa Exception ? typeof(m) : repr(m))
if a == [1, 2, 3] && r isa ArgumentError
    println("REPRODUCED reduce-cumsum-dims-nonpositive")
end
