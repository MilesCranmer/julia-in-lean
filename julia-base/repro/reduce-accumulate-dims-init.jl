a = accumulate(+, [1, 2]; dims=2, init=10)
b = accumulate(+, [1 2; 3 4]; dims=3, init=10)
s = sum([1 2; 3 4]; dims=3, init=10)
println(repr(a), " ", repr(b), " ", repr(s))
if a == [1, 2] && b == [1 2; 3 4]
    println("REPRODUCED reduce-accumulate-dims-init")
end
