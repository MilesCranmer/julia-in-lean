a = "\xe2\xc0"
b = "\xe2\x82"
x = cmp(a, b)
y = invoke(cmp, Tuple{AbstractString, AbstractString}, a, b)
println("cmp(a, b) = ", x, ", generic AbstractString cmp = ", y)
println("collect(a) = ", repr(collect(a)), ", collect(b) = ", repr(collect(b)))
println("isless(collect(a), collect(b)) = ", isless(collect(a), collect(b)))
x == 1 && y == -1 && println("REPRODUCED strings-cmp-malformed")
