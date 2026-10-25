# length(product(...)) throws OverflowError for an empty product whose earlier factors overflow
p = Iterators.product(1:2^32, 1:2^32, 1:0)
l = try length(p) catch e; e end
println("length(product(1:2^32, 1:2^32, 1:0)) = ", l isa Exception ? sprint(showerror, l) : repr(l))
println("isempty = ", isempty(p), ", size = ", size(p), ", length(collect) = ", length(collect(p)))
println("length(product(1:0, 1:2^32, 1:2^32)) = ", length(Iterators.product(1:0, 1:2^32, 1:2^32)))
l isa OverflowError && isempty(p) && println("REPRODUCED iterators-product-length-zero")
