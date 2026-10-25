# last(product(...)) returns a tuple for an empty product of ranges
p = Iterators.product(1:2, 1:0)
r = try last(p) catch e; e end
println("isempty(product(1:2, 1:0)) = ", isempty(p), ", last = ", repr(r))
println("last(product([1,2], Int[])) throws: ", try last(Iterators.product([1, 2], Int[])); false catch e; true end)
isempty(p) && r == (2, 0) && println("REPRODUCED iterators-product-last-empty")
