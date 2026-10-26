# intersect of two Iterators.product objects with different numbers of factors
# broadcasts the shorter tuple of factors, so it returns 2-tuples although the
# two iterators share no element (one yields 1-tuples, the other 2-tuples).
a = Iterators.product(1:3)
b = Iterators.product(1:2, 1:2)
r = collect(intersect(a, b))
expected = intersect(collect(a), collect(b))
println("collect(intersect(product(1:3), product(1:2, 1:2))) = ", repr(r))
println("intersect(collect(a), collect(b)) = ", repr(expected))
if !isempty(r) && isempty(expected)
    println("REPRODUCED iteratorscov-product-intersect-arity")
end
