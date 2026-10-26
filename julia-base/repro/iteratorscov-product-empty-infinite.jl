# IteratorSize(product(1:0, countfrom())) is IsInfinite although the product is
# empty, so zip with a finite iterator claims length 3 and collect returns three
# uninitialised elements.
p = Iterators.product(1:0, Iterators.countfrom())
println("IteratorSize = ", Base.IteratorSize(p), ", isempty = ", isempty(p))
z = zip(p, 1:3)
n = 0
for _ in z
    global n += 1
end
println("zip yields ", n, " elements, length(z) = ", length(z))
c = collect(z)
println("length(collect(z)) = ", length(c))
if Base.IteratorSize(p) isa Base.IsInfinite && isempty(p) && length(c) != n
    println("REPRODUCED iteratorscov-product-empty-infinite")
end
