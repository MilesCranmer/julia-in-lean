# == on CartesianIndices compares the component ranges, so two empty CartesianIndices of
# the same size are unequal although they are equal as arrays (and isequal, hash agree).
a = CartesianIndices((1:0, 1:2))
b = CartesianIndices((1:0, 3:4))
println("size: ", size(a), " ", size(b))
println("a == b: ", a == b, "   collect(a) == collect(b): ", collect(a) == collect(b),
        "   isequal(a, b): ", isequal(a, b), "   hash equal: ", hash(a) == hash(b))
println("ranges: (1:0) == (3:2) is ", (1:0) == (3:2))
if !(a == b) && collect(a) == collect(b) && isequal(a, b)
    println("REPRODUCED multidim-cartesianindices-empty-eq")
end
