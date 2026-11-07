# Both arrays are distinct, fully initialized, and have four elements.
source = reshape([1, 2, 3, 4], 4, 1)
ordinary = zeros(Int, 2, 2)
copyto!(ordinary, source)
println("ordinary destination = ", ordinary)
parent = zeros(Int, 2, 2)
destination = PermutedDimsArray(parent, (2, 1))
outcome = try
    copyto!(destination, source)
catch error
    error
end
println("source size = ", size(source), "; destination size = ", size(destination))
println("source length = ", length(source), "; destination length = ", length(destination))
println("permuted result = ", outcome isa Exception ? nameof(typeof(outcome)) : collect(destination))
println("parent after copy = ", parent)

# Every source Cartesian coordinate also fits inside this destination.
small = reshape([1, 2, 3, 4], 2, 2)
ordinary_large = zeros(Int, 3, 3)
copyto!(ordinary_large, small)
permuted_large = PermutedDimsArray(zeros(Int, 3, 3), (2, 1))
copyto!(permuted_large, small)
println("ordinary larger destination = ", ordinary_large)
println("permuted larger destination = ", collect(permuted_large))

if ordinary == [1 3; 2 4] && outcome isa BoundsError && parent == zeros(Int, 2, 2) &&
        ordinary_large == [1 4 0; 2 0 0; 3 0 0] &&
        collect(permuted_large) == [1 3 0; 2 4 0; 0 0 0]
    println("REPRODUCED permuteddimsarray-copy-linear-length")
else
    error("Candidate did not reproduce")
end
