# A view indexed by an array of CartesianIndex is not detected as aliasing a view of the
# same parent that uses a scalar index, so `.=` reads elements it has already overwritten.
M = [1 2 3; 4 5 6; 7 8 9]
idx = [CartesianIndex(3, 3), CartesianIndex(2, 2), CartesianIndex(1, 1)]
expected = copy(M)
expected[1, :] .= M[idx]                     # right-hand side copied first
println("mightalias = ", Base.mightalias(view(M, 1, :), view(M, idx)))
@views M[1, :] .= M[idx]
println("@views M[1, :] .= M[idx] gives row ", M[1, :], ", expected ", expected[1, :])
if M != expected
    println("REPRODUCED broadcastviews-cartesian-alias")
end
