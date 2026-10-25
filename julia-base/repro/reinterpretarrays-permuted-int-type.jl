# PermutedDimsArray(A, perm) rejects permutations given as non-Int integers, which permutedims(A, perm) accepts
A = reshape(collect(1:6), 2, 3)
res(f) = try f() catch e; e end
for p in ((Int32(2), Int32(1)), UInt8[2, 1], (UInt(2), UInt(1)))
    println(repr(p), ": permutedims -> size ", size(permutedims(A, p)), "; PermutedDimsArray -> ", res(() -> size(PermutedDimsArray(A, p))))
end
r = res(() -> PermutedDimsArray(A, Int32[2, 1]))
if size(permutedims(A, Int32[2, 1])) == (3, 2) && r isa ErrorException
    println("REPRODUCED reinterpretarrays-permuted-int-type")
end
