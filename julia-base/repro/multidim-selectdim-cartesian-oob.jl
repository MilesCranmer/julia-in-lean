# selectdim(A, d, I::CartesianIndex) with length(I) > 1 keeps a Slice for each original
# dimension, so the view extends past the last dimension of A and reads (and writes)
# memory outside A without any bounds error.
A = reshape(collect(1:24), 2, 3, 4)
V = selectdim(A, 2, CartesianIndex(1, 1))
W = view(A, :, CartesianIndex(1, 1), :)        # the documented equivalent
println("size(selectdim(A, 2, CartesianIndex(1, 1))) = ", size(V), ", size(view(A, :, CartesianIndex(1, 1), :)) = ", size(W))
println("A[1, 1, 1, 2] in bounds? ", checkbounds(Bool, A, 1, 1, 1, 2))
B = [1 2; 3 4]
S = selectdim(B, 1, CartesianIndex(2, 2))
println("size(selectdim(B, 1, CartesianIndex(2, 2))) = ", size(S), " (B has ", length(B), " elements; S[2] is B[2, 2, 2])")
if size(V) == (2, 4) && size(W) == (2, 1) && !checkbounds(Bool, A, 1, 1, 1, 2) && size(S) == (2,)
    println("REPRODUCED multidim-selectdim-cartesian-oob")
end
